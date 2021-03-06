

(*   translate_expr_map : Past.expr -> Ast.expr 
     Translates parsed AST to internal AST : 
     1) drop file locations 
     2) drop types 
     3) remove let 
     ) replace "?" (What) with unary function call 

  Note : our front-end drops type information.  Is this really a good idea? 
  Could types be useful in later phases of the compiler? 

*) 

let translate_uop = function 
  | Past.NEG -> Ast.NEG 
  | Past.NOT -> Ast.NOT 

let translate_bop = function 
  | Past.ADD -> Ast.ADD 
  | Past.MUL -> Ast.MUL
  | Past.DIV -> Ast.DIV
  | Past.SUB -> Ast.SUB
  | Past.LT -> Ast.LT
  | Past.AND -> Ast.AND
  | Past.OR -> Ast.OR
  | Past.EQI -> Ast.EQI
  | Past.EQB -> Ast.EQB
  | Past.EQ  -> Errors.complain "internal error, translate found a EQ that should have been resolved to EQI or EQB"

(* take a function definition with multiple input parameters (the tuple) and returns an expression that has a single argument
   p (we use the same name as the function itself to avoid creating a reserved word) that is a series of pairs, equivalent to the
   original tuple - e.g. (x: int, y: int, z: int) becomes (p: int * (int * int)) so variable x is fst (p), y is fst(snd(p)) and z is snd(snd(p))
   
   The expression returned by this function has replaced references to original variable names from the tuple with the correct nested reference
   into the pair p.
   
   e.g. let rev (x : int, y : int) : int * int = (y, x) in e is translated to...
   
   let rev (p: int * int) : int * int = 
     let x = fst p in
	   let y = snd p in
	     (y, x)
	   end
	 end
	in 
	  e
	end
	
	or for a triple: let rev(x : int, y : int, z : int) = e1 in e2 becomes...
	
	let rev (p: int * (int * int)) : int * int = 
     let x = fst p in
	   let y = fst snd p in
	     let z = snd snd p
	      e1
	   end
	 end
	in 
	  e2
	end
	
	Note that Past -> Ast loses type information so this function doesn't deal with re-evaluating the type of p
*)
let rec translate_t_lambda = function(tuples, body_expr, p) -> match tuples with
    | [(x, _)]     -> Ast.App(Ast.Lambda(x, body_expr), p)
	| (x, _)::rest -> translate_t_lambda(rest, Ast.App(Ast.Lambda(x, body_expr), Ast.Fst(p)), Ast.Snd(p))

let rec translate_expr_map = function (e, map) -> match e with
    | Past.Unit _            -> Ast.Unit
    | Past.What _            -> Ast.UnaryOp(Ast.READ, Ast.Unit)
    | Past.Var(_, x)         -> map x
    | Past.Integer(_, n)     -> Ast.Integer n
    | Past.Boolean(_, b)     -> Ast.Boolean b
    | Past.UnaryOp(_, op, e) -> Ast.UnaryOp(translate_uop op, translate_expr_map(e, map))
    | Past.Op(_, e1, op, e2) -> Ast.Op(translate_expr_map(e1, map), translate_bop op, translate_expr_map(e2, map))
    | Past.If(_, e1, e2, e3) -> Ast.If(translate_expr_map(e1, map), translate_expr_map(e2, map), translate_expr_map(e3,map))
    | Past.Pair(_, e1, e2)   -> Ast.Pair(translate_expr_map(e1, map), translate_expr_map(e2, map))
    | Past.Fst(_, e)         -> Ast.Fst(translate_expr_map(e, map))
    | Past.Snd(_, e)         -> Ast.Snd(translate_expr_map(e, map))
    | Past.Inl(_, _, e)       -> Ast.Inl(translate_expr_map(e, map))
    | Past.Inr(_, _, e)       -> Ast.Inr(translate_expr_map(e, map))
    | Past.Case(_, e, l1, l2) -> 
         Ast.Case(translate_expr_map(e, map), translate_lambda(l1, map), translate_lambda(l2, map)) 
    | Past.Lambda(_, l)      -> Ast.Lambda (translate_lambda (l, map))
    | Past.App(_, e1, e2)    -> Ast.App(translate_expr_map(e1, map), translate_expr_map(e2, map))
    (*
       Replace "let" with abstraction and application. For example, translate 
        "let x = e1 in e2 end" to "(fun x -> e2) e1" 
    *) 
    | Past.Let(_, x, _, e1, e2) -> 
         Ast.App(Ast.Lambda(x, translate_expr_map(e2, map)), translate_expr_map(e1, map))
    | Past.LetFun(_, f, l, _, e)     -> 
         Ast.LetFun(f, translate_lambda(l, map), translate_expr_map(e, map))
    | Past.LetTupleFun(_, f, l, _, e)     -> 
         Ast.LetFun(f, translate_tuple_lambda(f, l, map), translate_expr_map(e, map))
    | Past.LetRecFun(_, f, l, _, e)     -> 
         Ast.LetRecFun(f, translate_lambda(l, map), translate_expr_map(e, map))

    | Past.Seq(_, e1) -> Ast.Seq(List.map (function x -> translate_expr_map(x, map)) e1)
    | Past.While(_, e1, e2) -> Ast.While(translate_expr_map(e1, map), translate_expr_map(e2, map))
    | Past.Ref(_, e) -> Ast.Ref(translate_expr_map(e, map))
    | Past.Deref(_, e) -> Ast.Deref(translate_expr_map(e, map))
    | Past.Assign(_, e1, e2) -> Ast.Assign(translate_expr_map(e1, map), translate_expr_map(e2, map))

and translate_lambda = function((x, _, body), map) -> (x, translate_expr_map(body, map))
and translate_tuple_lambda = function(f, (tuples, _, body), map) -> (f, translate_t_lambda(tuples, translate_expr_map(body, map), Ast.Var(f)))

let update_map map (k, v) = function lookup -> if lookup = k then v else map lookup

let empty_map = function lookup -> Ast.Var lookup

let rec translate_expr e = translate_expr_map (e, empty_map)