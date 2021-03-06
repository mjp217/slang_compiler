let rev (p : int * int) : int * int  = (snd p, fst p) 
in 
    let cat (a: int) : int * int = rev (21, a) 
	in 
      cat 9
    end	  
end