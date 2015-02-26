structure MuKanren = struct

  type var = int
  datatype term = Var of var | Pair of term * term | Int of int

  (* walk : term -> subst -> term option *)
  fun walk u s =
    (case u of
       Var u => (case List.find (fn (v,t) => u = v) s of
                      NONE => Var u
                    | SOME (u, t) => walk t s)
    | t => t)

  fun extend s (v,t) = (v,t)::s

  fun unify u v s =
    case (walk u s, walk v s) of
        (Var u, Var v) => if u = v 
                          then SOME s 
                          else SOME (extend s (u, Var v)) 
      | (Var u, _) => SOME (extend s (u,v))
      | (_, Var v) => SOME (extend s (v,u))
      | (Pair (u1, u2), Pair (v1, v2)) =>
          (case unify u1 u2 s of
              NONE => NONE
            | SOME s => unify u2 v2 s)
      | (Int i1, Int i2) => if i1 = i2 then SOME s else NONE
      | (_, _) => NONE

  (* mixed lazy/eager lists *)
  datatype 'a stream = Nil 
                     | Cons of 'a * 'a stream 
                     | Lazy of (unit -> 'a stream)
  val mzero = Nil
  fun unit_ state = Cons (state, mzero)

  (* mplus : state stream -> state stream -> state stream *)
  fun mplus a1 a2 = 
    case (a1, a2) of
         (Nil, _) => a2
       | (Cons(st,a1), a2) => Cons (st, mplus a1 a2)
       | (Lazy a1, a2) => Lazy (fn () => mplus a2 (a1()))

  (* bind : state stream -> goal -> state list *)
  fun bind states goal =
    case states of
         Nil => mzero
       | (Cons(st,states)) => mplus (goal st) (bind states goal)
       | (Lazy f) => Lazy (fn () => bind (f()) goal)

  type subst = (var * term) list
  type state = subst * int
  type goal = state -> state stream

  (* equiv : term -> term -> (subst * int) -> state stream *)
  fun equiv u v : goal =
    fn (subst, counter) =>
      (case unify u v subst of
             NONE => mzero
           | SOME subst => unit_ (subst, counter) )

  (* call_fresh : (term -> term) -> (subst * int) -> state list *)
  fun call_fresh f : goal =
    fn (subst, counter) =>
      f (Var counter) (subst, counter + 1)

  (* disj : goal -> goal -> goal *)
  fun disj g1 g2 =
    fn (state, counter) => mplus (g1 (state, counter)) (g2 (state, counter))

  fun conj g1 g2 =
    fn (state, counter) => bind (g1 (state, counter)) g2 


  (* test cases *)
  val empty_state = ([], 0)

  fun five x = equiv x (Int 5)

  fun fives x = disj (equiv x (Int 5)) (fn sc => Lazy (fn () => (fives x) sc))
  val test_fives = call_fresh fives empty_state 

  fun force (Lazy f) = f ()

end
