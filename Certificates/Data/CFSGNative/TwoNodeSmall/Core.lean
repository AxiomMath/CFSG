module

public section

namespace CFSG.TwoNodeSmall

set_option compiler.extract_closed false

abbrev Vec := List Nat
abbrev Word := List Nat

structure Refl where
  f : Vec
  h : Vec

structure Pt where
  p : Nat
  D : Nat
  nFrame : Nat
  gens : List Refl
  x : Vec
  bound : Nat

structure TWit where
  word : Word
  u : Vec
  φ : Vec

structure Level where
  base : Vec
  strong : List Word
  tree : List (Vec × Nat × Nat)

structure OWit where
  levels : List Level

structure WWit where
  kind : Nat
  sigma : List (Word × Nat)
  expr : List Word
  chain : OWit

inductive Witness
  | kernel (w : Vec)
  | transv (t : TWit)
  | order (o : OWit)
  | weyl (c : WWit)

@[expose] def Pt.dotv (P : Pt) (f v : Vec) : Nat :=
  (((List.range P.D).map fun i => f.getD i 0 * v.getD i 0).foldl (· + ·) 0) % P.p

@[expose] def Pt.applyRefl (P : Pt) (r : Refl) (v : Vec) : Vec :=
  let c := P.dotv r.f v
  (List.range P.D).map fun i => (v.getD i 0 + (P.p - (c * r.h.getD i 0) % P.p)) % P.p

@[expose] def Pt.applyWord (P : Pt) (w : Word) (v : Vec) : Vec :=
  w.foldr (fun i acc => match P.gens[i]? with
    | some r => P.applyRefl r acc
    | none => acc) v

@[expose] def Pt.wordOK (P : Pt) (w : Word) : Bool := w.all fun i => decide (i < P.gens.length)

@[expose] def Pt.unit (P : Pt) (i : Nat) : Vec := (List.range P.D).map fun j => if j = i then 1 else 0

end CFSG.TwoNodeSmall
