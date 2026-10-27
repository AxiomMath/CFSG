module

public import Certificates.Data.Kernel.Ssa3

public section

namespace CFSG.KC.Ssa3

open CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def memS (x : Nat) : List Nat → Bool
  | [] => false
  | y :: C => Nat.beq x y || memS x C

@[expose] def powL (e : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [(z, k)] => [(z, k * e)]
  | l => (List.replicate e l).flatten

@[expose] def exS (D : SData) (C : List Nat) : Nat → Nat → List (Nat × Nat)
  | 0, x => [(x, 1)]
  | f + 1, x =>
    bif Nat.blt x 2 || memS x C then [(x, 1)] else bif Nat.beq x 2 then [] else
    bif Nat.blt (D.na.getD (x - 3) 0) x && Nat.blt (D.nb.getD (x - 3) 0) x then
      bif Nat.beq (D.nk.getD (x - 3) 1) 0 then
        exS D C f (D.na.getD (x - 3) 0) ++ exS D C f (D.nb.getD (x - 3) 0)
      else powL (D.nk.getD (x - 3) 1) (exS D C f (D.na.getD (x - 3) 0))
    else []

@[expose] def consM (z e : Nat) : List (Nat × Nat) → List (Nat × Nat)
  | [] => [(z, e)]
  | (y, k) :: r => bif Nat.beq z y then (z, e + k) :: r else (z, e) :: (y, k) :: r

@[expose] def mergeS : List (Nat × Nat) → List (Nat × Nat)
  | [] => []
  | (z, e) :: l => bif Nat.beq e 0 then mergeS l else consM z e (mergeS l)

@[expose] def wexS (D : SData) (C : List Nat) (f : Nat) : Word → List (Nat × Nat)
  | [] => []
  | (r, e) :: w => powL e (exS D C f (D.fv.getD r 0)) ++ wexS D C f w

@[expose] def eqL : List (Nat × Nat) → List (Nat × Nat) → Bool
  | [], [] => true
  | (a, b) :: l, (c, e) :: m => Nat.beq a c && Nat.beq b e && eqL l m
  | _, _ => false

@[expose] def freeS (D : SData) (f : Nat) (w₁ w₂ : Word) : Bool :=
  eqL (mergeS (wexS D (w₂.map fun p => D.fv.getD p.1 0) f w₁))
    (mergeS (wexS D (w₂.map fun p => D.fv.getD p.1 0) f w₂))

@[expose] def freeF (D : SData) (n f : Nat) : MFact → Bool
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && freeS D f w₁ w₂
  | _ => false

@[expose] def coverS (D : SData) (n f : Nat) (facts : List MFact) : Bool :=
  (List.range facts.length).all fun i =>
    (List.range D.qk.length).any (fun q => Nat.beq (D.qf.getD q 0) i) ||
      freeF D n f (facts.getD i (.eq [] []))

end CFSG.KC.Ssa3

end
