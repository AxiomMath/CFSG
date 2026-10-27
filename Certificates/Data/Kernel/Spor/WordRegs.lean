module

public import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.KS.WordRegs

@[expose] def flipC (c : Nat) : Nat := if c % 2 = 1 then c - 1 else c + 1

@[expose] def invW (w : List Nat) : List Nat := (w.map flipC).reverse

@[expose] def tieW (RW : List (List Nat)) (w : List Nat) (c : Nat) : Bool :=
  w == [c] || (c % 2 == 1 && decide (2 ≤ c / 2) && RW.getD (c / 2 - 2) [] == w)

@[expose] def updW (R : Nat → List Nat) (c : Nat) (w : List Nat) : Nat → List Nat :=
  fun r => if r = c then w else R r

@[expose] def triRegs : (Nat → List Nat) → List (Nat × Nat × Nat) → List Nat → Nat → List Nat
  | R, (_, _, c) :: P, g :: G => triRegs (updW R c [2 * g + 1]) P G
  | R, _, _ => R

@[expose] def triOK (RW : List (List Nat)) :
    (Nat → List Nat) → List (Nat × Nat × Nat) → List Nat → Bool
  | _, [], _ => true
  | R, (a, b, c) :: P, g :: G =>
    tieW RW (R a ++ R b) (2 * g + 1) && triOK RW (updW R c [2 * g + 1]) P G
  | _, _ :: _, [] => false

@[expose] def bprRegs :
    (Nat → List Nat) → List (Bool × Nat × Nat × Nat) → List Nat → Nat → List Nat
  | R, (true, _, _, c) :: P, g :: G => bprRegs (updW R c [2 * g + 1]) P G
  | R, (false, a, b, _) :: P, G => bprRegs (updW R b (invW (R a))) P G
  | R, _, _ => R

@[expose] def bprOK (RW : List (List Nat)) :
    (Nat → List Nat) → List (Bool × Nat × Nat × Nat) → List Nat → Bool
  | _, [], _ => true
  | R, (true, a, b, c) :: P, g :: G =>
    tieW RW (R a ++ R b) (2 * g + 1) && bprOK RW (updW R c [2 * g + 1]) P G
  | _, (true, _, _, _) :: _, [] => false
  | R, (false, a, b, _) :: P, G => bprOK RW (updW R b (invW (R a))) P G

@[expose] def sgnC (K : List Nat) (l : Int) : Nat :=
  if 0 < l then K.getD (l.natAbs - 1) 0 else flipC (K.getD (l.natAbs - 1) 0)

@[expose] def rootsOK (RW : List (List Nat)) : Bool :=
  (List.range RW.length).all fun k => (RW.getD k []).all fun c => decide (c / 2 < k + 2)

end CFSG.KS.WordRegs

end
