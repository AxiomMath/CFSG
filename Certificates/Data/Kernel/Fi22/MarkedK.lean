module

public import Certificates.Data.FischerMarkedReflection
public import Certificates.Data.Kernel.Fi22.LHK
public import CFSG.Certificates.Kernel.Common.HexNat

public section

namespace CFSG.KS.Fi22Marked

open CFSG.OddTranspositions.FischerMarked CFSG.KS.Fi22LH

@[expose] def markedText : String := include_str "marked.hex"

@[expose] noncomputable def markedTree : Nat := by hex_nat markedText 2370 14160839323748003830

@[expose] def tf (T i o : Nat) : Nat := Nat.land (Nat.shiftRight T (27 * i + o)) 511

@[expose] def pointsText : String := include_str "points.hex"

@[expose] noncomputable def pointsData : Nat := by hex_nat pointsText 5974 3447354730479907151

@[expose] def pcN (P a : Nat) : Nat := Nat.land (Nat.shiftRight P (12 * a)) 4095

@[expose] def piN (P c : Nat) : Nat := Nat.land (Nat.shiftRight P (4212 + 9 * c)) 511

@[expose] def pointsOK (P : Nat) : Prop :=
  (List.range 351).map (pcN P) = pointCodes.toList ∧
    (List.range 2187).map (piN P) = pointIndices.toList

@[expose] def dg (c k : Nat) : Nat := c / 3 ^ k % 3

@[expose] def tN (c d : Nat) : Nat :=
  (dg d 0 * dg c 0 + dg d 1 * dg c 1 + dg d 2 * dg c 2 + dg d 3 * dg c 3 + dg d 4 * dg c 4 +
    dg d 5 * dg c 5 + dg d 6 * dg c 6) % 3

@[expose] def rN (c d k : Nat) : Nat := (dg d k + tN c d * dg c k) % 3

@[expose] def reflN (c d : Nat) : Nat :=
  rN c d 0 + 3 * (rN c d 1 + 3 * (rN c d 2 + 3 * (rN c d 3 + 3 * (rN c d 4 +
    3 * (rN c d 5 + 3 * rN c d 6)))))

@[expose] def sigN (P a j : Nat) : Nat := piN P (reflN (pcN P a) (pcN P j)) % 351

@[expose] def rowsOK (R : Nat → Nat) (S T P : Nat) : Prop :=
  (∀ j < 351, ent S j < 3510) ∧
    ∀ a < 351, tf T a 18 < 7 → ∀ j < 351, ent (R (ent S a)) (ent S j) = ent S (sigN P a j)

@[expose] def treeOK (T P : Nat) : Prop :=
  ∀ i < 351, 7 ≤ tf T i 18 → tf T i 0 < 351 ∧ tf T i 9 < 351 ∧
    tf T (tf T i 0) 18 < tf T i 18 ∧ tf T (tf T i 9) 18 < tf T i 18 ∧
      sigN P (tf T i 0) (tf T i 9) = i

end CFSG.KS.Fi22Marked
