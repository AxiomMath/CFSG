module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811 IsSignedCoords)

@[expose] def K7L6TwoCentA : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLie811 Y .l6 2 1 →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
      Nat.card (centralizer (A : Set Y)) = 27

@[expose] def K7L6TwoPerfect : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsLie811 Y .l6 2 1 →
    ∀ A : Subgroup Y, IsElemAbelian 3 A → Nat.card A = 27 →
    ∀ c, IsSignedCoords A c → ∀ v : Fin 3 → ZMod 3, (v = ![1, 0, 0] ∨ v = ![1, 1, 1]) →
      ∃ K : Subgroup Y, K ≤ centralizer ({c (.ofAdd v)} : Set Y) ∧ ⁅K, K⁆ = K ∧
        7 ∣ Nat.card K

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
