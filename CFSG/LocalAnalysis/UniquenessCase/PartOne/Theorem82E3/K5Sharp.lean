module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)

@[expose] def K5A10Sharp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    IsAlt (Y ⧸ center Y) 10 → ∀ p : ℕ, p.Prime → 7 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1

@[expose] def K5A11Sharp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → Odd (Nat.card (center Y)) →
    IsAlt (Y ⧸ center Y) 11 → ∀ p : ℕ, p.Prime → 7 ≤ p →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1

@[expose] def K5ONanSharp : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], ThreeCover (fun Z _ => IsSpor Z .ONan) Y →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ 7 →
      pRank p (⊤ : Subgroup (MulAut Y)) ≤ 1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
