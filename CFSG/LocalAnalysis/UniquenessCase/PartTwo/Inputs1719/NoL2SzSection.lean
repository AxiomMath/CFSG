module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def K_19_25_noL2SzSection : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (p : ℕ) (Y : Subgroup Q), p.Prime → p ≠ 2 →
    genFittingFStar Q ≤ Y → CFSG.pPrimeCore p Q = ⊥ →
    ((∃ m : ℕ, LieModel ↥Y .PSL 2 p m) ∨ (∃ m : ℕ, LieModel ↥Y .PSU 3 p m) ∨
      (p = 3 ∧ (F07.IsReeType ↥Y 1 ∨ IsSpor ↥Y .M11 ∨ IsL3 ↥Y 2)) ∨
      (p = 5 ∧ (F07.IsAutSz ↥Y 5 ∨ LieModel ↥Y .Tits 0 2 1 ∨ IsSpor ↥Y .McL ∨ IsAlt ↥Y 10)) ∨
      (p = 11 ∧ IsSpor ↥Y .J4)) →
    ∀ N : Subgroup Q, IsStronglyPEmbedded p N → ∀ n : ℕ, 3 ≤ n → ¬ HasL2SzSection n N

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
