module

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91CoreArith
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91PrimeCoreD4Two
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91PrimeCoreD4One
import CFSG.Timmesfeld.Orders.Exceptional
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22


theorem primeCore_d4 {X : Type} [Group X] [Finite X] {n : ℕ} (h : Is3D4 X n) :
    Nat.card X = 2 ^ (12 * n) * (2 ^ (8 * n) + 2 ^ (4 * n) + 1) * (2 ^ (6 * n) - 1) *
        (2 ^ (2 * n) - 1) ∧
    ∀ p : ℕ, p.Prime → 5 ≤ p →
      CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 2 ∧
      (CFSG.Open.pRank p (⊤ : Subgroup X) = 2 ↔ p ∣ 2 ^ (6 * n) - 1) ∧
      (p ∣ Nat.card X → p ∣ 2 ^ (6 * n) - 1 ∨ p ∣ 2 ^ (4 * n) - 2 ^ (2 * n) + 1) := by
  have hcard : Nat.card X = ordTrialityD4 (2 ^ n) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two
      (CFSG.Blueprint.LieModel.chevalleyExceptionalModel h (by decide))
  refine ⟨hcard.trans (ordTrialityD4_two_pow_eq n), fun p hp hp5 => ?_⟩
  refine ⟨?_, ⟨fun h2 => ?_, fun hpd => pRank_d4_eq_two h hp hp5 hpd⟩, fun hpX => ?_⟩
  · by_cases hpd : p ∣ 2 ^ (6 * n) - 1
    · exact (pRank_d4_eq_two h hp hp5 hpd).le
    · exact (pRank_d4_le_one h hp hp5 hpd).trans (by norm_num)
  · by_contra hpd
    have h1 := pRank_d4_le_one h hp hp5 hpd
    omega
  · exact dvd_or_dvd_of_dvd_ordTrialityD4 hp hp5 (hcard ▸ hpX)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R891Core
