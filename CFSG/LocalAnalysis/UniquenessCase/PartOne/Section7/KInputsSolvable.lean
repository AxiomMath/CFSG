module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Steps
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.GroupTheory.PCore.PrimeSetCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

@[expose] def StronglyEmbeddedSolvable : Prop :=
  ∀ p : ℕ, p.Prime → 5 ≤ p →
    ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsKGroup X → CFSG.pPrimeCore p X = ⊥ →
      2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) → ∀ N : Subgroup X, IsStronglyPEmbedded p N →
        ¬ CoverHasLargeTwoLocal ↥(CFSG.generalizedFitting X) →
        IsSolvable ↥N ∨ (p = 5 ∧ (Nat.card N).factorization 5 ≤ 2 ∧
          ∀ Y : Subgroup X, Y ≤ N → ⁅Y, Y⁆ = Y → Nat.card Y ≤ 3600)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem solvable_or_of_stronglyEmbeddedSolvable (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (h3 : 3 ∉ CFSG.Open.uniqueFourBeta G) {H : Subgroup G}
    (hH : Config k H) (h75 : Step75 k) (hS : StronglyEmbeddedSolvable) :
    IsSolvable ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∨
      (k.p = 5 ∧
        (Nat.card ↥(((H ⊓ k.M).subgroupOf H).map
          (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)))).factorization 5 ≤ 2 ∧
        ∀ Y : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H),
          Y ≤ ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) →
          ⁅Y, Y⁆ = Y → Nat.card Y ≤ 3600) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  exact hS k.p hp h5 _
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH (CFSG.pPrimeCore k.p ↥H))
    (CFSG.pPrimeCore_quotient_eq_bot hp) (k.two_le_pRank_quotient_pPrimeCore hH) _
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) (k.not_coverHasLargeTwoLocal h3 hH h75)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
