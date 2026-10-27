module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Step75
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Step74

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem stronglyEmbeddedThree_at {p : ℕ} (hp3 : p = 3) (hK : StronglyEmbeddedThree) {X : Type}
    [Group X] [Finite X] (hKX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore p X = ⊥)
    (hrank : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) :
    CoverActsTriviallyOnSmall p ↥(CFSG.generalizedFitting X) ∧
      Nat.card ↥(CFSG.pPrimeCore p ↥N) ≤ 2 ∧
      CentralizerHasPElementOutside p N ∧
      IsSolvable ↥N := by
  subst hp3
  exact hK X hKX hO hrank N hN

namespace Sec7Core4

theorem kInputThree (k : Sec7Core4 G) (hp3 : k.p = 3) (hK : StronglyEmbeddedThree)
    {H : Subgroup G} (hH : Config k H) :
    CoverActsTriviallyOnSmall k.p ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ∧
      Nat.card ↥(CFSG.pPrimeCore k.p
        ↥(((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)))) ≤ 2 ∧
      CentralizerHasPElementOutside k.p
        (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) ∧
      IsSolvable ↥(((H ⊓ k.M).subgroupOf H).map
        (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) := by
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  exact stronglyEmbeddedThree_at hp3 hK
    (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH (CFSG.pPrimeCore k.p ↥H))
    (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.two_le_pRank_quotient_pPrimeCore hH)
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH)

theorem step75_of_stronglyEmbeddedThree (k : Sec7Core4 G) (hp3 : k.p = 3)
    (hK : StronglyEmbeddedThree) : Step75 k :=
  step75_of_coverActsTriviallyOnSmall k fun _ hH => (k.kInputThree hp3 hK hH).1

theorem step76C_of_stronglyEmbeddedThree (k : Sec7Core4 G) (hp3 : k.p = 3)
    (hK : StronglyEmbeddedThree) : Step76C k :=
  step76C_of_centralizerHasPElementOutside k fun _ hH => (k.kInputThree hp3 hK hH).2.2.1

theorem step74w_of_stronglyEmbeddedThree (k : Sec7Core4 G) (hp3 : k.p = 3)
    (hK : StronglyEmbeddedThree) : Step74w k := by
  intro H hH
  exact card_pCoreOf_inf_le_two k.prime k.odd
    (k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank) (k.kInputThree hp3 hK hH).2.1

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
