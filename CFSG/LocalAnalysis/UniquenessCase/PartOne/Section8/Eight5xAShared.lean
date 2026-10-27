module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.PRankLeOfSylowLe
import CFSG.LocalAnalysis.SectionRank.TwoGenerators
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight62CenterOfNormal
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Pair

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)

theorem normalizer_le_of_card_three_of_gamma {G : Type} [Group G] [Finite G] {M Q X : Subgroup G}
    (hΓ : rankThreeGamma 1 3 Q ≤ M) (hXQ : X ≤ Q) (hX : Nat.card X = 3) :
    Subgroup.normalizer (X : Set G) ≤ M := by
  have hXel : IsElemAbelian 3 X := CFSG.GroupTheory.isElemAbelian_of_card_prime hX
  have hrank : 1 ≤ CFSG.Open.pRank 3 X :=
    CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl hXel (by rw [hX]; norm_num)
  exact (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (p := 3) (k := 1) hXQ
    hrank).trans hΓ

theorem Cex856.pRank_sylowQ_eq_two {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (h : Cex856 D L Q P) : CFSG.Open.pRank 3 Q = 2 := by
  have hle : CFSG.Open.pRank 3 Q ≤ CFSG.Open.pRank 3 L :=
    CFSG.SectionRank.pRank_mono (by norm_num) h.sylowQ.le
  have hge : CFSG.Open.pRank 3 L ≤ CFSG.Open.pRank 3 Q :=
    CFSG.pRank_le_of_isSylowOf_le Nat.prime_three h.sylowQ.le h.sylowQ le_rfl
  have := h.rank
  omega

theorem Cex856.not_isCyclic_sylowQ {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (h : Cex856 D L Q P) : ¬ IsCyclic ↥Q := by
  intro hcyc
  have h1 := CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcyc
  have h2 := h.pRank_sylowQ_eq_two
  omega

theorem Cex856.pRank_sylowP_le_three {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (hSg : CFSG.LocalAnalysis.UniquenessCase.UC6S846.SigmaStd D)
    (h : Cex856 D L Q P) : CFSG.Open.pRank 3 P ≤ 3 :=
  (CFSG.SectionRank.pRank_mono (by norm_num) h.sylowP.le).trans
    (CFSG.LocalAnalysis.UniquenessCase.UC22.R8107E3.pRank_three_le_three_of_not_sp hSg
      h.notStrong h.mem)

theorem Cex856.inf_pCore_eq_bot {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (h : Cex856 D L Q P) : Q ⊓ pCoreOf 2 L = ⊥ :=
  (IsPGroup.disjoint_of_ne 3 2 (by norm_num) Q (pCoreOf 2 L) h.sylowQ.isPGroup
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)).eq_bot

theorem Cex856.le_normalizer_sylowQ {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P : Subgroup G} (h : Cex856 D L Q P) (h859 : R859 D) :
    P ≤ Subgroup.normalizer (Q : Set G) :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer h.le).mp
    (normal_subgroupOf_of_isSylowOf_of_le_normalizer h.sylowQ h.le h.sylowP.isPGroup
      (h859 L Q P h))

theorem ChoiceX.not_le_sylowQ {G : Type} [Group G] [Finite G] {D : Data G}
    {L Q P X : Subgroup G} (h : ChoiceX D L Q P X) : ¬ X ≤ Q := by
  intro hXQ
  exact h.notLe ((Subgroup.centralizer_le_normalizer (X : Set G)).trans
    (normalizer_le_of_card_three_of_gamma h.cex.gamma hXQ h.card))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
