module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerBar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CyclicCentralizerRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_centralizerBar_eq_bot_of_ker {P Q L : Subgroup G} (hQ : Q ≤ L)
    (hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hker : centralizerBar P L ⊓ L ≤ CFSG.Open.pCoreOf 2 L) :
    Q ⊓ centralizerBar P L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hzQ, hzC⟩ := Subgroup.mem_inf.mp hz
  have hzO : z ∈ CFSG.Open.pCoreOf 2 L := hker ⟨hzC, hQ hzQ⟩
  have hzQO : z ∈ Q ⊓ CFSG.Open.pCoreOf 2 L := ⟨hzQ, hzO⟩
  rwa [hQO2] at hzQO

theorem isCyclic_centralizerBar_of_pRank {P Q L : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hQP : Q ≤ P) (hQL : Q ≤ L) (hP3 : IsPGroup 3 P)
    (hPrank : CFSG.Open.pRank 3 P ≤ 3)
    (hQO2 : Q ⊓ CFSG.Open.pCoreOf 2 L = ⊥)
    (hker : centralizerBar P L ⊓ L ≤ CFSG.Open.pCoreOf 2 L)
    (hQnormP : (Q.subgroupOf P).Normal) :
    IsCyclic (centralizerBar P L) := by
  haveI hQn : (Q.subgroupOf P).Normal := hQnormP
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer_of_normal_subgroupOf hQP
  have hcommBot : ⁅Q, centralizerBar P L⁆ = ⊥ :=
    commutator_eq_bot_centralizerBar hQL hQO2 hPQ
  have hcomm : ∀ q ∈ Q, ∀ c ∈ centralizerBar P L, q * c = c * q := by
    intro q hq c hc
    have hmem : ⁅q, c⁆ = 1 := by
      have hmem' : ⁅q, c⁆ ∈ ⁅Q, centralizerBar P L⁆ :=
        Subgroup.commutator_mem_commutator hq hc
      rwa [hcommBot, Subgroup.mem_bot] at hmem'
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  exact isCyclic_of_extraspecial_left_of_pRank_le_three (P := P) (Q := Q)
    (C := centralizerBar P L) hQ hQP (centralizerBar_le P L) hP3 hPrank hcomm
    (inf_centralizerBar_eq_bot_of_ker hQL hQO2 hker)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
