module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialCentralizerRank
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.ExtraspecialCommutator
import all CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open scoped commutatorElement

theorem two_le_pRank_three_centralizer_of_isExtraspecialExpP
    {G : Type} [Group G] [Finite G] {Q X : Subgroup G} {x y : G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hxQ : x ∈ Q) (hyQ : y ∈ Q) (hxy : ⁅x, y⁆ ≠ 1)
    (hQX : Q ≤ Subgroup.centralizer (X : Set G)) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G)) := by
  classical
  have hQdef := hQ
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ
  have hx3 : x ^ 3 = 1 := by
    have h := Monoid.pow_exponent_eq_one (⟨x, hxQ⟩ : ↥Q)
    rw [hQ.2.1] at h
    simpa using congrArg Subtype.val h
  have hzmem : ⁅x, y⁆ ∈ (Subgroup.center ↥Q).map Q.subtype :=
    commutator_mem_center_of_isExtraspecialExpP hQdef hxQ hyQ
  obtain ⟨zQ, hzQmem, hzQval⟩ := Subgroup.mem_map.mp hzmem
  have hzx : Commute ⁅x, y⁆ x := by
    have h : Commute zQ (⟨x, hxQ⟩ : ↥Q) :=
      (Subgroup.mem_center_iff.mp hzQmem (⟨x, hxQ⟩ : ↥Q)).symm
    rw [← hzQval]
    exact h.map Q.subtype
  have hzy : Commute ⁅x, y⁆ y := by
    have h : Commute zQ (⟨y, hyQ⟩ : ↥Q) :=
      (Subgroup.mem_center_iff.mp hzQmem (⟨y, hyQ⟩ : ↥Q)).symm
    rw [← hzQval]
    exact h.map Q.subtype
  exact two_le_pRank_three_centralizer_of_extraspecial hxQ hyQ hQX hx3 hxy hzx hzy

theorem two_le_pRank_three_centralizer_of_isExtraspecialExpP_exists
    {G : Type} [Group G] [Finite G] {Q X : Subgroup G}
    (hQ : CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP 3 1 ↥Q)
    (hQX : Q ≤ Subgroup.centralizer (X : Set G)) :
    2 ≤ CFSG.Open.pRank 3 (Subgroup.centralizer (X : Set G)) := by
  classical
  have hQdef := hQ
  unfold CFSG.LocalAnalysis.RankThreeUC.SmallClassTwoGroups.IsExtraspecialExpP at hQ
  have hnab : ¬ ∀ a b : ↥Q, a * b = b * a := by
    intro hcomm
    have hcenter : Subgroup.center ↥Q = ⊤ := by
      rw [eq_top_iff]
      intro z _
      rw [Subgroup.mem_center_iff]
      intro g
      exact hcomm g z
    have hcardQ : Nat.card ↥Q = 27 := by
      rw [hQ.1]
      norm_num
    have hcardZ : Nat.card (Subgroup.center ↥Q) = 3 := hQ.2.2.2
    rw [hcenter, Subgroup.card_top] at hcardZ
    omega
  obtain ⟨xQ, hxQ'⟩ := not_forall.mp hnab
  obtain ⟨yQ, hxyQ⟩ := not_forall.mp hxQ'
  have hxy : ⁅(xQ : G), (yQ : G)⁆ ≠ 1 := by
    intro h
    apply hxyQ
    have h' : ⁅xQ, yQ⁆ = 1 := by
      apply Q.subtype_injective
      simpa [map_commutatorElement] using h
    exact commutatorElement_eq_one_iff_mul_comm.mp h'
  exact two_le_pRank_three_centralizer_of_isExtraspecialExpP hQdef xQ.2 yQ.2 hxy hQX

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
