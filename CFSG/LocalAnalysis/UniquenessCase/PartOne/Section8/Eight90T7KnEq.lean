module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
import CFSG.LocalAnalysis.GLTheoremA.PComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

theorem r890_false_of_isQuasisimple_perfInter {G : Type} [Group G] [Finite G] {J C N : Subgroup G}
    {n : ℕ} (hKX : perfInter890 J C ≤ perfInter890 J N)
    (hJ : perfInter890 J C ⊔ pCoreOf 2 J = J)
    (hF : Fstar (perfInter890 J C) = pCoreOf 2 (perfInter890 J C))
    (hSz : IsSz (Bar2 (perfInter890 J N)) n)
    (hQ : CFSG.Open.IsQuasisimple ↥(perfInter890 J N)) : False := by
  set K : Subgroup G := perfInter890 J C with hK
  set X : Subgroup G := perfInter890 J N with hX
  have hXJ : X ≤ J := by rw [hX]; exact r890_perfInter_le_left J N
  have hJeq : J = X ⊔ pCoreOf 2 J := by
    apply le_antisymm
    · calc J = K ⊔ pCoreOf 2 J := hJ.symm
        _ ≤ X ⊔ pCoreOf 2 J := sup_le_sup hKX le_rfl
    · exact sup_le hXJ (CFSG.LieType.BorelTits.pCoreOf_le 2 J)
  have hQeq : pCoreOf 2 X = X ⊓ pCoreOf 2 J :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.pCoreOf_eq_inf hXJ hJeq
  have hKnorm : K ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    (hKX.trans hXJ).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J)
  have hJmul : (J : Set G) = (K : Set G) * (pCoreOf 2 J : Set G) := by
    have h := Subgroup.coe_mul_of_left_le_normalizer_right K (pCoreOf 2 J) hKnorm
    rwa [hJ] at h
  have hrep : ∀ x ∈ X, ∃ k ∈ K, ∃ q ∈ pCoreOf 2 X, k * q = x := by
    intro x hx
    have hxJ : x ∈ (J : Set G) := hXJ hx
    rw [hJmul, Set.mem_mul] at hxJ
    obtain ⟨k, hk, z, hz, hkz⟩ := hxJ
    have hz_eq : z = k⁻¹ * x := by rw [← hkz]; group
    have hzX : z ∈ X := by
      rw [hz_eq]
      exact X.mul_mem (hKX (K.inv_mem hk)) hx
    have hzQ : z ∈ pCoreOf 2 X := by rw [hQeq]; exact ⟨hzX, hz⟩
    exact ⟨k, hk, z, hzQ, hkz⟩
  have hQleX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hQne : pCoreOf 2 X ≠ X := by
    intro hEq
    haveI : Group.IsPerfect ↥X := ⟨hQ.1⟩
    haveI : Nontrivial ↥X := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_nontrivial hQ
    have h2 : IsPGroup 2 ↥X := by
      rw [← hEq]
      exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X
    haveI : Group.IsNilpotent ↥X := IsPGroup.isNilpotent (p := 2) h2
    exact (Group.IsPerfect.not_isSolvable ↥X) inferInstance
  have hQcent : ∀ q ∈ pCoreOf 2 X, ∀ x ∈ X, q * x = x * q := by
    have hMnorm : ((pCoreOf 2 X).subgroupOf X).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQleX).mpr
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    have hMle : (pCoreOf 2 X).subgroupOf X ≤ Subgroup.center ↥X :=
      CFSG.LocalAnalysis.GLTheoremA.le_center_of_normal_of_isQuasisimple hQ hMnorm (by
        intro htop
        apply hQne
        apply le_antisymm hQleX _
        intro q hq
        have hqtop : (⟨q, hq⟩ : ↥X) ∈ (pCoreOf 2 X).subgroupOf X := by
          rw [htop]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf).mp hqtop)
    intro q hq x hx
    have hq' : (⟨q, hQleX hq⟩ : ↥X) ∈ Subgroup.center ↥X :=
      hMle ((Subgroup.mem_subgroupOf).mpr hq)
    have hcomm := Subgroup.mem_center_iff.mp hq' (⟨x, hx⟩ : ↥X)
    exact (congrArg Subtype.val hcomm).symm
  have hcommK : ⁅X, X⁆ ≤ K := by
    apply Subgroup.commutator_le.mpr
    intro a ha b hb
    obtain ⟨k1, hk1, q1, hq1, hkq1⟩ := hrep a ha
    obtain ⟨k2, hk2, q2, hq2, hkq2⟩ := hrep b hb
    rw [← hkq1, ← hkq2]
    have hk1X : k1 ∈ X := hKX hk1
    have hk2X : k2 ∈ X := hKX hk2
    have hq1X : q1 ∈ X := hQleX hq1
    have hq2X : q2 ∈ X := hQleX hq2
    have h1 : ⁅q1, k2 * q2⁆ = 1 := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr (hQcent q1 hq1 k2 hk2X),
        commutatorElement_eq_one_iff_mul_comm.mpr (hQcent q1 hq1 q2 hq2X)]
      group
    have h2 : ⁅k1, k2 * q2⁆ = ⁅k1, k2⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_eq_one_iff_mul_comm.mpr (hQcent q2 hq2 k1 hk1X).symm]
      group
    have hcomm : ⁅k1 * q1, k2 * q2⁆ = ⁅k1, k2⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul, h1, h2]
      group
    rw [hcomm]
    exact (Subgroup.commutator_le_of_le (le_refl K) (le_refl K))
      (Subgroup.commutator_mem_commutator hk1 hk2)
  have hXperf : ⁅X, X⁆ = X := by rw [hX]; exact r890_perfInter_perfect J N
  have hXleK : X ≤ K := by rw [← hXperf]; exact hcommK
  have hK_eq_X : K = X := le_antisymm hKX hXleK
  have hF' : Fstar X = pCoreOf 2 X := hK_eq_X ▸ hF
  have hqsX : CFSG.IsQuasisimple ↥X := by
    haveI : Group.IsPerfect ↥X := ⟨hQ.1⟩
    haveI : IsSimpleGroup (↥X ⧸ Subgroup.center ↥X) := hQ.2
    refine ⟨inferInstance, hQ.2, ?_⟩
    have h := Group.IsPerfect.not_isMulCommutative (↥X ⧸ Subgroup.center ↥X)
    simpa only [isMulCommutative_iff, not_forall] using h
  have hFstarX : Fstar X = X := by
    unfold Fstar
    rw [CFSG.Adapters.genFittingFStar_eq_foundations,
      CFSG.WholeGroup.generalizedFitting_eq_top_of_isQuasisimple hqsX]
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) X
  exact hQne (hFstarX.symm.trans hF').symm

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
