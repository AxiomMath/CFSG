module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureIndexTwo
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureOddCore
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalStabilizer
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionIndexTwo

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open CFSG.BenderSuzuki CFSG.ProperTwoGeneratedCore
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

universe u

variable {G : Type u} [Group G]

theorem minimalLocalFailure_normal_involution_extension_index_two
    (M : Subgroup G) [M.Normal] {z : G} (hz : orderOf z = 2) (hzM : z ∉ M) :
    (M.subgroupOf (M ⊔ Subgroup.zpowers z)).index = 2 := by
  let K := M ⊔ Subgroup.zpowers z
  have hzK : z ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
  let zK : K := ⟨z, hzK⟩
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨zK, hzM, ?_⟩
  intro k
  obtain ⟨m, hm, a, ha, hma⟩ := Subgroup.mem_sup_of_normal_left.mp k.property
  rcases involution_zpowers_elements hz ha with haone | haz
  · right
    change (k : G) ∈ M
    rw [← hma, haone, mul_one]
    exact hm
  · left
    change (k : G) * z ∈ M
    rw [← hma, haz, mul_assoc]
    have hzz : z * z = 1 := by simpa only [pow_two] using (orderOf_eq_prime_iff.mp hz).1
    rw [hzz, mul_one]
    exact hm

variable [Finite G]

theorem minimalLocalFailure_normal_eq_bot_or_top
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (M : Subgroup G) [M.Normal] : M = ⊥ ∨ M = ⊤ := by
  obtain ⟨hhull, hodd, htwo⟩ := minimalLocalFailure_involution_hull_and_cores h
  have hcenter := center_eq_bot_of_actual_odd_core_and_two_core hodd htwo
  obtain ⟨S, hzS, hzcenter⟩ := h.central_sylow
  have hzcentral : ∀ s ∈ (S : Subgroup G), Commute z s := by
    intro s hs
    exact (congrArg Subtype.val
      ((Subgroup.mem_center_iff.mp hzcenter) (⟨s, hs⟩ : (S : Subgroup G)))).symm
  by_cases hzM : z ∈ M
  · right
    apply top_le_iff.mp
    rw [← hhull]
    apply (Subgroup.closure_le _).mpr
    rintro d ⟨g, rfl⟩
    exact (inferInstance : M.Normal).conj_mem' z hzM g
  · by_cases hMbot : M = ⊥
    · exact Or.inl hMbot
    · exfalso
      have hMescape : ¬ M ≤ H := by
        intro hMH
        have hMC := local_involution_point_normal_stabilizer_subgroup_central
          h.local_datum S hzS hzcentral hhull hodd M hMH
        rw [hcenter] at hMC
        exact hMbot (le_antisymm hMC bot_le)
      let K := M ⊔ Subgroup.zpowers z
      have hMK : M ≤ K := le_sup_left
      have hzK : z ∈ K := Subgroup.mem_sup_right (Subgroup.mem_zpowers z)
      let zK : K := ⟨z, hzK⟩
      let A := M.subgroupOf K
      let : A.Normal := inferInstance
      have hindex : A.index = 2 :=
        minimalLocalFailure_normal_involution_extension_index_two M
          h.local_datum.distinguished_order hzM
      by_cases hK : K = ⊤
      · have hMindex : M.index = 2 := by
          have hrel : M.relIndex K = 2 := hindex
          rw [hK, Subgroup.relIndex_top_right] at hrel
          exact hrel
        exact hzM (involution_point_odd_core_free_index_two_obstruction
          h.local_datum h.central_sylow hodd M inferInstance hMindex)
      · have hKescape : ¬ K ≤ H := fun hKH => hMescape (hMK.trans hKH)
        obtain ⟨_, _, _, _, _, hcentral, _, _⟩ :=
          minimalLocalFailure_smaller_index_two_Zstar h K hK hzK hKescape A hindex hzM
        have hzMcomm : ∀ m ∈ M, Commute z m := by
          intro m hm
          let mK : K := ⟨m, hMK hm⟩
          let cK : K := zK * mK * zK⁻¹ * mK⁻¹
          have hcM : (cK : G) ∈ M :=
            M.mul_mem ((inferInstance : M.Normal).conj_mem m hm z) (M.inv_mem hm)
          have hcOdd : cK ∈ oddCore K := by
            apply (QuotientGroup.eq_one_iff cK).mp
            have hcomm : (QuotientGroup.mk mK : K ⧸ oddCore K) * QuotientGroup.mk zK =
                QuotientGroup.mk zK * QuotientGroup.mk mK :=
              Subgroup.mem_center_iff.mp hcentral (QuotientGroup.mk mK)
            change (QuotientGroup.mk cK : K ⧸ oddCore K) = 1
            dsimp only [cK]
            simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
            rw [← hcomm]
            group
          have hc1 : (cK : G) = 1 :=
            actual_odd_core_intermediate_normal_element_eq_one hodd M K hMK hcM hcOdd
          have hcomm : z * m * z⁻¹ * m⁻¹ = 1 := hc1
          have heq := congrArg (fun a : G => a * (m * z)) hcomm
          change z * m = m * z
          simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one, one_mul]
            using heq
        let C := Subgroup.centralizer (M : Set G)
        have hzC : z ∈ C := Subgroup.mem_centralizer_iff.mpr
          (fun m hm => (hzMcomm m hm).symm.eq)
        have hclass : involutionPointClass z ⊆ C := by
          rintro d ⟨g, rfl⟩
          exact (inferInstance : C.Normal).conj_mem' z hzC g
        have hCtop : C = ⊤ := by
          apply top_le_iff.mp
          rw [← hhull]
          exact (Subgroup.closure_le _).mpr hclass
        have hMC : M ≤ Subgroup.center G := Subgroup.centralizer_eq_top_iff_subset.mp hCtop
        rw [hcenter] at hMC
        exact hMbot (le_antisymm hMC bot_le)

theorem minimalLocalFailure_nonabelian_simple
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z) :
    IsSimpleGroup G ∧ ∃ a b : G, a * b ≠ b * a := by
  have hz1 : z ≠ 1 := (orderOf_eq_prime_iff.mp h.local_datum.distinguished_order).2
  let : Nontrivial G := ⟨⟨z, 1, hz1⟩⟩
  have hsimple : IsSimpleGroup G := ⟨fun M hM => by
    let : M.Normal := hM
    exact minimalLocalFailure_normal_eq_bot_or_top h M⟩
  refine ⟨hsimple, ?_⟩
  by_contra hnonab
  push Not at hnonab
  have hzcenter : z ∈ Subgroup.center G :=
    Subgroup.mem_center_iff.mpr (fun a => hnonab a z)
  have hcenter := center_eq_bot_of_actual_odd_core_and_two_core
    (minimalLocalFailure_odd_core_eq_bot h) (minimalLocalFailure_two_core_eq_bot h)
  rw [hcenter] at hzcenter
  exact hz1 (Subgroup.mem_bot.mp hzcenter)

end CFSG.ShultStronglyClosedTI
