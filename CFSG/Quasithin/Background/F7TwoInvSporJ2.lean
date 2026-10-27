module

public import CFSG.Quasithin.Background.F7TwoInvSporModel
public import CFSG.Quasithin.Background.F7TwoInvL2Model
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAutOddCore
public import Certificates.Certificate7415

public section

namespace CFSG.Quasithin.F7Two

open CFSG.ComponentClassification.J2Cover CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.Blueprint

section Check


theorem j2InvChk_spec :
    permU * permA = permA * permU ∧ permTwoA * permA = permA * permTwoA ∧
      (permU * permB * permU⁻¹ * permB⁻¹) ^ 3 = 1 ∧ permU * permB * permU⁻¹ * permB⁻¹ ≠ 1 ∧
      (permTwoA * permB * permTwoA⁻¹ * permB⁻¹) ^ 3 = 1 ∧
      permTwoA * permB * permTwoA⁻¹ * permB⁻¹ ≠ 1 := by
  have h := Certificates.certificate7415
  simp only [j2InvChk, j2OrderThree, j2CommB, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5, h6⟩ := h
  have hA : Rep 315 autStrong[0]! permA := rep_permA
  have hB : Rep 315 autStrong[1]! permB := rep_permB
  have hBi : Rep 315 (invCand 315 autStrong[1]!) permB⁻¹ := rep_strong_inv (j := 1) (by norm_num)
  have hU : Rep 315 outerArr permU := rep_permU
  have hZ : Rep 315 twoAArr permTwoA := rep_permTwoA
  have hU' : Rep 315 outerArr permU⁻¹ := by rw [permU_inv]; exact hU
  have hZ' : Rep 315 twoAArr permTwoA⁻¹ := by rw [permTwoA_inv]; exact hZ
  have cU := rep_compA (rep_compA (rep_compA hU hB) hU') hBi
  have cZ := rep_compA (rep_compA (rep_compA hZ hB) hZ') hBi
  refine ⟨(eqA_iff (rep_compA hU hA) (rep_compA hA hU)).1 h1,
    (eqA_iff (rep_compA hZ hA) (rep_compA hA hZ)).1 h2, ?_, ?_, ?_, ?_⟩
  · rw [pow_three]
    exact (eqA_iff (rep_compA cU (rep_compA cU cU)) rep_idA).1 h3
  · intro h
    rw [← eqA_iff cU rep_idA] at h
    simp [h] at h4
  · rw [pow_three]
    exact (eqA_iff (rep_compA cZ (rep_compA cZ cZ)) rep_idA).1 h5
  · intro h
    rw [← eqA_iff cZ rep_idA] at h
    simp [h] at h6

theorem commutator_ab_not_two_element :
    ∀ n : ℕ, (permA * permB * permA⁻¹ * permB⁻¹) ^ 2 ^ n ≠ 1 := by
  have h12 : orderOf (permA * permB * permA⁻¹ * permB⁻¹) = 12 := by
    have h := at_j2_image_pair_count.2.2.2.1
    rw [← Subgroup.orderOf_coe] at h
    exact h
  refine pow_two_pow_ne_one_of_pow (s := 2) (m := 3) (by decide) ?_ ?_
  · have := pow_orderOf_eq_one (permA * permB * permA⁻¹ * permB⁻¹)
    rwa [h12] at this
  · exact pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h12]; norm_num)

end Check

section Seeds


theorem invAutGen_rConj_of_seeds {ρ : Equiv.Perm (Fin 315)} (hρ : ρ ∈ R)
    (ha : ρ * permA = permA * ρ) (hb : ∀ n : ℕ, (ρ * permB * ρ⁻¹ * permB⁻¹) ^ 2 ^ n ≠ 1) :
    InvAutGen P (rConj ⟨ρ, hρ⟩) :=
  invAutGen_of_conj_model (a := pa) (b := pb) (fun g => rConj_apply _ g) closure_pa_pb ha hb

end Seeds

section Classes


theorem invAutGen_rConj_reps :
    ∀ ρ ∈ [permA, permTwoA, permU], ∃ hρ : ρ ∈ R, InvAutGen P (rConj ⟨ρ, hρ⟩) := by
  obtain ⟨hu, hz, hu3, hu1, hz3, hz1⟩ := j2InvChk_spec
  intro ρ hρ
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hρ
  rcases hρ with rfl | rfl | rfl
  · exact ⟨P_le_R permA_mem, invAutGen_rConj_of_seeds _ rfl commutator_ab_not_two_element⟩
  · refine ⟨P_le_R permTwoA_mem, invAutGen_rConj_of_seeds _ hz ?_⟩
    exact pow_two_pow_ne_one_of_pow (s := 0) (m := 3) (by decide) (by simpa using hz3)
      (by simpa using hz1)
  · refine ⟨permU_mem_R, invAutGen_rConj_of_seeds _ hu ?_⟩
    exact pow_two_pow_ne_one_of_pow (s := 0) (m := 3) (by decide) (by simpa using hu3)
      (by simpa using hu1)

theorem invAutGen_P_involution :
    ∀ α : MulAut P, α * α = 1 → α ≠ 1 → InvAutGen P α := by
  intro α hα2 hα1
  set r : R := rAutEquiv.symm α with hr
  have hrα : rConj r = α := (rAutEquiv_apply r).symm.trans (rAutEquiv.apply_symm_apply α)
  have hr2 : r * r = 1 := by
    apply rConj_injective
    rw [map_mul, hrα, hα2, map_one]
  have hr1 : (r : Equiv.Perm (Fin 315)) ≠ 1 := by
    intro h1
    apply hα1
    have : r = 1 := Subtype.ext h1
    rw [← hrα, this, map_one]
  have hord : orderOf (r : Equiv.Perm (Fin 315)) = 2 := by
    refine orderOf_eq_prime ?_ hr1
    rw [pow_two]
    exact congrArg Subtype.val hr2
  obtain ⟨ρ, hρ, c, hc, hrc⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial.2.2.2.2.2.2.2.2.2.2.2.2.1
      (r : Equiv.Perm (Fin 315)) r.2 hord
  obtain ⟨hρR, hP⟩ := invAutGen_rConj_reps ρ hρ
  have hrR : r = ⟨c, P_le_R hc⟩ * ⟨ρ, hρR⟩ * ⟨c, P_le_R hc⟩⁻¹ := Subtype.ext hrc
  refine invAutGen_of_conj_aut (rConj ⟨c, P_le_R hc⟩) ?_ hP
  rw [← hrα, hrR, map_mul, map_mul, map_inv]

theorem invAutGen_carrier_J2 :
    ∀ φ : MulAut (NativeSporadic.Carrier .J2), φ * φ = 1 → φ ≠ 1 →
      InvAutGen (NativeSporadic.Carrier .J2) φ :=
  invAutGen_of_mulEquiv_forall nativeEquivP invAutGen_P_involution

end Classes

end CFSG.Quasithin.F7Two
