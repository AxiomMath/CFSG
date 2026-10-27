module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralGenerators

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private lemma w183b2_conj_mul_eq_inv {X : Type*} [Group X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  simp only [mul_inv_rev, hb', ha']
  calc a * (a * b) * a = (a * a) * (b * a) := by group
    _ = b * a := by rw [ha, one_mul]

private lemma w183b2_notMem_zpowers_mul {X : Type*} [Group X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a ∉ Subgroup.zpowers (a * b) := by
  intro hmem
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hcomm : a * (a * b) = (a * b) * a := by
    have hcomm' : Commute ((a * b) ^ k) (a * b) :=
      ((Commute.refl (a * b)).zpow_right k).symm
    rw [hk] at hcomm'
    exact hcomm'.eq
  have hsq : (a * b) * (a * b) = 1 := by
    have h1 : a * (a * b) * a⁻¹ = a * b := by
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
    rw [w183b2_conj_mul_eq_inv ha hb] at h1
    exact inv_eq_iff_mul_eq_one.mp h1
  have hsq' : (a * b) ^ (2 : ℤ) = 1 := by
    rw [zpow_two]
    exact hsq
  have hk' : (a * b) ^ k = (a * b) ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2, zpow_add, zpow_mul]
    rw [hsq', one_zpow, mul_one]
  rw [hk'] at hk
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · rw [h0, zpow_zero] at hk
    exact ha1 hk.symm
  · rw [h1, zpow_one] at hk
    exact hb1 (mul_eq_left.mp hk)

theorem w183b2_dihedral_of_involutions {X : Type} [Group X] [Finite X] {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (hab : a ≠ b) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    Nonempty (↥(Subgroup.closure ({a, b} : Set X)) ≃* DihedralGroup (orderOf (a * b))) := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  set H := Subgroup.closure ({a, b} : Set X) with hH
  have haH : a ∈ H := Subgroup.subset_closure (by simp)
  have hbH : b ∈ H := Subgroup.subset_closure (by simp)
  set ρ : H := ⟨a * b, H.mul_mem haH hbH⟩ with hρ
  set σ : H := ⟨a, haH⟩ with hσ
  set τ : H := ⟨b, hbH⟩ with hτ
  have hστ : σ * τ = ρ := by
    apply Subtype.ext
    rfl
  have hgen : (⊤ : Subgroup H) = Subgroup.zpowers ρ ⊔ Subgroup.zpowers σ := by
    refine (eq_top_iff.mpr ?_).symm
    rintro ⟨x, hx⟩ -
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
      · have hy' : y = b := hy
        subst b
        have hb_eq : (⟨y, hbH⟩ : H) = σ⁻¹ * ρ := by
          apply Subtype.ext
          simp only [hσ, hρ, Subgroup.coe_mul, Subgroup.coe_inv]
          rw [ha', ← mul_assoc, ha, one_mul]
        rw [hb_eq]
        exact Subgroup.mul_mem _
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)))
          (Subgroup.mem_sup_left (Subgroup.mem_zpowers ρ))
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => exact Subgroup.inv_mem _ hx
  have hσ2 : σ ^ 2 = 1 := by
    apply Subtype.ext
    simp [hσ, pow_two, ha]
  have hτ2 : τ ^ 2 = 1 := by
    apply Subtype.ext
    simp [hτ, pow_two, hb]
  have hσ1 : σ ≠ 1 := by
    intro h
    apply ha1
    have := congrArg Subtype.val h
    simpa [hσ] using this
  have hτ1 : τ ≠ 1 := by
    intro h
    apply hb1
    have := congrArg Subtype.val h
    simpa [hτ] using this
  have hrel : σ * ρ * σ⁻¹ = ρ⁻¹ := by
    apply Subtype.ext
    simp only [hσ, hρ, Subgroup.coe_mul, Subgroup.coe_inv]
    exact w183b2_conj_mul_eq_inv ha hb
  have hσρ : σ ∉ Subgroup.zpowers ρ := by
    rw [← hστ]
    exact w183b2_notMem_zpowers_mul (by simpa [pow_two] using hσ2)
      (by simpa [pow_two] using hτ2) hσ1 hτ1
  obtain ⟨e⟩ :=
    CFSG.GorensteinWalter.dihedral_of_generators_of_not_mem ρ σ hgen hσ2 hrel hσρ
  have hord : orderOf ρ = orderOf (a * b) := by
    rw [hρ, Subgroup.orderOf_mk]
  rw [hord] at e
  exact ⟨by simpa [hH] using e⟩

end CFSG.LocalAnalysis.WeakClosure81

end
