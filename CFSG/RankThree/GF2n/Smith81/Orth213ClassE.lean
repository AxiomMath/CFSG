module

public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthClass

open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem exists_eichler_of_fix_perp (hQ : (polarBilin Q).Nondegenerate) {o : V ≃ₗ[K] V}
    (ho : o ∈ TauCeti.QuadraticMap.orthogonalGroup Q) {u : V} (hu : Q u = 0) (hu0 : u ≠ 0)
    (hou : o u = u) (hperp : ∀ v, polar Q v u = 0 → ∃ c : K, o v = v + c • u) :
    ∃ w, polar Q u w = 0 ∧ o = eichler Q u w := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : V, polar Q u x₀ = 1 := by
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ hu0
    exact ⟨(polar Q u y)⁻¹ • y, by rw [polar_smul_right_eq, inv_mul_cancel₀ hy]⟩
  have hx₀' : polar Q x₀ u = 1 := by rw [polar_comm]; exact hx₀
  obtain ⟨πl, hπl⟩ : ∃ p : V →ₗ[K] V, ∀ v, p v = v - polar Q v u • x₀ :=
    ⟨LinearMap.id - LinearMap.smulRight (LinearMap.flip (polarBilin Q) u) x₀,
      fun v => by simp [LinearMap.smulRight_apply, LinearMap.flip_apply]⟩
  have hπU : ∀ v, polar Q (πl v) u = 0 := by
    intro v
    rw [hπl, polar_sub_left, polar_smul_left_eq, hx₀', mul_one, sub_self]
  have hπfix : ∀ v, polar Q v u = 0 → πl v = v := by
    intro v hv
    rw [hπl, hv, zero_smul, sub_zero]
  obtain ⟨ψl, hψl⟩ : ∃ f : V →ₗ[K] K, ∀ v, f v = polar Q (o (πl v) - πl v) x₀ :=
    ⟨LinearMap.flip (polarBilin Q) x₀ ∘ₗ ((o : V →ₗ[K] V) ∘ₗ πl - πl),
      fun v => by simp [LinearMap.flip_apply]⟩
  have hψ_key : ∀ v, o (πl v) = πl v + ψl v • u := by
    intro v
    obtain ⟨c, hc⟩ := hperp (πl v) (hπU v)
    have h1 : ψl v = c := by
      rw [hψl, hc, add_sub_cancel_left, polar_smul_left_eq, hx₀, mul_one]
    rw [h1, hc]
  have hψu : ψl u = 0 := by
    rw [hψl, hπfix u (polar_self_eq_zero hu), hou, sub_self, polar_zero_left]
  obtain ⟨w, hw⟩ := (LinearMap.BilinForm.toDual (polarBilin Q) hQ).surjective (-ψl)
  have hwv : ∀ v, polar Q v w = -ψl v := by
    intro v
    have h := congrArg (fun f : Module.Dual K V => f v) hw
    simp only [LinearMap.BilinForm.toDual_def, QuadraticMap.polarBilin_apply_apply,
      LinearMap.neg_apply] at h
    rw [polar_comm]
    exact h
  have hwu : polar Q u w = 0 := by rw [hwv u, hψu, neg_zero]
  have hEU : ∀ v, polar Q v u = 0 → eichler Q u w v = o v := by
    intro v hv
    have hov : o v = v + ψl v • u := by
      have h := hψ_key v
      rwa [hπfix v hv] at h
    rw [eichler_apply hu hwu v, hv, zero_smul, add_zero, mul_zero, add_zero, hwv v, hov,
      neg_smul, sub_neg_eq_add]
  obtain ⟨k, hk⟩ : ∃ k : V ≃ₗ[K] V, k = (eichler Q u w)⁻¹ * o := ⟨_, rfl⟩
  have hkv : ∀ v, k v = (eichler Q u w)⁻¹ (o v) := fun v => by
    rw [hk, LinearEquiv.mul_apply]
  have hko : k ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hk]
    exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
      ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem (eichler_mem_orthogonalGroup Q u w)) ho
  have hk_map : ∀ v, Q (k v) = Q v := fun v => map_of_mem hko v
  have hk_polar : ∀ x y, polar Q (k x) (k y) = polar Q x y := fun x y => polar_map_of_mem hko x y
  have hkU : ∀ v, polar Q v u = 0 → k v = v := by
    intro v hv
    rw [hkv, ← hEU v hv, LinearEquiv.inv_apply_apply']
  have hkx₀ : k x₀ = x₀ := by
    have hd_U : ∀ v, polar Q (k x₀ - x₀) (πl v) = 0 := by
      intro v
      have h1 := hk_polar x₀ (πl v)
      rw [hkU (πl v) (hπU v)] at h1
      rw [polar_sub_left, h1, sub_self]
    have hd_form : ∀ v, polar Q (k x₀ - x₀) v = polar Q v u * polar Q (k x₀ - x₀) x₀ := by
      intro v
      have hv : v = polar Q v u • x₀ + πl v := by
        rw [hπl]
        abel
      rw [congrArg (polar Q (k x₀ - x₀)) hv, polar_add_right, polar_smul_right_eq, hd_U v,
        add_zero, mul_comm]
    have hz : k x₀ - x₀ - polar Q (k x₀ - x₀) x₀ • u = 0 := by
      apply eq_zero_of_polar_eq_zero hQ
      intro v
      rw [polar_sub_left, polar_smul_left_eq, hd_form v, polar_comm Q u v]
      ring
    obtain ⟨a, ha⟩ : ∃ a : K, k x₀ = a • u + x₀ :=
      ⟨polar Q (k x₀ - x₀) x₀, sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)⟩
    have hQa := hk_map x₀
    rw [ha, QuadraticMap.map_add Q (a • u) x₀, map_smul_eq_sq, hu, polar_smul_left_eq,
      hx₀] at hQa
    have ha0 : a = 0 := by linear_combination hQa
    rw [ha, ha0, zero_smul, zero_add]
  have hkfix : ∀ v, k v = v := by
    intro v
    have hv : v = polar Q v u • x₀ + πl v := by
      rw [hπl]
      abel
    calc k v = k (polar Q v u • x₀ + πl v) := congrArg k hv
      _ = polar Q v u • k x₀ + k (πl v) := by rw [map_add, map_smul]
      _ = polar Q v u • x₀ + πl v := by rw [hkx₀, hkU (πl v) (hπU v)]
      _ = v := hv.symm
  refine ⟨w, hwu, LinearEquiv.ext fun v => ?_⟩
  have h := hkfix v
  rw [hkv] at h
  calc o v = eichler Q u w ((eichler Q u w)⁻¹ (o v)) := (LinearEquiv.apply_inv_apply' _ _).symm
    _ = eichler Q u w v := by rw [h]

end CFSG.RankThree.GF2n.Smith81.OrthClass
