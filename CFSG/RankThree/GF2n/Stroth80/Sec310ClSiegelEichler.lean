module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs
public import CFSG.ClassicalGroups.Orthogonal.Eichler

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

open CFSG.ClassicalGroups.Orthogonal QuadraticMap

section Siegel

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem orthSubgroup_eq_orthogonalGroup (Qf : QuadraticForm K V) :
    orthSubgroup Qf = TauCeti.QuadraticMap.orthogonalGroup Qf :=
  Subgroup.ext fun g => by
    rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    exact Iff.rfl

private theorem mem_pointRad_iff_siegel {F : LinearMap.BilinForm K V} {e : V}
    {g : V ≃ₗ[K] V} :
    g ∈ pointRad F e ↔ IsIsom F g ∧ g e = e ∧ ∀ v, F v e = 0 → ∃ c : K, g v = v + c • e :=
  Iff.rfl

theorem eichler_mem_pointRad {Qf : QuadraticForm K V} {u w : V} (hu : Qf u = 0)
    (hw : QuadraticMap.polar Qf u w = 0) : eichler Qf u w ∈ pointRad Qf.polarBilin u := by
  refine mem_pointRad_iff_siegel.mpr ⟨fun x y => ?_, eichler_apply_self u w, fun v hv => ?_⟩
  · simp only [QuadraticMap.polarBilin_apply_apply]
    exact polar_map_of_mem (eichler_mem_orthogonalGroup Qf u w) x y
  · rw [QuadraticMap.polarBilin_apply_apply] at hv
    refine ⟨-QuadraticMap.polar Qf v w, ?_⟩
    rw [eichler_apply hu hw v, hv]
    module

theorem mem_elementaryGroup_of_mem_pointRad [FiniteDimensional K V] {Qf : QuadraticForm K V}
    (hQ : Qf.polarBilin.Nondegenerate) {e : V} (he : Qf e = 0) (he0 : e ≠ 0)
    {g : V ≃ₗ[K] V} (hg : g ∈ orthSubgroup Qf) (hgr : g ∈ pointRad Qf.polarBilin e) :
    g ∈ elementaryGroup Qf := by
  obtain ⟨-, hge, hgc⟩ := mem_pointRad_iff_siegel.mp hgr
  have hgc' : ∀ v, polar Qf v e = 0 → ∃ c : K, g v = v + c • e := fun v hv =>
    hgc v (by rw [QuadraticMap.polarBilin_apply_apply]; exact hv)
  have hgo : g ∈ TauCeti.QuadraticMap.orthogonalGroup Qf := by
    rw [← orthSubgroup_eq_orthogonalGroup]
    exact hg
  obtain ⟨x₀, hx₀⟩ : ∃ x₀ : V, polar Qf e x₀ = 1 := by
    obtain ⟨y, hy⟩ := exists_polar_ne_zero hQ he0
    exact ⟨(polar Qf e y)⁻¹ • y, by rw [polar_smul_right_eq, inv_mul_cancel₀ hy]⟩
  have hx₀' : polar Qf x₀ e = 1 := by
    rw [polar_comm]
    exact hx₀
  obtain ⟨πl, hπl⟩ : ∃ p : V →ₗ[K] V, ∀ v, p v = v - polar Qf v e • x₀ :=
    ⟨LinearMap.id - LinearMap.smulRight (LinearMap.flip Qf.polarBilin e) x₀,
      fun v => by simp [LinearMap.smulRight_apply, LinearMap.flip_apply]⟩
  have hπU : ∀ v, polar Qf (πl v) e = 0 := by
    intro v
    rw [hπl, polar_sub_left, polar_smul_left_eq, hx₀', mul_one, sub_self]
  have hπfix : ∀ u, polar Qf u e = 0 → πl u = u := by
    intro u hu
    rw [hπl, hu, zero_smul, sub_zero]
  obtain ⟨ψl, hψl⟩ : ∃ f : V →ₗ[K] K, ∀ v, f v = polar Qf (g (πl v) - πl v) x₀ :=
    ⟨LinearMap.flip Qf.polarBilin x₀ ∘ₗ ((g : V →ₗ[K] V) ∘ₗ πl - πl),
      fun v => by simp [LinearMap.flip_apply]⟩
  have hψ_key : ∀ v, g (πl v) = πl v + ψl v • e := by
    intro v
    obtain ⟨c, hc⟩ := hgc' (πl v) (hπU v)
    have h1 : ψl v = c := by
      rw [hψl, hc, add_sub_cancel_left, polar_smul_left_eq, hx₀, mul_one]
    rw [h1, hc]
  have hψe : ψl e = 0 := by
    rw [hψl, hπfix e (polar_self_eq_zero he), hge, sub_self, polar_zero_left]
  obtain ⟨w, hw⟩ := (LinearMap.BilinForm.toDual Qf.polarBilin hQ).surjective (-ψl)
  have hwv : ∀ v, polar Qf v w = -ψl v := by
    intro v
    have h := congrArg (fun f : Module.Dual K V => f v) hw
    simp only [LinearMap.BilinForm.toDual_def, QuadraticMap.polarBilin_apply_apply,
      LinearMap.neg_apply] at h
    rw [polar_comm]
    exact h
  have hwe : polar Qf e w = 0 := by
    rw [hwv e, hψe, neg_zero]
  have hEU : ∀ u, polar Qf u e = 0 → eichler Qf e w u = g u := by
    intro u hu
    have hgu : g u = u + ψl u • e := by
      have h := hψ_key u
      rwa [hπfix u hu] at h
    rw [eichler_apply he hwe u, hu, zero_smul, add_zero, mul_zero, add_zero, hwv u, hgu,
      neg_smul, sub_neg_eq_add]
  obtain ⟨k, hk⟩ : ∃ k : V ≃ₗ[K] V, k = (eichler Qf e w)⁻¹ * g := ⟨_, rfl⟩
  have hkv : ∀ v, k v = (eichler Qf e w)⁻¹ (g v) := fun v => by
    rw [hk, LinearEquiv.mul_apply]
  have hko : k ∈ TauCeti.QuadraticMap.orthogonalGroup Qf := by
    rw [hk]
    exact (TauCeti.QuadraticMap.orthogonalGroup Qf).mul_mem
      ((TauCeti.QuadraticMap.orthogonalGroup Qf).inv_mem
        (eichler_mem_orthogonalGroup Qf e w)) hgo
  have hk_map : ∀ v, Qf (k v) = Qf v := fun v =>
    TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hko v
  have hk_polar : ∀ x y, polar Qf (k x) (k y) = polar Qf x y := fun x y =>
    TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hko x y
  have hkU : ∀ u, polar Qf u e = 0 → k u = u := by
    intro u hu
    rw [hkv, ← hEU u hu, LinearEquiv.inv_apply_apply']
  have hkx₀ : k x₀ = x₀ := by
    have hd_U : ∀ v, polar Qf (k x₀ - x₀) (πl v) = 0 := by
      intro v
      have h1 := hk_polar x₀ (πl v)
      rw [hkU (πl v) (hπU v)] at h1
      rw [polar_sub_left, h1, sub_self]
    have hd_form : ∀ v, polar Qf (k x₀ - x₀) v = polar Qf v e * polar Qf (k x₀ - x₀) x₀ := by
      intro v
      have hv : v = polar Qf v e • x₀ + πl v := by
        rw [hπl]
        abel
      rw [congrArg (polar Qf (k x₀ - x₀)) hv, polar_add_right, polar_smul_right_eq, hd_U v,
        add_zero]
    have hz : k x₀ - x₀ - polar Qf (k x₀ - x₀) x₀ • e = 0 := by
      apply eq_zero_of_polar_eq_zero hQ
      intro v
      rw [polar_sub_left, polar_smul_left_eq, hd_form v, polar_comm Qf e v]
      ring
    obtain ⟨a, ha⟩ : ∃ a : K, k x₀ = a • e + x₀ :=
      ⟨polar Qf (k x₀ - x₀) x₀, sub_eq_iff_eq_add.mp (sub_eq_zero.mp hz)⟩
    have hQa := hk_map x₀
    rw [ha, QuadraticMap.map_add Qf (a • e) x₀, map_smul_eq_sq, he, polar_smul_left_eq,
      hx₀] at hQa
    have ha0 : a = 0 := by linear_combination hQa
    rw [ha, ha0, zero_smul, zero_add]
  have hkfix : ∀ v, k v = v := by
    intro v
    have hv : v = polar Qf v e • x₀ + πl v := by
      rw [hπl]
      abel
    calc k v = k (polar Qf v e • x₀ + πl v) := congrArg k hv
      _ = polar Qf v e • k x₀ + k (πl v) := by rw [map_add, map_smul]
      _ = polar Qf v e • x₀ + πl v := by rw [hkx₀, hkU (πl v) (hπU v)]
      _ = v := hv.symm
  have hgE : ∀ v, g v = eichler Qf e w v := by
    intro v
    have h := hkfix v
    rw [hkv] at h
    calc g v = eichler Qf e w ((eichler Qf e w)⁻¹ (g v)) :=
          (LinearEquiv.apply_inv_apply' _ _).symm
      _ = eichler Qf e w v := by rw [h]
  rw [LinearEquiv.ext hgE]
  exact eichler_mem_elementaryGroup Qf e w

theorem closure_siegel_eq_elementaryGroup [FiniteDimensional K V] {Qf : QuadraticForm K V}
    (hQ : Qf.polarBilin.Nondegenerate) :
    Subgroup.closure (⋃ e ∈ {e : V | e ≠ 0 ∧ Qf e = 0},
      (orthSubgroup Qf : Set (V ≃ₗ[K] V)) ∩ pointRad Qf.polarBilin e) = elementaryGroup Qf := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨e, ⟨he0, he⟩, hge⟩ := Set.mem_iUnion₂.mp hg
    exact mem_elementaryGroup_of_mem_pointRad hQ he he0 hge.1 hge.2
  · rw [elementaryGroup, Subgroup.closure_le]
    rintro _ ⟨u, w, hu, hw, rfl⟩
    by_cases h0 : u = 0
    · subst h0
      rw [eichler_zero_left]
      exact Subgroup.one_mem _
    · have hmem : eichler Qf u w ∈ (orthSubgroup Qf : Set (V ≃ₗ[K] V)) ∩
          pointRad Qf.polarBilin u :=
        ⟨by rw [orthSubgroup_eq_orthogonalGroup]; exact eichler_mem_orthogonalGroup Qf u w,
          eichler_mem_pointRad hu hw⟩
      exact Subgroup.subset_closure (Set.mem_iUnion₂.mpr ⟨u, ⟨h0, hu⟩, hmem⟩)

end Siegel

end CFSG.RankThree.GF2n.Stroth80.Classify
