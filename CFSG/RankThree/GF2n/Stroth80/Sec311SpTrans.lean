module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem form_add_smul_self {F : LinearMap.BilinForm K V} (halt : F.IsAlt) (v w : V) (t : K) :
    F (v + t • w) w = F v w := by
  rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    halt.self_eq_zero, mul_zero, add_zero]

@[expose] def symTransvection {F : LinearMap.BilinForm K V} (halt : F.IsAlt) (w : V) (c : K) :
    V ≃ₗ[K] V where
  toFun v := v + (c * F v w) • w
  invFun v := v + (-c * F v w) • w
  map_add' u v := by
    simp only [map_add, LinearMap.add_apply]
    module
  map_smul' a v := by
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply]
    module
  left_inv v := by
    simp only [form_add_smul_self halt]
    module
  right_inv v := by
    simp only [form_add_smul_self halt]
    module

theorem symTransvection_apply {F : LinearMap.BilinForm K V} (halt : F.IsAlt) (w : V) (c : K)
    (v : V) : symTransvection halt w c v = v + (c * F v w) • w :=
  rfl

theorem symTransvection_mem {F : LinearMap.BilinForm K V} (halt : F.IsAlt) (w : V) (c : K) :
    symTransvection halt w c ∈ sympSubgroup F := by
  show IsIsom F (symTransvection halt w c)
  intro x y
  rw [symTransvection_apply, symTransvection_apply]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    halt.self_eq_zero, mul_zero, add_zero]
  rw [← halt.neg_eq y w]
  ring

theorem exists_symp_apply_of_form_ne_zero {F : LinearMap.BilinForm K V} (halt : F.IsAlt)
    {x y : V} (hxy : F x y ≠ 0) : ∃ g ∈ sympSubgroup F, g x = y := by
  refine ⟨symTransvection halt (x - y) (F x y)⁻¹, symTransvection_mem halt _ _, ?_⟩
  have h1 : F x (x - y) = -F x y := by
    rw [map_sub, halt.self_eq_zero x, zero_sub]
  rw [symTransvection_apply, h1, mul_neg, inv_mul_cancel₀ hxy]
  module

theorem exists_form_pair {F : LinearMap.BilinForm K V} (hnd : F.Nondegenerate) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) : ∃ z : V, F x z ≠ 0 ∧ F y z ≠ 0 := by
  obtain ⟨a, ha⟩ : ∃ a : V, F x a ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (hnd.1 x h)
  obtain ⟨b, hb⟩ : ∃ b : V, F y b ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (hnd.1 y h)
  by_cases h1 : F y a = 0
  · by_cases h2 : F x b = 0
    · refine ⟨a + b, ?_, ?_⟩
      · rw [map_add, h2, add_zero]
        exact ha
      · rw [map_add, h1, zero_add]
        exact hb
    · exact ⟨b, h2, hb⟩
  · exact ⟨a, ha, h1⟩

theorem exists_symp_apply_eq {F : LinearMap.BilinForm K V} (hnd : F.Nondegenerate)
    (halt : F.IsAlt) {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    ∃ g ∈ sympSubgroup F, g x = y := by
  by_cases hxy : F x y = 0
  · obtain ⟨z, hxz, hyz⟩ := exists_form_pair hnd hx hy
    obtain ⟨g₁, hg₁, hg₁x⟩ := exists_symp_apply_of_form_ne_zero halt hxz
    have hzy : F z y ≠ 0 := by
      rw [← halt.neg_eq y z]
      exact neg_ne_zero.mpr hyz
    obtain ⟨g₂, hg₂, hg₂z⟩ := exists_symp_apply_of_form_ne_zero halt hzy
    refine ⟨g₂ * g₁, (sympSubgroup F).mul_mem hg₂ hg₁, ?_⟩
    rw [LinearEquiv.mul_apply, hg₁x, hg₂z]
  · exact exists_symp_apply_of_form_ne_zero halt hxy

end CFSG.RankThree.GF2n.Stroth80.Classify
