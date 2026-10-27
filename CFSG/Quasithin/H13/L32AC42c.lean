module

public import CFSG.Quasithin.Background.A1GaschutzNorm
public import CFSG.Quasithin.Background.F1Basic

public section

namespace CFSG.Quasithin.H13.L32A.C

theorem exists_fixed_mul_of_coprime_index {Y M : Type*} [Group Y] [Group M] [Finite Y]
    [Finite M] (φ : Y →* MulAut M) (hc : ∀ a b : M, a * b = b * a) {e : ℕ}
    (he : ∀ m : M, m ^ e = 1) {X T : Subgroup Y} {U : Subgroup M}
    (hcop : Nat.Coprime e (T.relIndex X)) (hXU : ∀ x ∈ X, ∀ m : M, φ x m * m⁻¹ ∈ U)
    (hT : ∀ m : M, ∃ u ∈ U, ∃ c : M, (∀ t ∈ T, φ t c = c) ∧ m = u * c) :
    ∀ m : M, ∃ u ∈ U, ∃ c : M, (∀ x ∈ X, φ x c = c) ∧ m = u * c := by
  classical
  have : Finite (M ⋊[φ] Y) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  set Wm : Subgroup (M ⋊[φ] Y) := (SemidirectProduct.inl : M →* M ⋊[φ] Y).range with hWm
  set U' : Subgroup (M ⋊[φ] Y) := U.map SemidirectProduct.inl with hU'
  set X' : Subgroup (M ⋊[φ] Y) := X.map SemidirectProduct.inr with hX'
  set T' : Subgroup (M ⋊[φ] Y) := T.map SemidirectProduct.inr with hT'
  have hconj : ∀ (y : Y) (m : M), (SemidirectProduct.inr y : M ⋊[φ] Y) *
      SemidirectProduct.inl m * (SemidirectProduct.inr y)⁻¹ = SemidirectProduct.inl (φ y m) :=
    fun y m => by rw [SemidirectProduct.inl_aut, map_inv]
  have hWn : Wm.Normal := by
    rw [hWm, SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hcop' : Nat.Coprime e (T'.relIndex X') := by
    rwa [hT', hX', Subgroup.relIndex_map_map_of_injective _ _ SemidirectProduct.inr_injective]
  have hG := GaschutzNorm.sup_fixed_eq_of_coprime_index (X := X') (T := T') (W := Wm) (U := U')
    hcop' ?_ ?_ ?_ ?_ ?_ ?_
  rotate_left
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, hc]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, he, map_one]
  · rintro _ ⟨u, -, rfl⟩
    exact ⟨u, rfl⟩
  · intro g _
    rw [Subgroup.normalizer_eq_top_iff.mpr hWn]
    exact Subgroup.mem_top g
  · rintro _ ⟨y, hy, rfl⟩ _ ⟨m, rfl⟩
    refine ⟨φ y m * m⁻¹, hXU y hy m, ?_⟩
    rw [map_mul, map_inv, ← hconj]
  · rintro _ ⟨m, rfl⟩
    obtain ⟨u, hu, c, hcT, rfl⟩ := hT m
    rw [map_mul]
    refine Subgroup.mul_mem_sup ⟨u, hu, rfl⟩
      (Subgroup.mem_inf.mpr ⟨⟨c, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩)
    rintro _ ⟨t, ht, rfl⟩
    calc SemidirectProduct.inr t * SemidirectProduct.inl c =
        SemidirectProduct.inr t * SemidirectProduct.inl c * (SemidirectProduct.inr t)⁻¹ *
          SemidirectProduct.inr t := by group
      _ = SemidirectProduct.inl c * SemidirectProduct.inr t := by rw [hconj, hcT t ht]
  intro m
  have hm : (SemidirectProduct.inl m : M ⋊[φ] Y) ∈ U' ⊔ Wm ⊓ Subgroup.centralizer (X' : Set _) := by
    rw [hG]
    exact ⟨m, rfl⟩
  have hN : Wm ⊓ Subgroup.centralizer (X' : Set (M ⋊[φ] Y)) ≤
      Subgroup.normalizer (U' : Set (M ⋊[φ] Y)) := by
    rintro _ ⟨⟨c, rfl⟩, -⟩
    refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    obtain ⟨u, hu, rfl⟩ := hz
    refine ⟨c * u * c⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    rw [hc c u, mul_inv_cancel_right]
    exact hu
  obtain ⟨a, ⟨u, hu, rfl⟩, b, ⟨⟨c, rfl⟩, hcX⟩, hab⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hN).mp hm
  refine ⟨u, hu, c, fun x hx => ?_, ?_⟩
  · have h1 := Subgroup.mem_centralizer_iff.mp hcX _ ⟨x, hx, rfl⟩
    refine SemidirectProduct.inl_injective (φ := φ) ?_
    rw [← hconj, h1, mul_inv_cancel_right]
  · refine SemidirectProduct.inl_injective (φ := φ) ?_
    rw [hab, map_mul]

end CFSG.Quasithin.H13.L32A.C
