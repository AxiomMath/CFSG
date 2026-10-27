module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11Case5Tensor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.H.Om4

private theorem s16c11_v1_exists_unit_order_three {K : Type} [Field K] [Finite K]
    (hK4 : Nat.card K = 4) : ∃ ω : Kˣ, ω ^ 3 = 1 ∧ ω ≠ 1 := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hcard : Nat.card Kˣ = 3 := by rw [Nat.card_units, hK4]
  rw [hcard] at hω
  refine ⟨ω, ?_, ?_⟩
  · rw [← hω]; exact pow_orderOf_eq_one ω
  · intro h; rw [h] at hω; simp at hω

private theorem s16c11_v1_diag_mul_eq_self {K : Type} [Field K] {v : Fin 2 → K}
    (h0 : v 0 ≠ 1) (h1 : v 1 ≠ 1) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : Matrix.diagonal v * X = X) : X = 0 := by
  ext i j
  have hij : (Matrix.diagonal v * X) i j = X i j := by rw [hX]
  rw [Matrix.diagonal_mul] at hij
  have hvi : v i ≠ 1 := by fin_cases i <;> assumption
  have h2 : (v i - 1) * X i j = 0 := by rw [sub_mul, one_mul, hij, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact absurd h (sub_ne_zero.mpr hvi)
  · exact h

private theorem s16c11_v1_mul_diag_eq_self {K : Type} [Field K] {v : Fin 2 → K}
    (h0 : v 0 ≠ 1) (h1 : v 1 ≠ 1) {X : Matrix (Fin 2) (Fin 2) K}
    (hX : X * Matrix.diagonal v = X) : X = 0 := by
  ext i j
  have hij : (X * Matrix.diagonal v) i j = X i j := by rw [hX]
  rw [Matrix.mul_diagonal] at hij
  have hvj : v j ≠ 1 := by fin_cases j <;> assumption
  have h2 : X i j * (v j - 1) = 0 := by rw [mul_sub, mul_one, hij, sub_self]
  rcases mul_eq_zero.mp h2 with h | h
  · exact h
  · exact absurd h (sub_ne_zero.mpr hvj)

private theorem s16c11_v1_om4_tensor_fpf {K : Type} [Field K] [Finite K]
    (hK4 : Nat.card K = 4) :
    ∃ t₁ ∈ (rho (K := K)).range, ∃ t₂ ∈ (rho (K := K)).range,
      t₁ * t₂ = t₂ * t₁ ∧ t₁ ^ 3 = 1 ∧ t₂ ^ 3 = 1 ∧
      (∀ X : VM K, t₁ X = X → X = 1) ∧ (∀ X : VM K, t₂ X = X → X = 1) ∧
      (rho (K := K)).range ≤ Subgroup.closure {x | x ∈ (rho (K := K)).range ∧
        (x * t₁ = t₁ * x ∨ x * t₂ = t₂ * x)} := by
  obtain ⟨ω, hω3, hωne⟩ := s16c11_v1_exists_unit_order_three (K := K) hK4
  have hω3inv : (ω⁻¹ : Kˣ) ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
  let v : Fin 2 → K := ![(ω : K), ((ω⁻¹ : Kˣ) : K)]
  have hv0 : v 0 = (ω : K) := rfl
  have hv1 : v 1 = ((ω⁻¹ : Kˣ) : K) := rfl
  have hv0ne : v 0 ≠ 1 := by
    rw [hv0]
    exact fun h => hωne (Units.val_eq_one.mp h)
  have hv1ne : v 1 ≠ 1 := by
    rw [hv1]
    exact fun h => (inv_ne_one.mpr hωne) (Units.val_eq_one.mp h)
  have hdet : Matrix.det (Matrix.diagonal v) = 1 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    change (ω : K) * ((ω⁻¹ : Kˣ) : K) = 1
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  let c : Matrix.SpecialLinearGroup (Fin 2) K := ⟨Matrix.diagonal v, hdet⟩
  have hcmat : (c : Matrix (Fin 2) (Fin 2) K) = Matrix.diagonal v := rfl
  have hval : (ω : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hvalinv : ((ω⁻¹ : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hω3inv, Units.val_one]
  have hc3 : c ^ 3 = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one, hcmat,
      Matrix.diagonal_pow]
    have hv3 : v ^ 3 = 1 := by
      funext i
      fin_cases i <;> simp [Pi.pow_apply, v, hval, hvalinv]
    rw [hv3]
    exact Matrix.diagonal_one
  have h1 : ∀ X : VM K, Multiplicative.toAdd (rho (c, 1) X) =
      Matrix.diagonal v * Multiplicative.toAdd X := by
    intro X
    rw [rho_apply, toAdd_lr]
    simp [hcmat]
  have h2 : ∀ X : VM K, Multiplicative.toAdd (rho (1, c) X) =
      Multiplicative.toAdd X * Matrix.diagonal v := by
    intro X
    rw [rho_apply, toAdd_lr]
    simp [hcmat, Matrix.diagonal_transpose]
  have hcomm : rho (c, 1) * rho (1, c) = rho (1, c) * rho (c, 1) := by
    rw [← map_mul, ← map_mul]
    congr 1
    ext <;> simp
  have hcp1 : ((c, 1) : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
    ext <;> simp [hc3]
  have hcp2 : ((1, c) : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) ^ 3 = 1 := by
    ext <;> simp [hc3]
  have hpow1 : rho (c, 1) ^ 3 = 1 := by
    rw [← map_pow, hcp1, map_one]
  have hpow2 : rho (1, c) ^ 3 = 1 := by
    rw [← map_pow, hcp2, map_one]
  have hfix1 : ∀ X : VM K, rho (c, 1) X = X → X = 1 := by
    intro X hX
    have hX' : Matrix.diagonal v * Multiplicative.toAdd X = Multiplicative.toAdd X := by
      have := congrArg Multiplicative.toAdd hX
      rwa [h1 X] at this
    have hzero := s16c11_v1_diag_mul_eq_self hv0ne hv1ne hX'
    exact Multiplicative.toAdd.injective (by rw [hzero]; rfl)
  have hfix2 : ∀ X : VM K, rho (1, c) X = X → X = 1 := by
    intro X hX
    have hX' : Multiplicative.toAdd X * Matrix.diagonal v = Multiplicative.toAdd X := by
      have := congrArg Multiplicative.toAdd hX
      rwa [h2 X] at this
    have hzero := s16c11_v1_mul_diag_eq_self hv0ne hv1ne hX'
    exact Multiplicative.toAdd.injective (by rw [hzero]; rfl)
  have hcl : (rho (K := K)).range ≤
      Subgroup.closure {x | x ∈ (rho (K := K)).range ∧
        (x * rho (c, 1) = rho (c, 1) * x ∨ x * rho (1, c) = rho (1, c) * x)} := by
    rintro y ⟨⟨a, b⟩, rfl⟩
    have hdecomp : rho (a, 1) * rho (1, b) = rho (a, b) := by
      rw [← map_mul]
      congr 1
      ext <;> simp
    rw [← hdecomp]
    apply Subgroup.mul_mem
    · apply Subgroup.subset_closure
      refine ⟨⟨(a, 1), rfl⟩, Or.inr ?_⟩
      rw [← map_mul, ← map_mul]
      congr 1
      ext <;> simp
    · apply Subgroup.subset_closure
      refine ⟨⟨(1, b), rfl⟩, Or.inl ?_⟩
      rw [← map_mul, ← map_mul]
      congr 1
      ext <;> simp
  exact ⟨rho (c, 1), ⟨(c, 1), rfl⟩, rho (1, c), ⟨(1, c), rfl⟩,
    hcomm, hpow1, hpow2, hfix1, hfix2, hcl⟩

theorem s16c11_v1_natOmegaPlus_two_fpf_in {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    (h : NatOmegaPlus H ⊤ ⊥ 4 2) :
    ∃ t₁ ∈ H, ∃ t₂ ∈ H, t₁ * t₂ = t₂ * t₁ ∧ t₁ ^ 3 = 1 ∧ t₂ ^ 3 = 1 ∧
      (∀ w, t₁ w = w → w = 1) ∧ (∀ w, t₂ w = w → w = 1) ∧
      H ≤ Subgroup.closure {x | x ∈ H ∧ (x * t₁ = t₁ * x ∨ x * t₂ = t₂ * x)} := by
  obtain ⟨K, hKf, hKfin, β, hKcard, hL⟩ := s16c11_case5_tensor h
  letI : Field K := hKf
  letI : Finite K := hKfin
  obtain ⟨t₁', ht₁'range, t₂', ht₂'range, hcomm, hpow1, hpow2, hfix1, hfix2, hcl⟩ :=
    s16c11_v1_om4_tensor_fpf (K := K) hKcard
  have hmap1 : t₁' ∈ H.map (MulAut.congr β).toMonoidHom := by rw [hL]; exact ht₁'range
  obtain ⟨t₁, ht₁H, ht₁eq⟩ := Subgroup.mem_map.mp hmap1
  have hmap2 : t₂' ∈ H.map (MulAut.congr β).toMonoidHom := by rw [hL]; exact ht₂'range
  obtain ⟨t₂, ht₂H, ht₂eq⟩ := Subgroup.mem_map.mp hmap2
  have ht₁eq' : (MulAut.congr β) t₁ = t₁' := ht₁eq
  have ht₂eq' : (MulAut.congr β) t₂ = t₂' := ht₂eq
  let S : Set (MulAut W) := {x | x ∈ H ∧ (x * t₁ = t₁ * x ∨ x * t₂ = t₂ * x)}
  let S' : Set (MulAut (VM K)) :=
    {x | x ∈ (rho (K := K)).range ∧ (x * t₁' = t₁' * x ∨ x * t₂' = t₂' * x)}
  have hcl' : (rho (K := K)).range ≤ Subgroup.closure S' := hcl
  have hmemH : ∀ y : MulAut W, (MulAut.congr β) y ∈ (rho (K := K)).range ↔ y ∈ H := by
    intro y
    rw [← hL]
    exact Subgroup.mem_map_iff_mem (MulAut.congr β).injective
  have hiff : ∀ y : MulAut W, (MulAut.congr β) y ∈ S' ↔ y ∈ S := by
    intro y
    constructor
    · rintro ⟨hyH, hy⟩
      refine ⟨(hmemH y).mp hyH, ?_⟩
      rcases hy with h | h
      · left
        apply (MulAut.congr β).injective
        rw [map_mul, map_mul, ht₁eq']
        exact h
      · right
        apply (MulAut.congr β).injective
        rw [map_mul, map_mul, ht₂eq']
        exact h
    · rintro ⟨hyH, hy⟩
      refine ⟨(hmemH y).mpr hyH, ?_⟩
      rcases hy with h | h
      · left
        have hh := congrArg (MulAut.congr β) h
        rw [map_mul, map_mul, ht₁eq'] at hh
        exact hh
      · right
        have hh := congrArg (MulAut.congr β) h
        rw [map_mul, map_mul, ht₂eq'] at hh
        exact hh
  have hS : (MulAut.congr β).toMonoidHom '' S = S' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hiff y).mpr hy
    · intro hx
      refine ⟨(MulAut.congr β).symm x, (hiff _).mp ?_, (MulAut.congr β).apply_symm_apply x⟩
      rwa [MulEquiv.apply_symm_apply]
  have hclosure : (Subgroup.closure S).map (MulAut.congr β).toMonoidHom =
      Subgroup.closure S' := by
    rw [MonoidHom.map_closure, hS]
  refine ⟨t₁, ht₁H, t₂, ht₂H, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (MulAut.congr β).injective
    rw [map_mul, map_mul, ht₁eq', ht₂eq', hcomm]
  · apply (MulAut.congr β).injective
    rw [map_pow, ht₁eq', hpow1, map_one]
  · apply (MulAut.congr β).injective
    rw [map_pow, ht₂eq', hpow2, map_one]
  · intro w hw
    have hβ : β (t₁ w) = t₁' (β w) := by
      have hcongr : ((MulAut.congr β) t₁) (β w) = β (t₁ (β.symm (β w))) := rfl
      have hthis := congrArg (fun f : MulAut (VM K) => f (β w)) ht₁eq'
      rw [hcongr, MulEquiv.symm_apply_apply] at hthis
      exact hthis
    have hw' : t₁' (β w) = β w := by rw [← hβ, hw]
    have hone : β w = 1 := hfix1 (β w) hw'
    exact β.injective (by rw [hone, map_one])
  · intro w hw
    have hβ : β (t₂ w) = t₂' (β w) := by
      have hcongr : ((MulAut.congr β) t₂) (β w) = β (t₂ (β.symm (β w))) := rfl
      have hthis := congrArg (fun f : MulAut (VM K) => f (β w)) ht₂eq'
      rw [hcongr, MulEquiv.symm_apply_apply] at hthis
      exact hthis
    have hw' : t₂' (β w) = β w := by rw [← hβ, hw]
    have hone : β w = 1 := hfix2 (β w) hw'
    exact β.injective (by rw [hone, map_one])
  · intro h hh
    have hmem : (MulAut.congr β) h ∈ H.map (MulAut.congr β).toMonoidHom :=
      Subgroup.mem_map_of_mem _ hh
    have hh' : (MulAut.congr β) h ∈ Subgroup.closure S' := by
      rw [hL] at hmem
      exact hcl' hmem
    rw [← hclosure] at hh'
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hh'
    have hyh : y = h := (MulAut.congr β).injective hyeq
    rw [hyh] at hy
    exact hy

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
