module

public import CFSG.Walter.Ree.Thompson2.BaseGrp.Field
public import CFSG.Walter.Ree.Thompson2.BaseGrp.NComp

public section

namespace CFSG.Walter.Ree.T2.BaseGrp

section

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k}

theorem alpha_ne_zero_of_cube_ne_one {α β γ : k} (h : pp σ α β γ ^ 3 ≠ 1) : α ≠ 0 := by
  rintro rfl
  apply h
  rw [pp_cube, map_zero, zero_mul, pp_zero]

theorem beta_eq_zero_of_J_inv {α β γ : k}
    (h : (ThompsonN.J σ)⁻¹ * pp σ α β γ * ThompsonN.J σ = (pp σ α β γ)⁻¹) : β = 0 := by
  rw [J_conj_pp, pp_inv, pp_eq_iff] at h
  have h2 : (2 : k) * β = 0 := by linear_combination h.2.1
  exact (mul_eq_zero.mp h2).resolve_left two_ne_zero_of_charThree

theorem pp_inv_mul_tT_conj (α γ : k) :
    (pp σ α 0 γ)⁻¹ * ((tT σ)⁻¹ * pp σ α 0 γ * tT σ) = pp σ 0 0 (-α) := by
  rw [tT_conj_pp, pp_inv, pp_mul, pp_eq_iff]
  simp only [map_neg]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination (-(α ^ 2 * σ α)) * ThompsonN.three_eq_zero (K := k)

theorem pp_pow_three_mul (α β γ : k) (i : ℕ) :
    pp σ α β γ ^ (3 * i) = pp σ 0 0 (i * (σ α * α ^ 2)) := by
  rw [pow_mul, pp_cube, pp_center_pow]

theorem three_dvd_of_alpha_pow_eq_zero {x : ThompsonN k σ} (hx : x ∈ ThompsonN.P σ)
    (hα : x.α ≠ 0) {j : ℕ} (hj : (x ^ j).α = 0) : 3 ∣ j := by
  rw [alpha_pow hx] at hj
  exact (CharP.cast_eq_zero_iff k 3 j).mp ((mul_eq_zero.mp hj).resolve_right hα)

variable [Fintype k] {n : ℕ}

theorem eq_one_or_neg_one_of_natCast_mul (hk : Fintype.card k = 3 ^ (2 * n + 1)) {α : k}
    (hα : α ≠ 0) {i : ℕ} (h : (i : k) * (σ α * α ^ 2) = -α) : α = 1 ∨ α = -1 := by
  have h3 := ThompsonN.three_eq_zero (K := k)
  rw [CharP.cast_eq_mod k 3 i] at h
  have hi : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rcases hi with hi | hi | hi <;> rw [hi] at h <;> push_cast at h
  · exact absurd (by linear_combination h) hα
  · exfalso
    have h1 : α * (σ α * α + 1) = 0 := by linear_combination h
    have h2 : σ α * α = -1 :=
      eq_neg_of_add_eq_zero_left ((mul_eq_zero.mp h1).resolve_left hα)
    exact not_isSquare_neg_one hk (h2 ▸ isSquare_sigma_mul hk α)
  · apply sigma_mul_eq_one hk
    have h1 : α * (σ α * α - 1) = 0 := by linear_combination -h + σ α * α ^ 2 * h3
    exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hα)

end

theorem exists_tY_of_nine {k : Type} [Field k] [Fintype k] [CharP k 3] {σ : k ≃+* k} {n : ℕ}
    (hk : Fintype.card k = 3 ^ (2 * n + 1)) {x : ThompsonN k σ} (hx9 : x ^ 9 = 1)
    (hx3 : x ^ 3 ≠ 1) (hT : (tT σ)⁻¹ * x * tT σ ∈ Subgroup.zpowers x)
    (hJ : (ThompsonN.J σ)⁻¹ * x * ThompsonN.J σ = x⁻¹) :
    ∃ d : k, x = tY σ d ∨ x⁻¹ = tY σ d := by
  obtain ⟨α, β, γ, rfl⟩ : ∃ α β γ : k, x = pp σ α β γ :=
    ⟨_, _, _, eq_pp_of_mem_P (mem_P_of_pow_nine hx9)⟩
  have hα : α ≠ 0 := alpha_ne_zero_of_cube_ne_one hx3
  obtain rfl : β = 0 := beta_eq_zero_of_J_inv hJ
  have hmem : pp σ 0 0 (-α) ∈ Subgroup.zpowers (pp σ α 0 γ) := by
    rw [← pp_inv_mul_tT_conj α γ]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers _)) hT
  have hfin : IsOfFinOrder (pp σ α 0 γ) :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨9, by norm_num, hx9⟩
  obtain ⟨j, hj⟩ := (Submonoid.mem_powers_iff _ _).mp (hfin.mem_powers_iff_mem_zpowers.mpr hmem)
  obtain ⟨i, rfl⟩ : 3 ∣ j :=
    three_dvd_of_alpha_pow_eq_zero (pp_mem_P (σ := σ) α 0 γ) hα (by rw [hj]; rfl)
  rw [pp_pow_three_mul, pp_eq_iff] at hj
  rcases eq_one_or_neg_one_of_natCast_mul hk hα hj.2.2 with rfl | rfl
  · exact ⟨γ, Or.inl rfl⟩
  · refine ⟨-γ, Or.inr ?_⟩
    rw [pp_inv, tY, pp_eq_iff]
    refine ⟨by ring, by ring, by ring⟩

end CFSG.Walter.Ree.T2.BaseGrp
