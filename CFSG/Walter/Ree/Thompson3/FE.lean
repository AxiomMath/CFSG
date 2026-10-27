module

public import CFSG.Walter.Ree.Thompson3.BaseFacts
public import CFSG.Walter.Ree.Thompson3.Thm81
public import CFSG.Walter.Ree.Thompson3.Centralizer
public import CFSG.Walter.Ree.Thompson2.Eq69

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3]

theorem pp_0x1_eq (σ : k ≃+* k) (x : k) : pp σ 0 x 1 = pp σ 0 (-1) 1 * pp σ 0 (x + 1) 0 := by
  simp only [pp]
  rw [ThompsonN.mul_P]
  ext
  · rfl
  · simp
  · simp
  · simp

theorem pp_P0_mul (σ : k ≃+* k) {x : k} (hx : x + 1 ≠ 0) :
    pp σ 0 (-1) 1 * pp σ 0 (-(x + 1)⁻¹) 0 = pp σ 0 ((1 - x) / (1 + x)) 1 := by
  simp only [pp]
  rw [ThompsonN.mul_P]
  have hx' : 1 + x ≠ 0 := by rwa [add_comm]
  have h3 := ThompsonN.three_eq_zero (K := k)
  ext
  · rfl
  · simp
  · simp only [map_zero, mul_zero, add_zero, sub_zero]
    field_simp
    linear_combination (-(1 + x)) * h3
  · simp

theorem pp_fe2_a (σ : k ≃+* k) (x : k) : pp σ 0 (x - 1) 0 * (pp σ 0 (-1) 1)⁻¹ =
    ThompsonN.torus σ (-1) * pp σ 0 x 1 * (ThompsonN.torus σ (-1))⁻¹ := by
  simp only [pp]
  rw [ThompsonN.inv_P, ThompsonN.mul_P, torus_conj_inv]
  ext
  · rfl
  · simp
  · simp
  · simp

theorem pp_fe2_b (σ : k ≃+* k) {x : k} (hx : x - 1 ≠ 0) :
    pp σ 0 (-(x - 1)⁻¹) 0 * (pp σ 0 (-1) 1)⁻¹ =
      ThompsonN.torus σ (-1) * pp σ 0 ((x + 1) / (x - 1)) 1 * (ThompsonN.torus σ (-1))⁻¹ := by
  simp only [pp]
  rw [ThompsonN.inv_P, ThompsonN.mul_P, torus_conj_inv]
  have h3 := ThompsonN.three_eq_zero (K := k)
  ext
  · rfl
  · simp
  · simp only [map_zero, zero_mul, add_zero, sub_zero, Units.val_neg, Units.val_one, inv_neg,
      inv_one, map_neg, map_one, neg_neg]
    field_simp
    linear_combination (-1 : k) * h3
  · simp

theorem J_conj_tY_sq_inv (σ : k ≃+* k) (d : k) :
    ThompsonN.torus σ (-1) * (tY σ d ^ 2)⁻¹ * (ThompsonN.torus σ (-1))⁻¹ = tY σ d ^ 2 := by
  rw [← tY_pow_seven, tY_pow_seven_eq, tY_sq]
  simp only [pp]
  rw [torus_conj_inv]
  ext
  · rfl
  · simp
  · simp
  · simp

namespace RType

variable [Finite k] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem fe1
    {S : k → k × k × k} (hS : IsS R S) {a : ℕ} (ha : Even a)
    (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) {x : k} (hx : x + 1 ≠ 0) :
    ppv σ (S x) = ThompsonN.torus σ (Units.mk0 (x + 1) hx ^ a) *
      ppv σ (S ((1 - x) / (1 + x))) * (ThompsonN.torus σ (Units.mk0 (x + 1) hx ^ a))⁻¹ *
        pp σ 0 (-(x + 1)⁻¹) 0 := by
  set y := -(x + 1)⁻¹ with hydef
  have hy : y ≠ 0 := neg_ne_zero.2 (inv_ne_zero hx)
  set x' := (1 - x) / (1 + x) with hx'def
  set ω := Units.mk0 (x + 1) hx ^ a with hωdef
  have h69 := R.eq69 a ha haσ y hy
  have hω : (Units.mk0 y hy)⁻¹ ^ a = ω := by
    ext
    simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, hωdef, hydef,
      inv_neg, inv_inv]
    exact ha.neg_pow _
  have hyy : -y⁻¹ = x + 1 := by rw [hydef, inv_neg, inv_inv, neg_neg]
  rw [hω, hyy] at h69
  have hP0 := R.K_P0_K
  obtain ⟨ν, hν⟩ := hS x
  obtain ⟨ν', hν'⟩ := hS x'
  have hKK := R.K_mul_K
  have hKω := R.K_mul_torus ω
  simp only [map_inv] at hKω
  have hωK : (R.ι (ThompsonN.torus σ ω))⁻¹ * R.K = R.K * R.ι (ThompsonN.torus σ ω) := hKω.symm
  have hpres : R.ι ν * R.K * R.ι (ppv σ (S x)) =
      R.ι (tY σ d ^ 2 * ThompsonN.J σ * ν' * ThompsonN.torus σ ω) * R.K *
        R.ι (ThompsonN.torus σ ω * ppv σ (S x') * (ThompsonN.torus σ ω)⁻¹ * pp σ 0 y 0) := by
    rw [← hν, pp_0x1_eq σ x, map_mul]
    calc R.K * (R.ι (pp σ 0 (-1) 1) * R.ι (pp σ 0 (x + 1) 0)) * R.K =
        (R.K * R.ι (pp σ 0 (-1) 1) * R.K) * (R.K * R.ι (pp σ 0 (x + 1) 0) * R.K) := by
          rw [show (R.K * R.ι (pp σ 0 (-1) 1) * R.K) * (R.K * R.ι (pp σ 0 (x + 1) 0) * R.K) =
            R.K * R.ι (pp σ 0 (-1) 1) * (R.K * R.K) * R.ι (pp σ 0 (x + 1) 0) * R.K by group,
            hKK]
          group
      _ = R.ι (tY σ d ^ 2 * ThompsonN.J σ) * R.K * R.ι (pp σ 0 (-1) 1 * pp σ 0 y 0) *
          R.ι (ThompsonN.torus σ ω) * R.K * R.ι (pp σ 0 y 0) := by
          rw [hP0, ← h69, map_mul R.ι (pp σ 0 (-1) 1)]; group
      _ = R.ι (tY σ d ^ 2 * ThompsonN.J σ) * (R.K * R.ι (pp σ 0 x' 1) * R.K) *
          (R.K * R.ι (ThompsonN.torus σ ω) * R.K) * R.ι (pp σ 0 y 0) := by
          rw [pp_P0_mul σ hx, ← hx'def]
          rw [show R.ι (tY σ d ^ 2 * ThompsonN.J σ) * (R.K * R.ι (pp σ 0 x' 1) * R.K) *
            (R.K * R.ι (ThompsonN.torus σ ω) * R.K) * R.ι (pp σ 0 y 0) =
              R.ι (tY σ d ^ 2 * ThompsonN.J σ) * R.K * R.ι (pp σ 0 x' 1) * (R.K * R.K) *
                R.ι (ThompsonN.torus σ ω) * R.K * R.ι (pp σ 0 y 0) by group, hKK]
          group
      _ = R.ι (tY σ d ^ 2 * ThompsonN.J σ) * (R.ι ν' * R.K * R.ι (ppv σ (S x'))) *
          ((R.ι (ThompsonN.torus σ ω))⁻¹ * R.K * R.K) * R.ι (pp σ 0 y 0) := by
          rw [← hν', hKω]
      _ = R.ι (tY σ d ^ 2 * ThompsonN.J σ) * R.ι ν' * R.K * (R.ι (ThompsonN.torus σ ω))⁻¹ *
          (R.ι (ThompsonN.torus σ ω) * R.ι (ppv σ (S x')) * (R.ι (ThompsonN.torus σ ω))⁻¹) *
            R.ι (pp σ 0 y 0) := by
          rw [mul_assoc _ R.K R.K, hKK, mul_one]; group
      _ = R.ι (tY σ d ^ 2 * ThompsonN.J σ) * R.ι ν' * (R.K * (R.ι (ThompsonN.torus σ ω))⁻¹) *
          (R.ι (ThompsonN.torus σ ω) * R.ι (ppv σ (S x')) * (R.ι (ThompsonN.torus σ ω))⁻¹) *
            R.ι (pp σ 0 y 0) := by group
      _ = _ := by
          have hKωi : R.K * (R.ι (ThompsonN.torus σ ω))⁻¹ = R.ι (ThompsonN.torus σ ω) * R.K := by
            calc R.K * (R.ι (ThompsonN.torus σ ω))⁻¹ =
                R.ι (ThompsonN.torus σ ω) * ((R.ι (ThompsonN.torus σ ω))⁻¹ * R.K) *
                  (R.ι (ThompsonN.torus σ ω))⁻¹ := by group
              _ = _ := by rw [hωK]; group
          rw [hKωi]
          simp only [map_mul, map_inv]
          group
  have hm : ThompsonN.torus σ ω * ppv σ (S x') * (ThompsonN.torus σ ω)⁻¹ * pp σ 0 y 0 ∈
      ThompsonN.P σ := by
    refine (ThompsonN.P σ).mul_mem ?_ rfl
    exact (ThompsonN.P_normal (σ := σ)).conj_mem _ (ppv_mem_P σ _) _
  rw [← ppv_coords hm] at hpres
  have := (R.pres_unique hpres).2
  rw [this, ppv_coords hm]

theorem fe1_coords
    {S : k → k × k × k} (hS : IsS R S) {a : ℕ} (ha : Even a)
    (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) {x : k} (hx : x + 1 ≠ 0) :
    S x = ((S ((1 - x) / (1 + x))).1 * ((x + 1) ^ a)⁻¹,
      (S ((1 - x) / (1 + x))).2.1 * ((x + 1) ^ 2)⁻¹ - (x + 1)⁻¹,
      (S ((1 - x) / (1 + x))).2.2 * ((x + 1) ^ (a + 2))⁻¹) := by
  have e := congrArg coords (R.fe1 hS ha haσ hx)
  rw [coords_ppv] at e
  rw [e]
  have h2 : σ (x + 1) ^ a * (x + 1) ^ a = (x + 1) ^ 2 := by rw [← mul_pow]; exact haσ (x + 1)
  have hxa : (x + 1) ^ a ≠ 0 := pow_ne_zero _ hx
  have hsxa : σ (x + 1) ^ a ≠ 0 := pow_ne_zero _ ((map_ne_zero σ).mpr hx)
  generalize S ((1 - x) / (1 + x)) = v
  obtain ⟨X, Y, Z⟩ := v
  simp only [ppv, pp]
  rw [torus_conj_inv, ThompsonN.mul_P]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp [coords]
  · simp only [coords, Units.val_pow_eq_pow_val, Units.val_mk0, map_inv₀, map_pow, map_zero,
      mul_zero, zero_mul, add_zero, sub_zero]
    rw [show (((x + 1) ^ a)⁻¹ * (σ (x + 1) ^ a)⁻¹) = ((x + 1) ^ 2)⁻¹ by
      rw [← mul_inv, mul_comm, h2]]
    ring
  · simp only [coords, Units.val_pow_eq_pow_val, Units.val_mk0, map_inv₀, map_pow, map_zero,
      mul_zero, zero_mul, add_zero, sub_zero]
    rw [show (((x + 1) ^ a)⁻¹ ^ 2 * (σ (x + 1) ^ a)⁻¹) = ((x + 1) ^ (a + 2))⁻¹ by
      rw [pow_add, ← h2]; field_simp]
    ring

theorem fe2
    {S : k → k × k × k} (hS : IsS R S) {a : ℕ} (ha : Even a)
    (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) {x : k} (hx : x - 1 ≠ 0) :
    ppv σ (S x) = (ThompsonN.J σ)⁻¹ * ppv σ (S ((x + 1) / (x - 1))) * ThompsonN.J σ *
      tY σ d ^ 2 := by
  set x'' := (x + 1) / (x - 1) with hx''def
  have hp := R.K_pp0_K ha haσ R.eq69 (x - 1) hx
  have hP0 : R.K * R.ι (pp σ 0 (-1) 1) * R.K =
      R.ι (tY σ d ^ 2 * ThompsonN.torus σ (-1)) * R.K * R.ι (pp σ 0 (-1) 1) := R.K_P0_K
  have hp' := R.K_inv_K hP0
  obtain ⟨ν'', hν''⟩ := hS x''
  have hX := R.K_conj_torus (-1) hν''
  rw [← pp_fe2_b σ hx] at hX
  have hc := R.cocycle hp hp' hX
  obtain ⟨ν, hν⟩ := hS x
  have hx' := R.K_conj_torus (-1) hν
  rw [← pp_fe2_a σ x] at hx'
  have hm1 : (ThompsonN.torus σ (-1))⁻¹ * ppv σ (S x) * ThompsonN.torus σ (-1) ∈
      ThompsonN.P σ := by
    simpa using (ThompsonN.P_normal (σ := σ)).conj_mem _ (ppv_mem_P σ (S x))
      (ThompsonN.torus σ (-1))⁻¹
  have hm2 : ThompsonN.torus σ (-1) * ((ThompsonN.torus σ (-1))⁻¹ * ppv σ (S x'') *
      ThompsonN.torus σ (-1)) * (ThompsonN.torus σ (-1))⁻¹ * (tY σ d ^ 2)⁻¹ ∈ ThompsonN.P σ := by
    refine (ThompsonN.P σ).mul_mem ?_ ((ThompsonN.P σ).inv_mem ((ThompsonN.P σ).pow_mem rfl 2))
    rw [show ThompsonN.torus σ (-1) * ((ThompsonN.torus σ (-1))⁻¹ * ppv σ (S x'') *
      ThompsonN.torus σ (-1)) * (ThompsonN.torus σ (-1))⁻¹ = ppv σ (S x'') by group]
    exact ppv_mem_P σ (S x'')
  have e := (R.pres_unique_P hm1 hm2 (hx'.symm.trans hc)).2
  have hJ : ThompsonN.J σ = ThompsonN.torus σ (-1) := rfl
  have hJi : (ThompsonN.torus σ (-1))⁻¹ = ThompsonN.torus σ (-1) := by
    rw [← map_inv, inv_neg, inv_one]
  have e' : (ThompsonN.torus σ (-1))⁻¹ * ppv σ (S x) * ThompsonN.torus σ (-1) =
      ppv σ (S x'') * (tY σ d ^ 2)⁻¹ := by rw [e]; group
  have hs : ppv σ (S x) = (ThompsonN.torus σ (-1) * ppv σ (S x'') * (ThompsonN.torus σ (-1))⁻¹) *
      (ThompsonN.torus σ (-1) * (tY σ d ^ 2)⁻¹ * (ThompsonN.torus σ (-1))⁻¹) := by
    calc ppv σ (S x) = ThompsonN.torus σ (-1) * ((ThompsonN.torus σ (-1))⁻¹ * ppv σ (S x) *
          ThompsonN.torus σ (-1)) * (ThompsonN.torus σ (-1))⁻¹ := by group
      _ = _ := by rw [e']; group
  rw [hs, J_conj_tY_sq_inv, hJ, hJi]

theorem fe2_coords
    {S : k → k × k × k} (hS : IsS R S) {a : ℕ} (ha : Even a)
    (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) {x : k} (hx : x - 1 ≠ 0) :
    S x = (-(S ((x + 1) / (x - 1))).1 - 1,
      (S ((x + 1) / (x - 1))).2.1 + (S ((x + 1) / (x - 1))).1 - σ (S ((x + 1) / (x - 1))).1,
      1 - d - (S ((x + 1) / (x - 1))).2.2 - (S ((x + 1) / (x - 1))).2.1 -
        σ (S ((x + 1) / (x - 1))).1 - (S ((x + 1) / (x - 1))).1 +
          (S ((x + 1) / (x - 1))).1 ^ 2) := by
  have e := congrArg coords (R.fe2 hS ha haσ hx)
  rw [coords_ppv] at e
  rw [e]
  generalize S ((x + 1) / (x - 1)) = v
  obtain ⟨X, Y, Z⟩ := v
  simp only [ppv, pp]
  rw [ThompsonN.J_conj, tY_sq, pp, ThompsonN.mul_P]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · simp only [coords]; ring
  · simp only [coords, map_neg, map_one]; ring
  · simp only [coords, map_neg, map_one]; ring

theorem s_neg_one
    {S : k → k × k × k} (hS : IsS R S) : S (-1) = (0, -1, 1) := by
  obtain ⟨ν, hν⟩ := hS (-1)
  have h := R.K_P0_K
  rw [hν] at h
  have := congrArg coords (R.pres_unique_P (ppv_mem_P σ _) (ppv_mem_P σ (0, -1, 1)) h).2
  rwa [coords_ppv, coords_ppv] at this

theorem s_zero
    {S : k → k × k × k} (hS : IsS R S) {a : ℕ} (ha : Even a)
    (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) : S 0 = (-1, -1, 1 - d) := by
  have h3 := ThompsonN.three_eq_zero (K := k)
  have hx : (-1 : k) - 1 ≠ 0 := by
    intro h; exact one_ne_zero (by linear_combination h + h3)
  have e := R.fe2_coords hS ha haσ hx
  rw [show ((-1 : k) + 1) / (-1 - 1) = 0 by simp, R.s_neg_one hS] at e
  generalize S 0 = v at e ⊢
  obtain ⟨X, Y, Z⟩ := v
  simp only [Prod.mk.injEq] at e ⊢
  obtain ⟨e1, e2, e3⟩ := e
  have hX : X = -1 := by linear_combination e1
  subst hX
  simp only [map_neg, map_one] at e2 e3
  have hY : Y = -1 := by linear_combination -e2
  subst hY
  exact ⟨rfl, rfl, by linear_combination e3 + h3⟩

theorem s_one
    {S : k → k × k × k} (hS : IsS R S) {a : ℕ} (ha : Even a)
    (haσ : ∀ x : k, (σ x * x) ^ a = x ^ 2) : S 1 = (-1, 0, 1 - d) := by
  have h3 := ThompsonN.three_eq_zero (K := k)
  have h2 : (1 : k) + 1 = -1 := by linear_combination h3
  have hx : (1 : k) + 1 ≠ 0 := by rw [h2]; exact neg_ne_zero.2 one_ne_zero
  have e := R.fe1_coords hS ha haσ hx
  rw [show ((1 : k) - 1) / (1 + 1) = 0 by simp, R.s_zero hS ha haσ, h2, ha.neg_pow, one_pow,
    Even.neg_pow (by decide : Even 2), one_pow] at e
  rw [e]
  simp only [inv_one, mul_one, inv_neg, Prod.mk.injEq, true_and]
  refine ⟨by ring, ?_⟩
  rw [Even.neg_one_pow (ha.add even_two), inv_one, mul_one]

end RType

end CFSG.Walter.Ree.T2
