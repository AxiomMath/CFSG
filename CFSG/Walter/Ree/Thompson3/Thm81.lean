module

public import CFSG.Walter.Ree.Thompson3.Base
public import CFSG.Walter.Ree.Thompson3.Rules
import CFSG.Walter.Ree.Thompson2.BaseRel

public section

namespace CFSG.Walter.Ree.T2

variable {k : Type} [Field k] [CharP k 3]

theorem tY_pow_seven (σ : k ≃+* k) (d : k) : tY σ d ^ 7 = (tY σ d ^ 2)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← pow_add]; exact tY_pow_nine σ d)

theorem tY_pow_seven_eq (σ : k ≃+* k) (d : k) : tY σ d ^ 7 = pp σ 1 0 (d - 1) := by
  rw [tY_pow_seven, tY_sq]
  simp only [pp]
  rw [ThompsonN.inv_P]
  ext
  · rfl
  · simp
  · simp
  · simp only; ring

theorem torus_conj_inv {σ : k ≃+* k} (t : kˣ) (α β γ : k) :
    ThompsonN.torus σ t * ⟨1, α, β, γ⟩ * (ThompsonN.torus σ t)⁻¹ =
      ⟨1, α * (t : k)⁻¹, β * ((t : k)⁻¹ * σ (t : k)⁻¹), γ * ((t : k)⁻¹ ^ 2 * σ (t : k)⁻¹)⟩ := by
  have h := ThompsonN.torus_conj (σ := σ) t⁻¹ α β γ
  rw [map_inv, inv_inv] at h
  rw [h]
  simp [Units.val_inv_eq_inv_val]

theorem conj_eq_A {σ : k ≃+* k} {z y u : k} (hz : z ≠ 0) (hy : y ≠ 0)
    (h1 : σ z * z ^ 2 - σ y * y ^ 2 = -1) (h2 : σ z * z - σ y * y = u) :
    ThompsonN.torus σ (Units.mk0 z hz) * pp σ 0 u 1 * (ThompsonN.torus σ (Units.mk0 z hz))⁻¹ =
      ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy) * pp σ 0 (-1) 1 *
        (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy))⁻¹ * (pp σ 0 (-1) 1)⁻¹ := by
  simp only [pp]
  rw [torus_conj_inv, torus_conj_inv, ThompsonN.inv_P, ThompsonN.mul_P]
  have hsz : σ z ≠ 0 := by simpa using hz
  have hsy : σ y ≠ 0 := by simpa using hy
  ext
  · rfl
  · simp
  · simp only [Units.val_div_eq_div_val, Units.val_mk0, map_inv₀, map_div₀, map_zero, zero_mul,
      add_zero, sub_zero]
    field_simp
    linear_combination (-1 : k) * h2
  · simp only [Units.val_div_eq_div_val, Units.val_mk0, map_inv₀, map_div₀, map_zero, zero_mul,
      add_zero]
    field_simp
    linear_combination h1

theorem conj_eq_B {σ : k ≃+* k} {z y u : k} (hz : z ≠ 0) (hy : y ≠ 0)
    (h1 : σ z * z ^ 2 - σ y * y ^ 2 = -1) (h2 : σ z * z - σ y * y = u) :
    ThompsonN.torus σ (Units.mk0 y hy) * pp σ 0 (-u) 1 * (ThompsonN.torus σ (Units.mk0 y hy))⁻¹ *
        ((ThompsonN.J σ)⁻¹ * pp σ 0 (-1) 1 * ThompsonN.J σ) * ThompsonN.J σ =
      ThompsonN.J σ * ((ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy))⁻¹ * pp σ 0 (-1) 1 *
        ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) := by
  have hJJ : ThompsonN.J σ * ThompsonN.J σ = 1 := by rw [ThompsonN.J, ← map_mul]; simp
  have hJi : (ThompsonN.J σ)⁻¹ = ThompsonN.J σ := inv_eq_of_mul_eq_one_right hJJ
  suffices h : (ThompsonN.J σ)⁻¹ * (ThompsonN.torus σ (Units.mk0 y hy) * pp σ 0 (-u) 1 *
      (ThompsonN.torus σ (Units.mk0 y hy))⁻¹ * ((ThompsonN.J σ)⁻¹ * pp σ 0 (-1) 1 *
        ThompsonN.J σ)) * ThompsonN.J σ =
      (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy))⁻¹ * pp σ 0 (-1) 1 *
        ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy) by
    rw [← h, hJi]
    simp only [← mul_assoc, hJJ, one_mul]
  simp only [pp]
  rw [ThompsonN.J_conj, torus_conj_inv, ThompsonN.mul_P, ThompsonN.J_conj, ThompsonN.torus_conj]
  have hsz : σ z ≠ 0 := by simpa using hz
  have hsy : σ y ≠ 0 := by simpa using hy
  ext
  · rfl
  · simp
  · simp only [Units.val_div_eq_div_val, Units.val_mk0, map_inv₀, map_div₀, map_zero, mul_zero,
      zero_mul, add_zero, sub_zero, neg_zero]
    field_simp
    linear_combination h2
  · simp only [Units.val_div_eq_div_val, Units.val_mk0, map_inv₀, map_div₀, map_zero, mul_zero,
      zero_mul, add_zero, sub_zero, neg_zero]
    field_simp
    linear_combination (-1 : k) * h1

namespace RType

variable {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem K_Y7_K : R.K * R.ι (tY σ d ^ 7) * R.K =
    R.ι ((ThompsonN.J σ)⁻¹ * pp σ 0 (-1) 1 * ThompsonN.J σ) * R.Jg * R.K *
      (R.ι (pp σ 0 (-1) 1))⁻¹ := by
  have ha := R.rel_a
  have hKK := R.K_mul_K
  have hJK := R.Jg_mul_K
  have hKi := R.K_inv_eq
  have hJJ : R.Jg * R.Jg = 1 := by
    rw [Jg, ← map_mul, ThompsonN.J, ← map_mul]; simp
  have hJi : R.Jg⁻¹ = R.Jg := inv_eq_of_mul_eq_one_right hJJ
  have hιJ : R.ι ((ThompsonN.J σ)⁻¹ * pp σ 0 (-1) 1 * ThompsonN.J σ) =
      R.Jg * R.ι (pp σ 0 (-1) 1) * R.Jg := by
    rw [map_mul, map_mul, map_inv, ← Jg, hJi]
  rw [tY_pow_seven, map_inv, map_pow, hιJ]
  generalize R.ι (pp σ 0 (-1) 1) = P at ha ⊢
  generalize R.ι (tY σ d) = Y at ha ⊢
  have hY2 : Y ^ 2 = R.K * P * R.K * P⁻¹ * R.K * R.Jg := by
    rw [← hJi]; exact eq_mul_inv_of_mul_eq ha.symm
  rw [hY2]
  simp only [mul_inv_rev, inv_inv, hKi, hJi]
  have hKK' : ∀ x, R.K * (R.K * x) = x := fun x => by rw [← mul_assoc, hKK, one_mul]
  have hKJ' : ∀ x, R.K * (R.Jg * x) = R.Jg * (R.K * x) := fun x => by
    rw [← mul_assoc, ← hJK, mul_assoc]
  simp only [mul_assoc, hKK, hJJ, hKK', hKJ', mul_one]

theorem K_B_K_Y7_K {z y u : k} (hz : z ≠ 0) (hy : y ≠ 0)
    (h1 : σ z * z ^ 2 - σ y * y ^ 2 = -1) (h2 : σ z * z - σ y * y = u) :
    R.K * R.ι (ThompsonN.torus σ (Units.mk0 y hy) * pp σ 0 (-u) 1 *
        (ThompsonN.torus σ (Units.mk0 y hy))⁻¹) * R.K * R.ι (tY σ d ^ 7) * R.K =
      R.Jg * R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) * R.ι (tY σ d) ^ 2 *
        R.Jg * R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) * R.K *
          R.ι (ThompsonN.torus σ (Units.mk0 z hz) * pp σ 0 u 1 *
            (ThompsonN.torus σ (Units.mk0 z hz))⁻¹) := by
  have hb := R.K_Y7_K
  have hB : R.ι (ThompsonN.torus σ (Units.mk0 y hy) * pp σ 0 (-u) 1 *
        (ThompsonN.torus σ (Units.mk0 y hy))⁻¹) *
        R.ι ((ThompsonN.J σ)⁻¹ * pp σ 0 (-1) 1 * ThompsonN.J σ) * R.Jg =
      R.Jg * ((R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)))⁻¹ *
        R.ι (pp σ 0 (-1) 1) * R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy))) := by
    have := congrArg R.ι (conj_eq_B hz hy h1 h2)
    simp only [map_mul, map_inv] at this ⊢
    exact this
  have hA : R.ι (ThompsonN.torus σ (Units.mk0 z hz) * pp σ 0 u 1 *
        (ThompsonN.torus σ (Units.mk0 z hz))⁻¹) =
      R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) * R.ι (pp σ 0 (-1) 1) *
        (R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)))⁻¹ *
          (R.ι (pp σ 0 (-1) 1))⁻¹ := by
    rw [conj_eq_A hz hy h1 h2]; simp only [map_mul, map_inv]
  have ha := R.rel_a
  have hKK := R.K_mul_K
  have hJK := R.Jg_mul_K
  have hKT := R.K_mul_torus (Units.mk0 z hz / Units.mk0 y hy)
  simp only [map_inv] at hKT
  rw [hA]
  generalize R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) = T at hKT hB ⊢
  generalize R.ι (ThompsonN.torus σ (Units.mk0 y hy) * pp σ 0 (-u) 1 *
    (ThompsonN.torus σ (Units.mk0 y hy))⁻¹) = B at hB ⊢
  generalize R.ι ((ThompsonN.J σ)⁻¹ * pp σ 0 (-1) 1 * ThompsonN.J σ) = PJ at hb hB ⊢
  generalize R.ι (pp σ 0 (-1) 1) = P at ha hb hB ⊢
  generalize R.ι (tY σ d ^ 7) = Y7 at hb ⊢
  have hTK : T * R.K = R.K * T⁻¹ := by
    calc T * R.K = T * (R.K * T) * T⁻¹ := by group
      _ = T * (T⁻¹ * R.K) * T⁻¹ := by rw [hKT]
      _ = R.K * T⁻¹ := by group
  have ha' : R.K * P * R.K = R.ι (tY σ d) ^ 2 * R.Jg * R.K * P := by
    rw [← ha]
    calc R.K * P * R.K = R.K * P * R.K * P⁻¹ * (R.K * R.K) * P := by rw [hKK]; group
      _ = _ := by group
  calc R.K * B * R.K * Y7 * R.K = R.K * B * (R.K * Y7 * R.K) := by group
    _ = R.K * B * (PJ * R.Jg * R.K * P⁻¹) := by rw [hb]
    _ = R.K * (B * PJ * R.Jg) * R.K * P⁻¹ := by group
    _ = R.K * (R.Jg * (T⁻¹ * P * T)) * R.K * P⁻¹ := by rw [hB]
    _ = (R.K * R.Jg) * T⁻¹ * P * (T * R.K) * P⁻¹ := by group
    _ = (R.Jg * R.K) * T⁻¹ * P * (T * R.K) * P⁻¹ := by rw [hJK]
    _ = R.Jg * (R.K * T⁻¹) * P * (T * R.K) * P⁻¹ := by group
    _ = R.Jg * (T * R.K) * P * (R.K * T⁻¹) * P⁻¹ := by rw [hTK]
    _ = R.Jg * T * (R.K * P * R.K) * T⁻¹ * P⁻¹ := by group
    _ = R.Jg * T * (R.ι (tY σ d) ^ 2 * R.Jg * R.K * P) * T⁻¹ * P⁻¹ := by rw [ha']
    _ = R.Jg * T * R.ι (tY σ d) ^ 2 * R.Jg * (R.K * T⁻¹) * (T * P * T⁻¹ * P⁻¹) := by group
    _ = R.Jg * T * R.ι (tY σ d) ^ 2 * R.Jg * (T * R.K) * (T * P * T⁻¹ * P⁻¹) := by rw [hTK]
    _ = _ := by group

theorem thm81'
    [Finite k] {z y u : k} (hz : z ≠ 0) (hy : y ≠ 0) (hE : (z, y, u) ∈ hopkinsE σ)
    {ν ν' p p' : ThompsonN k σ} (hp : p ∈ ThompsonN.P σ) (hp' : p' ∈ ThompsonN.P σ)
    (h1 : R.K * R.ι (pp σ 0 u 1) * R.K = R.ι ν * R.K * R.ι p)
    (h2 : R.K * R.ι (pp σ 0 (-u) 1) * R.K = R.ι ν' * R.K * R.ι p') :
    (ThompsonN.torus σ (Units.mk0 z hz))⁻¹ * p * ThompsonN.torus σ (Units.mk0 z hz) =
      (ThompsonN.torus σ (Units.mk0 y hy))⁻¹ * p' * ThompsonN.torus σ (Units.mk0 y hy) *
        tY σ d ^ 7 := by
  obtain ⟨hE1, hE2⟩ := hE
  have hA := R.K_conj_torus (Units.mk0 z hz) h1
  have hB := R.K_conj_torus (Units.mk0 y hy) h2
  have hst := R.K_B_K_Y7_K hz hy hE1 hE2
  have hKK := R.K_mul_K
  rw [show R.Jg = R.ι (ThompsonN.J σ) from rfl] at hst
  have hKAK : R.K * R.ι (ThompsonN.torus σ (Units.mk0 z hz) * pp σ 0 u 1 *
        (ThompsonN.torus σ (Units.mk0 z hz))⁻¹) * R.K =
      (R.ι (ThompsonN.J σ) * R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) *
        R.ι (tY σ d) ^ 2 * R.ι (ThompsonN.J σ) *
          R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)))⁻¹ *
        (R.K * R.ι (ThompsonN.torus σ (Units.mk0 y hy) * pp σ 0 (-u) 1 *
          (ThompsonN.torus σ (Units.mk0 y hy))⁻¹) * R.K) * R.ι (tY σ d ^ 7) := by
    generalize R.ι (ThompsonN.torus σ (Units.mk0 z hz) * pp σ 0 u 1 *
      (ThompsonN.torus σ (Units.mk0 z hz))⁻¹) = A at hst ⊢
    generalize R.ι (ThompsonN.torus σ (Units.mk0 y hy) * pp σ 0 (-u) 1 *
      (ThompsonN.torus σ (Units.mk0 y hy))⁻¹) = B at hst ⊢
    generalize R.ι (tY σ d ^ 7) = Y7 at hst ⊢
    generalize R.ι (ThompsonN.J σ) * R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) *
      R.ι (tY σ d) ^ 2 * R.ι (ThompsonN.J σ) *
        R.ι (ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy)) = W at hst ⊢
    calc R.K * A * R.K = W⁻¹ * (W * R.K * A) * R.K := by group
      _ = W⁻¹ * (R.K * B * R.K * Y7 * R.K) * R.K := by rw [← hst]
      _ = W⁻¹ * (R.K * B * R.K) * Y7 * (R.K * R.K) := by group
      _ = _ := by rw [hKK, mul_one]
  have hpres : R.ι ((ThompsonN.torus σ (Units.mk0 z hz))⁻¹ * ν *
        (ThompsonN.torus σ (Units.mk0 z hz))⁻¹) * R.K *
        R.ι ((ThompsonN.torus σ (Units.mk0 z hz))⁻¹ * p * ThompsonN.torus σ (Units.mk0 z hz)) =
      R.ι ((ThompsonN.J σ * ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy) * tY σ d ^ 2 *
          ThompsonN.J σ * ThompsonN.torus σ (Units.mk0 z hz / Units.mk0 y hy))⁻¹ *
        ((ThompsonN.torus σ (Units.mk0 y hy))⁻¹ * ν' * (ThompsonN.torus σ (Units.mk0 y hy))⁻¹)) *
        R.K * R.ι ((ThompsonN.torus σ (Units.mk0 y hy))⁻¹ * p' *
          ThompsonN.torus σ (Units.mk0 y hy) * tY σ d ^ 7) := by
    rw [← hA, hKAK, hB]
    simp only [map_mul, map_inv, map_pow]
    group
  have hm1 : (ThompsonN.torus σ (Units.mk0 z hz))⁻¹ * p * ThompsonN.torus σ (Units.mk0 z hz) ∈
      ThompsonN.P σ := by
    simpa using (ThompsonN.P_normal (σ := σ)).conj_mem _ hp
      (ThompsonN.torus σ (Units.mk0 z hz))⁻¹
  have hm2 : (ThompsonN.torus σ (Units.mk0 y hy))⁻¹ * p' * ThompsonN.torus σ (Units.mk0 y hy) *
      tY σ d ^ 7 ∈ ThompsonN.P σ := by
    refine (ThompsonN.P σ).mul_mem ?_ ((ThompsonN.P σ).pow_mem rfl 7)
    simpa using (ThompsonN.P_normal (σ := σ)).conj_mem _ hp'
      (ThompsonN.torus σ (Units.mk0 y hy))⁻¹
  rw [← ppv_coords hm1, ← ppv_coords hm2] at hpres
  have := (R.pres_unique hpres).2
  rw [← ppv_coords hm1, this, ppv_coords hm2]

theorem thm81 [Finite k] :
    ∀ (z y u : k) (hz : z ≠ 0) (hy : y ≠ 0), u ≠ 0 → (z, y, u) ∈ hopkinsE σ →
      ∀ (ν ν' p p' : ThompsonN k σ), p ∈ ThompsonN.P σ → p' ∈ ThompsonN.P σ →
        R.K * R.ι (pp σ 0 u 1) * R.K = R.ι ν * R.K * R.ι p →
        R.K * R.ι (pp σ 0 (-u) 1) * R.K = R.ι ν' * R.K * R.ι p' →
        (ThompsonN.torus σ (Units.mk0 z hz))⁻¹ * p * ThompsonN.torus σ (Units.mk0 z hz) =
          (ThompsonN.torus σ (Units.mk0 y hy))⁻¹ * p' * ThompsonN.torus σ (Units.mk0 y hy) *
            tY σ d ^ 7 :=
  fun _ _ _ hz hy _ hE _ _ _ _ hp hp' h1 h2 => R.thm81' hz hy hE hp hp' h1 h2

theorem components_thm81
    [Finite k] {S : k → k × k × k} (hS : IsS R S) {z y u : k}
    (hz : z ≠ 0) (hy : y ≠ 0) (hE : (z, y, u) ∈ hopkinsE σ) :
    (S u).1 * z = (S (-u)).1 * y + 1 ∧
    (S u).2.1 * (z * σ z) = (S (-u)).2.1 * (y * σ y) + (S (-u)).1 * y - σ ((S (-u)).1 * y) ∧
    (S u).2.2 * (z ^ 2 * σ z) = d - 1 + (S (-u)).2.2 * (y ^ 2 * σ y) +
      (S (-u)).2.1 * (y * σ y) + σ ((S (-u)).1 * y) + (S (-u)).1 * y - ((S (-u)).1 * y) ^ 2 := by
  obtain ⟨ν, hν⟩ := hS u
  obtain ⟨ν', hν'⟩ := hS (-u)
  have h := R.thm81' hz hy hE (ppv_mem_P σ _) (ppv_mem_P σ _) hν hν'
  rw [show ppv σ (S u) = ⟨1, (S u).1, (S u).2.1, (S u).2.2⟩ from rfl,
    show ppv σ (S (-u)) = ⟨1, (S (-u)).1, (S (-u)).2.1, (S (-u)).2.2⟩ from rfl,
    ThompsonN.torus_conj, ThompsonN.torus_conj, tY_pow_seven_eq] at h
  simp only [pp] at h
  rw [ThompsonN.mul_P] at h
  simp only [ThompsonN.mk.injEq, Units.val_mk0, map_one, mul_one, one_pow, add_zero,
    true_and] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1.trans (by ring), h2.trans (by ring), h3.trans (by ring)⟩

end RType

end CFSG.Walter.Ree.T2
