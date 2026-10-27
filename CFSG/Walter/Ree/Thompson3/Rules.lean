module

public import CFSG.Walter.Ree.Thompson3.Action

public section

namespace CFSG.Walter.Ree.T2.RType

variable {k : Type} [Field k] [CharP k 3] {σ : k ≃+* k} {d : k}
variable {G : Type} [Group G] [Finite G] (R : RType G k σ d)

theorem K_conj_torus (t : kˣ) {a ν p : ThompsonN k σ}
    (h : R.K * R.ι a * R.K = R.ι ν * R.K * R.ι p) :
    R.K * R.ι (ThompsonN.torus σ t * a * (ThompsonN.torus σ t)⁻¹) * R.K =
      R.ι ((ThompsonN.torus σ t)⁻¹ * ν * (ThompsonN.torus σ t)⁻¹) * R.K *
        R.ι ((ThompsonN.torus σ t)⁻¹ * p * ThompsonN.torus σ t) := by
  have hKT := R.K_mul_torus t
  simp only [map_inv] at hKT
  simp only [map_mul, map_inv]
  generalize R.ι (ThompsonN.torus σ t) = T at hKT ⊢
  have hTK : T * R.K = R.K * T⁻¹ := by
    calc T * R.K = T * (R.K * T) * T⁻¹ := by group
      _ = T * (T⁻¹ * R.K) * T⁻¹ := by rw [hKT]
      _ = R.K * T⁻¹ := by group
  calc R.K * (T * R.ι a * T⁻¹) * R.K = (R.K * T) * R.ι a * (T⁻¹ * R.K) := by group
    _ = (T⁻¹ * R.K) * R.ι a * (R.K * T) := by rw [hKT]
    _ = T⁻¹ * (R.K * R.ι a * R.K) * T := by group
    _ = T⁻¹ * (R.ι ν * R.K * R.ι p) * T := by rw [h]
    _ = T⁻¹ * R.ι ν * T⁻¹ * (T * R.K) * R.ι p * T := by group
    _ = T⁻¹ * R.ι ν * T⁻¹ * (R.K * T⁻¹) * R.ι p * T := by rw [hTK]
    _ = _ := by group

theorem K_f_K {a ν p : ThompsonN k σ} (h : R.K * R.ι a * R.K = R.ι ν * R.K * R.ι p) :
    R.K * R.ι p * R.K = R.ι ν⁻¹ * R.K * R.ι a := by
  have hKK := R.K_mul_K
  rw [map_inv]
  calc R.K * R.ι p * R.K = (R.ι ν)⁻¹ * (R.ι ν * R.K * R.ι p) * R.K := by group
    _ = (R.ι ν)⁻¹ * R.K * R.ι a * (R.K * R.K) := by rw [← h]; group
    _ = _ := by rw [hKK, mul_one]

theorem K_inv_K {a g p : ThompsonN k σ} {κ : kˣ}
    (h : R.K * R.ι a * R.K = R.ι (g * ThompsonN.torus σ κ) * R.K * R.ι p) :
    R.K * R.ι a⁻¹ * R.K = R.ι (p⁻¹ * ThompsonN.torus σ κ) * R.K * R.ι g⁻¹ := by
  have hKi := R.K_inv_eq
  have hKT := R.torus_mul_K κ
  have e := congrArg (·⁻¹) h
  simp only [mul_inv_rev, hKi, map_mul, map_inv] at e hKT ⊢
  calc R.K * (R.ι a)⁻¹ * R.K = R.K * ((R.ι a)⁻¹ * R.K) := by group
    _ = (R.ι p)⁻¹ * (R.K * ((R.ι (ThompsonN.torus σ κ))⁻¹ * (R.ι g)⁻¹)) := e
    _ = (R.ι p)⁻¹ * (R.K * (R.ι (ThompsonN.torus σ κ))⁻¹) * (R.ι g)⁻¹ := by group
    _ = (R.ι p)⁻¹ * (R.ι (ThompsonN.torus σ κ) * R.K) * (R.ι g)⁻¹ := by rw [hKT]
    _ = _ := by group

theorem cocycle {a a' ν p g' p' ν₁ p₁ : ThompsonN k σ} {κ : kˣ}
    (h : R.K * R.ι a * R.K = R.ι ν * R.K * R.ι p)
    (h' : R.K * R.ι a' * R.K = R.ι (g' * ThompsonN.torus σ κ) * R.K * R.ι p')
    (hX : R.K * R.ι (p * g') * R.K = R.ι ν₁ * R.K * R.ι p₁) :
    R.K * R.ι (a * a') * R.K = R.ι (ν * ν₁ * ThompsonN.torus σ κ) * R.K *
      R.ι (ThompsonN.torus σ κ * p₁ * (ThompsonN.torus σ κ)⁻¹ * p') := by
  have hKK := R.K_mul_K
  have hKt := R.K_mul_torus κ
  simp only [map_mul, map_inv] at h' hX hKt ⊢
  generalize R.ι (ThompsonN.torus σ κ) = T at h' hKt ⊢
  have hKti : R.K * T⁻¹ = T * R.K := by
    calc R.K * T⁻¹ = T * (T⁻¹ * R.K) * T⁻¹ := by group
      _ = T * (R.K * T) * T⁻¹ := by rw [hKt]
      _ = T * R.K := by group
  calc R.K * (R.ι a * R.ι a') * R.K = (R.K * R.ι a * R.K) * (R.K * R.ι a' * R.K) := by
        rw [show (R.K * R.ι a * R.K) * (R.K * R.ι a' * R.K) =
          R.K * R.ι a * (R.K * R.K) * R.ι a' * R.K by group, hKK]
        group
    _ = (R.ι ν * R.K * R.ι p) * (R.ι g' * T * R.K * R.ι p') := by rw [h, h']
    _ = R.ι ν * (R.K * (R.ι p * R.ι g') * R.K) * (R.K * T * R.K) * R.ι p' := by
        rw [show R.ι ν * (R.K * (R.ι p * R.ι g') * R.K) * (R.K * T * R.K) * R.ι p' =
          R.ι ν * R.K * R.ι p * R.ι g' * (R.K * R.K) * T * R.K * R.ι p' by group, hKK]
        group
    _ = R.ι ν * (R.ι ν₁ * R.K * R.ι p₁) * T⁻¹ * R.ι p' := by
        rw [hX, hKt, mul_assoc T⁻¹ R.K R.K, hKK, mul_one]
    _ = R.ι ν * R.ι ν₁ * (R.K * T⁻¹) * (T * R.ι p₁ * T⁻¹) * R.ι p' := by group
    _ = R.ι ν * R.ι ν₁ * (T * R.K) * (T * R.ι p₁ * T⁻¹) * R.ι p' := by rw [hKti]
    _ = _ := by group

theorem pres_unique_P
    [Finite k] {ν ν' p p' : ThompsonN k σ} (hp : p ∈ ThompsonN.P σ)
    (hp' : p' ∈ ThompsonN.P σ) (h : R.ι ν * R.K * R.ι p = R.ι ν' * R.K * R.ι p') :
    ν = ν' ∧ p = p' := by
  rw [← ppv_coords hp, ← ppv_coords hp'] at h
  obtain ⟨h1, h2⟩ := R.pres_unique h
  exact ⟨h1, by rw [← ppv_coords hp, h2, ppv_coords hp']⟩

end CFSG.Walter.Ree.T2.RType
