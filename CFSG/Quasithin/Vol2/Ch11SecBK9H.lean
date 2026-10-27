module

public import CFSG.Quasithin.Vol2.Ch11SecBK9A
public import CFSG.Quasithin.Vol2.Ch11SecBK9E

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

open Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply)

variable {K : Type} [Field K] [CharP K 2]

theorem trv_mulVec_self (y : Fin 2 ⊕ Fin 2 → K) (t : K) : mat 2 K (K7.trv y t) *ᵥ y = y := by
  rw [K7.trv_mulVec, K7.bil_self, mul_zero, zero_smul, add_zero]

theorem smul_left_cancel {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) {a b : K} (h : a • y = b • y) :
    a = b := by
  by_contra hab
  apply hy
  have h1 : (a - b) • y = 0 := by rw [sub_smul, h, sub_self]
  exact (smul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hab)

structure RootCocycle (K : Type) [Field K] where
  c : ↥(StatedSp 2 K) → (Fin 2 ⊕ Fin 2 → K)
  mul : ∀ γ δ, c (γ * δ) = c γ + mat 2 K γ *ᵥ c δ
  root : ∀ y : Fin 2 ⊕ Fin 2 → K, y ≠ 0 → ∀ t : K, ∃ μ : K, c (K7.trv y t) = μ • y

namespace RootCocycle

variable (R : RootCocycle K)

theorem c_one : R.c 1 = 0 := by
  have h := R.mul 1 1
  rw [mul_one, map_one, one_mulVec] at h
  exact (add_eq_left.mp h.symm)

theorem c_inv (γ : ↥(StatedSp 2 K)) : mat 2 K γ *ᵥ R.c γ⁻¹ = -R.c γ := by
  have h := R.mul γ γ⁻¹
  rw [mul_inv_cancel, R.c_one] at h
  linear_combination (exp := 1) -h

@[expose] noncomputable def rho (y : Fin 2 ⊕ Fin 2 → K) (t : K) : K := by
  classical
  exact if hy : y = 0 then 0 else (R.root y hy t).choose

theorem rho_spec {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (t : K) :
    R.c (K7.trv y t) = R.rho y t • y := by
  classical
  simp only [rho, hy, ↓reduceDIte]
  exact (R.root y hy t).choose_spec

theorem rho_add {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (t t' : K) :
    R.rho y (t + t') = R.rho y t + R.rho y t' := by
  apply smul_left_cancel hy
  rw [← R.rho_spec hy, ← K7.trv_mul, R.mul, R.rho_spec hy, R.rho_spec hy, mulVec_smul,
    trv_mulVec_self, add_smul]

theorem rho_conj (γ : ↥(StatedSp 2 K)) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (t : K) :
    R.rho (mat 2 K γ *ᵥ y) t = R.rho y t + t * spB K (R.c γ) (mat 2 K γ *ᵥ y) := by
  have hγy : mat 2 K γ *ᵥ y ≠ 0 := fun h => hy (by
    rw [← KGNat.mat_inv_mulVec γ y, h, mulVec_zero])
  apply smul_left_cancel hγy
  have e1 : R.c (K7.trv (mat 2 K γ *ᵥ y) t) =
      R.c γ + mat 2 K γ *ᵥ R.c (K7.trv y t) +
        mat 2 K (γ * K7.trv y t) *ᵥ R.c γ⁻¹ := by
    rw [← K7.trv_conj, R.mul, R.mul, add_assoc]
  have e2 : mat 2 K (γ * K7.trv y t) *ᵥ R.c γ⁻¹ =
      mat 2 K (K7.trv (mat 2 K γ *ᵥ y) t) *ᵥ (mat 2 K γ *ᵥ R.c γ⁻¹) := by
    rw [← K7.trv_conj, mulVec_mulVec, ← map_mul, inv_mul_cancel_right]
  have hneg : spB K (-R.c γ) (mat 2 K γ *ᵥ y) = spB K (R.c γ) (mat 2 K γ *ᵥ y) := by
    rw [map_neg, LinearMap.neg_apply, CharTwo.neg_eq]
  rw [← R.rho_spec hγy, e1, e2, R.c_inv, R.rho_spec hy, mulVec_smul, K7.trv_mulVec, hneg,
    add_smul, CharTwo.neg_eq]
  have h2 : ∀ v : Fin 2 ⊕ Fin 2 → K, v + v = 0 := fun v => by
    rw [← two_smul K v, show (2 : K) = 0 from CharTwo.two_eq_zero, zero_smul]
  calc R.c γ + R.rho y t • mat 2 K γ *ᵥ y +
        (R.c γ + (t * spB K (R.c γ) (mat 2 K γ *ᵥ y)) • mat 2 K γ *ᵥ y)
      = (R.c γ + R.c γ) + (R.rho y t • mat 2 K γ *ᵥ y +
          (t * spB K (R.c γ) (mat 2 K γ *ᵥ y)) • mat 2 K γ *ᵥ y) := by abel
    _ = _ := by rw [h2, zero_add]

theorem rho_smul {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) {a : K} (ha : a ≠ 0) (t : K) :
    a * R.rho (a • y) t = R.rho y (a ^ 2 * t) := by
  apply smul_left_cancel hy
  rw [mul_smul, ← smul_comm, ← R.rho_spec (smul_ne_zero ha hy), ← R.rho_spec hy, K7.trv_smul]

end RootCocycle

section Four

variable [Finite K]

theorem exists_lin_frob (hK : Nat.card K = 4) (φ : K → K)
    (hφ : ∀ t t', φ (t + t') = φ t + φ t') : ∃ α β : K, ∀ t, φ t = α * t + β * t ^ 2 := by
  obtain ⟨ω, hω, h4⟩ := exists_omega hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h0 : φ 0 = 0 := by
    have h := hφ 0 0
    rw [add_zero] at h
    exact add_eq_left.mp h.symm
  refine ⟨φ 1 + (φ ω + ω * φ 1), φ ω + ω * φ 1, fun t => ?_⟩
  rcases h4 t with h | h | h | h <;> rw [h]
  · rw [h0]
    ring
  · linear_combination (-(φ ω + ω * φ 1)) * h2
  · linear_combination (-(φ ω + ω * φ 1)) * hω + (-(φ 1 * ω + (φ ω + ω * φ 1) * ω)) * h2
  · rw [hφ]
    linear_combination (-(φ ω + ω * φ 1)) * hω +
      (-(φ ω + 2 * φ 1 * ω + 2 * (φ ω + ω * φ 1) * ω)) * h2

theorem lin_frob_unique (hK : Nat.card K = 4) {α β α' β' : K}
    (h : ∀ t : K, α * t + β * t ^ 2 = α' * t + β' * t ^ 2) : α = α' ∧ β = β' := by
  obtain ⟨ω, hω, -⟩ := exists_omega hK
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 := h 1
  have hw := h ω
  have hd : α - α' = 0 := by
    linear_combination (1 + ω) * h1 - hw + (β - β') * hω
  refine ⟨sub_eq_zero.mp hd, ?_⟩
  linear_combination h1 - hd

namespace RootCocycle

variable (R : RootCocycle K)

@[expose] noncomputable def coef (hK : Nat.card K = 4) (y : Fin 2 ⊕ Fin 2 → K) : K × K := by
  classical
  exact if hy : y = 0 then (0, 0) else
    ((exists_lin_frob hK (R.rho y) (R.rho_add hy)).choose,
      (exists_lin_frob hK (R.rho y) (R.rho_add hy)).choose_spec.choose)

theorem rho_eq (hK : Nat.card K = 4) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (t : K) :
    R.rho y t = (R.coef hK y).1 * t + (R.coef hK y).2 * t ^ 2 := by
  classical
  simp only [coef, hy, ↓reduceDIte]
  exact (exists_lin_frob hK (R.rho y) (R.rho_add hy)).choose_spec.choose_spec t

theorem coef_zero (hK : Nat.card K = 4) : R.coef hK 0 = (0, 0) := by
  classical
  simp [coef]

theorem coef_conj (hK : Nat.card K = 4) (γ : ↥(StatedSp 2 K)) {y : Fin 2 ⊕ Fin 2 → K}
    (hy : y ≠ 0) :
    (R.coef hK (mat 2 K γ *ᵥ y)).1 = (R.coef hK y).1 + spB K (R.c γ) (mat 2 K γ *ᵥ y) ∧
      (R.coef hK (mat 2 K γ *ᵥ y)).2 = (R.coef hK y).2 := by
  have hγy : mat 2 K γ *ᵥ y ≠ 0 := fun h => hy (by
    rw [← KGNat.mat_inv_mulVec γ y, h, mulVec_zero])
  refine lin_frob_unique hK fun t => ?_
  rw [← R.rho_eq hK hγy, R.rho_conj γ hy, R.rho_eq hK hy]
  ring

theorem beta_eq (hK : Nat.card K = 4) {y y' : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) (hy' : y' ≠ 0) :
    (R.coef hK y').2 = (R.coef hK y).2 := by
  obtain ⟨γ, hγ⟩ := KGNat.exists_sp4_lin_eq y y' hy hy'
  rw [KGNat.linModelNat_lin] at hγ
  have h := (R.coef_conj hK γ hy).2
  rwa [show mat 2 K γ *ᵥ y = y' from hγ] at h

theorem alpha_smul (hK : Nat.card K = 4) {y : Fin 2 ⊕ Fin 2 → K} (hy : y ≠ 0) {a : K}
    (ha : a ≠ 0) : (R.coef hK (a • y)).1 = a * (R.coef hK y).1 := by
  have h := (lin_frob_unique hK (α := a * (R.coef hK (a • y)).1) (β := a * (R.coef hK (a • y)).2)
    (α' := a ^ 2 * (R.coef hK y).1) (β' := a ^ 4 * (R.coef hK y).2) fun t => by
      have e := R.rho_smul hy ha t
      rw [R.rho_eq hK (smul_ne_zero ha hy), R.rho_eq hK hy] at e
      linear_combination e).1
  apply mul_left_cancel₀ ha
  linear_combination h

end RootCocycle

end Four

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
