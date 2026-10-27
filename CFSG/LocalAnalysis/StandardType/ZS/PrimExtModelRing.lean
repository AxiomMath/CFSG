module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.LinearCombination
public import CFSG.LocalAnalysis.StandardType.ZS.ExcMatrices

public section

namespace CFSG.StandardType.ZS.PrimModel

abbrev ZAl : Type := QuadraticAlgebra ℤ 1 1

abbrev ZGa : Type := QuadraticAlgebra ℤ (-2) (-1)

@[expose] def qa (a b : ℤ) : ZAl := ⟨a, b⟩

@[expose] def qg (a b : ℤ) : ZGa := ⟨a, b⟩

@[expose] def GoodAl (x : ZAl) : Prop := QuadraticAlgebra.norm x ∣ 2 ^ 32

instance (x : ZAl) : Decidable (GoodAl x) := inferInstanceAs (Decidable (_ ∣ _))

@[expose] def GoodGa (x : ZGa) : Prop := QuadraticAlgebra.norm x ∣ 2 ^ 32

instance (x : ZGa) : Decidable (GoodGa x) := inferInstanceAs (Decidable (_ ∣ _))

@[expose] def GoodZ (x : ℤ) : Prop := x ∣ 2 ^ 32

instance (x : ℤ) : Decidable (GoodZ x) := inferInstanceAs (Decidable (_ ∣ _))

variable {p : ℕ} [Fact p.Prime]

@[expose] noncomputable def evalAl {α : ZMod p} (hα : α ^ 2 = α + 1) : ZAl →+* ZMod p :=
  (QuadraticAlgebra.lift ⟨α, by rw [one_smul, one_smul, ← sq, hα, add_comm]⟩).toRingHom

@[expose] noncomputable def evalGa {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) : ZGa →+* ZMod p :=
  (QuadraticAlgebra.lift ⟨2 * β, by
    simp only [zsmul_eq_mul]
    push_cast
    linear_combination 2 * hβ⟩).toRingHom

theorem evalAl_qa {α : ZMod p} (hα : α ^ 2 = α + 1) (a b : ℤ) :
    evalAl hα (qa a b) = a + b * α := by
  have h : evalAl hα (qa a b) = a • (1 : ZMod p) + b • α := rfl
  rw [h]
  simp only [zsmul_eq_mul, mul_one]

theorem evalGa_qg {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) (a b : ℤ) :
    evalGa hβ (qg a b) = a + b * (2 * β) := by
  have h : evalGa hβ (qg a b) = a • (1 : ZMod p) + b • (2 * β) := rfl
  rw [h]
  simp only [zsmul_eq_mul, mul_one]

private theorem intCast_ne_zero_of_dvd_two_pow (hp : p ≠ 2) {x : ℤ} (hx : x ∣ 2 ^ 32) :
    Int.castRingHom (ZMod p) x ≠ 0 := by
  intro h
  have hpp : p.Prime := Fact.out
  have hpx : (p : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h
  have hdvd : (p : ℤ) ∣ (2 : ℤ) ^ 32 := dvd_trans hpx hx
  have hdvd_nat : p ∣ 2 ^ 32 := by exact_mod_cast hdvd
  have hp2 : p ∣ 2 := hpp.dvd_of_dvd_pow hdvd_nat
  exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp hp2)

theorem evalAl_ne_zero (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) {x : ZAl}
    (hx : GoodAl x) : evalAl hα x ≠ 0 := by
  intro h
  have hmap : Int.castRingHom (ZMod p) (QuadraticAlgebra.norm x) = 0 := by
    have h1 := congrArg (evalAl hα) (QuadraticAlgebra.algebraMap_norm_eq_mul_star x)
    rw [map_mul, h, zero_mul] at h1
    have h2 : evalAl hα ((QuadraticAlgebra.norm x : ℤ) : ZAl) = 0 := h1
    rw [map_intCast] at h2
    exact h2
  exact intCast_ne_zero_of_dvd_two_pow hp (show GoodZ (QuadraticAlgebra.norm x) from hx) hmap

theorem evalGa_ne_zero (hp : p ≠ 2) {β : ZMod p} (hβ : 2 * β ^ 2 + β + 1 = 0) {x : ZGa}
    (hx : GoodGa x) : evalGa hβ x ≠ 0 := by
  intro h
  have hmap : Int.castRingHom (ZMod p) (QuadraticAlgebra.norm x) = 0 := by
    have h1 := congrArg (evalGa hβ) (QuadraticAlgebra.algebraMap_norm_eq_mul_star x)
    rw [map_mul, h, zero_mul] at h1
    have h2 : evalGa hβ ((QuadraticAlgebra.norm x : ℤ) : ZGa) = 0 := h1
    rw [map_intCast] at h2
    exact h2
  exact intCast_ne_zero_of_dvd_two_pow hp (show GoodZ (QuadraticAlgebra.norm x) from hx) hmap

theorem intCast_ne_zero_of_goodZ (hp : p ≠ 2) {x : ℤ} (hx : GoodZ x) :
    Int.castRingHom (ZMod p) x ≠ 0 :=
  intCast_ne_zero_of_dvd_two_pow hp hx

section Scaled

variable {R : Type} [CommRing R] {n : ℕ}

@[expose] def reflZ (r c : Fin n → R) : Matrix (Fin n) (Fin n) R :=
  (2 : R) • (1 : Matrix (Fin n) (Fin n) R) - Matrix.vecMulVec r c

@[expose] def diagZ (i : Fin n) : Matrix (Fin n) (Fin n) R :=
  Matrix.diagonal fun j => if j = i then -2 else 2

@[expose] noncomputable def evMat (φ : R →+* ZMod p) (k : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) (ZMod p) :=
  ((2 : ZMod p) ^ k)⁻¹ • M.map φ

private theorem evMat_two_ne_zero (hp : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have hpp : p.Prime := Fact.out
  exact hp ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp
    ((ZMod.natCast_eq_zero_iff 2 p).mp h))

private theorem map_two_pow_smul_one (φ : R →+* ZMod p) (k : ℕ) :
    (((2 : R) ^ k • (1 : Matrix (Fin n) (Fin n) R)).map φ)
      = (2 : ZMod p) ^ k • (1 : Matrix (Fin n) (Fin n) (ZMod p)) := by
  rw [Matrix.map_smulₛₗ φ φ ((2 : R) ^ k) (fun a => by simp only [smul_eq_mul, map_mul])]
  simp [map_ofNat]

theorem evMat_mul (φ : R →+* ZMod p) (k l : ℕ) (M N : Matrix (Fin n) (Fin n) R) :
    evMat φ (k + l) (M * N) = evMat φ k M * evMat φ l N := by
  simp only [evMat, Matrix.map_mul, pow_add, mul_inv_rev]
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [mul_comm ((2 : ZMod p) ^ l)⁻¹ ((2 : ZMod p) ^ k)⁻¹]

theorem evMat_pow (φ : R →+* ZMod p) (k e : ℕ) (M : Matrix (Fin n) (Fin n) R) :
    evMat φ (k * e) (M ^ e) = evMat φ k M ^ e := by
  induction e with
  | zero =>
      rw [Nat.mul_zero, pow_zero, evMat, Matrix.map_one φ (map_zero φ) (map_one φ)]
      simp
  | succ e ih =>
      calc evMat φ (k * (e + 1)) (M ^ (e + 1))
          = evMat φ (k * e + k) (M ^ e * M) := by rw [Nat.mul_succ, pow_succ]
        _ = evMat φ (k * e) (M ^ e) * evMat φ k M := evMat_mul φ (k * e) k (M ^ e) M
        _ = evMat φ k M ^ e * evMat φ k M := by rw [ih]
        _ = evMat φ k M ^ (e + 1) := (pow_succ _ _).symm

theorem evMat_two_pow_smul_one (hp : p ≠ 2) (φ : R →+* ZMod p) (k : ℕ) :
    evMat φ k ((2 : R) ^ k • (1 : Matrix (Fin n) (Fin n) R)) = 1 := by
  rw [evMat, map_two_pow_smul_one φ k, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero k (evMat_two_ne_zero hp)), one_smul]

theorem evMat_reflZ (hp : p ≠ 2) (φ : R →+* ZMod p) (r c : Fin n → R) :
    evMat φ 1 (reflZ r c) =
      1 - Matrix.vecMulVec (fun i => φ (r i)) (fun i => (2 : ZMod p)⁻¹ * φ (c i)) := by
  have h2 : (((2 : R) • (1 : Matrix (Fin n) (Fin n) R)).map φ)
      = (2 : ZMod p) • (1 : Matrix (Fin n) (Fin n) (ZMod p)) := by
    rw [Matrix.map_smulₛₗ φ φ (2 : R) (fun a => by simp only [smul_eq_mul, map_mul])]
    simp [map_ofNat]
  have hv : ((Matrix.vecMulVec r c : Matrix (Fin n) (Fin n) R).map φ)
      = Matrix.vecMulVec (fun i => φ (r i)) (fun i => φ (c i)) := by
    ext i j
    simp [Matrix.vecMulVec_apply]
  have hsub : (2 : ZMod p)⁻¹ • Matrix.vecMulVec (fun i => φ (r i)) (fun i => φ (c i))
      = Matrix.vecMulVec (fun i => φ (r i)) (fun i => (2 : ZMod p)⁻¹ * φ (c i)) := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  rw [evMat, reflZ, Matrix.map_sub φ (fun a b => map_sub φ a b), h2, hv, pow_one,
    smul_sub, smul_smul, inv_mul_cancel₀ (evMat_two_ne_zero hp), one_smul, hsub]

theorem evMat_diagZ (hp : p ≠ 2) (φ : R →+* ZMod p) (i : Fin n) :
    evMat φ 1 (diagZ i : Matrix (Fin n) (Fin n) R) = diagSignMat i := by
  ext j k
  simp only [evMat, diagZ, diagSignMat, Matrix.smul_apply, Matrix.map_apply,
    Matrix.diagonal_apply, smul_eq_mul, pow_one]
  by_cases hjk : j = k
  · subst hjk
    rw [if_pos rfl, if_pos rfl]
    by_cases hji : j = i
    · subst hji
      rw [if_pos rfl, if_pos rfl, map_neg, map_ofNat, mul_neg,
        inv_mul_cancel₀ (evMat_two_ne_zero hp)]
    · rw [if_neg hji, if_neg hji, map_ofNat, inv_mul_cancel₀ (evMat_two_ne_zero hp)]
  · rw [if_neg hjk, if_neg hjk, map_zero, mul_zero]

theorem evMat_ne_one (φ : R →+* ZMod p) {good : R → Prop} (hgood : ∀ x, good x → φ x ≠ 0)
    {k : ℕ} {M : Matrix (Fin n) (Fin n) R} {a b : Fin n}
    (h : good ((M - (2 : R) ^ k • (1 : Matrix (Fin n) (Fin n) R)) a b)) : evMat φ k M ≠ 1 := by
  intro hev
  have hgood' : φ ((M - (2 : R) ^ k • (1 : Matrix (Fin n) (Fin n) R)) a b) ≠ 0 := hgood _ h
  by_cases hk : (2 : ZMod p) ^ k = 0
  · have h1 : (0 : ZMod p) = 1 := by
      have h2 : (evMat φ k M) a a = (1 : Matrix (Fin n) (Fin n) (ZMod p)) a a := by rw [hev]
      simp [evMat, hk] at h2
    exact one_ne_zero h1.symm
  · have hM : M.map φ = (2 : ZMod p) ^ k • (1 : Matrix (Fin n) (Fin n) (ZMod p)) := by
      have h3 := congrArg (fun X : Matrix (Fin n) (Fin n) (ZMod p) => (2 : ZMod p) ^ k • X) hev
      simpa [evMat, smul_smul, mul_inv_cancel₀ hk] using h3
    have hzero : φ ((M - (2 : R) ^ k • (1 : Matrix (Fin n) (Fin n) R)) a b) = 0 := by
      have h4 : ((M - (2 : R) ^ k • (1 : Matrix (Fin n) (Fin n) R)).map φ) a b = 0 := by
        rw [Matrix.map_sub φ (fun x y => map_sub φ x y), hM, map_two_pow_smul_one φ k]
        simp
      rwa [Matrix.map_apply] at h4
    exact hgood' hzero

end Scaled

end CFSG.StandardType.ZS.PrimModel

end
