module

public import Mathlib.FieldTheory.Finite.Extension

public section

open Matrix

namespace CFSG.Singer

variable {K : Type*} [Field K]

theorem exists_singer_sl [Finite K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (n : ℕ) [NeZero n] {p : ℕ}
    [Fact p.Prime] (hpn : p ∣ (Nat.card K ^ n - 1) / (Nat.card K - 1)) :
    ∃ τ σ : SpecialLinearGroup (Fin n) K, orderOf τ = p ∧ σ * τ * σ⁻¹ = τ ^ Nat.card K := by
  classical
  set E := FiniteField.Extension K ℓ n with hE
  have hfin : Module.finrank K E = n := FiniteField.finrank_extension K ℓ n
  let b := Module.finBasisOfFinrankEq K E hfin
  have hdvd1 : Nat.card K - 1 ∣ Nat.card K ^ n - 1 := Nat.sub_one_dvd_pow_sub_one (Nat.card K) n
  have hpL : p ∣ Nat.card Eˣ := by
    rw [Nat.card_units, hE, FiniteField.natCard_extension]
    exact hpn.trans (Nat.div_dvd_of_dvd hdvd1)
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hpL
  have hyp : (y : E) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hy, pow_orderOf_eq_one, Units.val_one]
  have hnorm : Algebra.norm K (y : E) = 1 := by
    have hcE : Nat.card E = Nat.card K ^ n := FiniteField.natCard_extension K ℓ n
    apply (algebraMap K E).injective
    rw [FiniteField.algebraMap_norm_eq_pow, map_one, hcE]
    obtain ⟨m, hm⟩ := hpn
    rw [hm, pow_mul, hyp, one_pow]
  let τ : SpecialLinearGroup (Fin n) K :=
    ⟨Algebra.leftMulMatrix b (y : E), by rw [← Algebra.norm_eq_matrix_det, hnorm]⟩
  have hτpow : ∀ m : ℕ, ((τ ^ m : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      Algebra.leftMulMatrix b ((y : E) ^ m) := by
    intro m
    rw [SpecialLinearGroup.coe_pow, map_pow]
  have hτord : orderOf τ = p := by
    rw [← hy]
    apply orderOf_eq_orderOf_iff.mpr
    intro m
    constructor
    · intro h
      apply Units.ext
      apply Algebra.leftMulMatrix_injective b
      have h' := congrArg (fun A : SpecialLinearGroup (Fin n) K => (A : Matrix (Fin n) (Fin n) K)) h
      simp only [hτpow, SpecialLinearGroup.coe_one] at h'
      rw [Units.val_pow_eq_pow_val, h', Units.val_one, map_one]
    · intro h
      apply Subtype.ext
      rw [hτpow, SpecialLinearGroup.coe_one, ← Units.val_pow_eq_pow_val, h, Units.val_one, map_one]
  let φ := FiniteField.Extension.frob K ℓ n
  let S₀ : Matrix (Fin n) (Fin n) K := LinearMap.toMatrix b b φ.toLinearMap
  have hS₀ : S₀ * Algebra.leftMulMatrix b (y : E) =
      Algebra.leftMulMatrix b ((y : E) ^ Nat.card K) * S₀ := by
    have hlin : φ.toLinearMap * Algebra.lmul K E (y : E) =
        Algebra.lmul K E ((y : E) ^ Nat.card K) * φ.toLinearMap := by
      apply LinearMap.ext
      intro x
      simp only [φ, Module.End.mul_apply, AlgEquiv.toLinearMap_apply, Algebra.coe_lmul_eq_mul,
        FiniteField.Extension.frob_apply]
      change ((y : E) * x) ^ Nat.card K = (y : E) ^ Nat.card K * x ^ Nat.card K
      exact mul_pow _ _ _
    simp only [S₀, Algebra.leftMulMatrix_apply, ← LinearMap.toMatrix_mul, hlin]
  have hdet₀ : IsUnit S₀.det := by
    have hinv : LinearMap.toMatrix b b φ.symm.toLinearMap * S₀ = 1 := by
      rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_one b]
      congr 1
      apply LinearMap.ext
      intro x
      simp
    exact Matrix.isUnit_det_of_left_inverse hinv
  obtain ⟨y₀, hy₀⟩ := FiniteField.unitsMap_norm_surjective (K := K) (K' := E) hdet₀.unit⁻¹
  have hnorm₀ : Algebra.norm K (y₀ : E) * S₀.det = 1 := by
    have h := congrArg (fun u : Kˣ => (u : K)) hy₀
    simp only [Units.coe_map, MonoidHom.coe_coe] at h
    rw [h]
    exact hdet₀.val_inv_mul
  let σ : SpecialLinearGroup (Fin n) K :=
    ⟨Algebra.leftMulMatrix b (y₀ : E) * S₀, by
      rw [Matrix.det_mul, ← Algebra.norm_eq_matrix_det, hnorm₀]⟩
  refine ⟨τ, σ, hτord, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, hτpow]
  change Algebra.leftMulMatrix b (y₀ : E) * S₀ * Algebra.leftMulMatrix b (y : E) =
    Algebra.leftMulMatrix b ((y : E) ^ Nat.card K) * (Algebra.leftMulMatrix b (y₀ : E) * S₀)
  rw [mul_assoc, hS₀, ← mul_assoc, ← mul_assoc, ← map_mul, ← map_mul, mul_comm]

theorem pow_card_eq_one_of_mem_center {n : ℕ} {A : SpecialLinearGroup (Fin n) K}
    (hA : A ∈ Subgroup.center (SpecialLinearGroup (Fin n) K)) : A ^ n = 1 := by
  obtain ⟨r, hr, hrA⟩ := SpecialLinearGroup.mem_center_iff.mp hA
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_pow, ← hrA, SpecialLinearGroup.coe_one, Fintype.card_fin] at *
  rw [← map_pow, hr, map_one]

end CFSG.Singer

end
