module

public import CFSG.RankThree.GroupTheory.SteinbergCETruncatedExpLog

public section

namespace CFSG.RankThree.PartOne.KCExpLog

open Matrix CFSG.RankThree.GroupTheory

variable {K : Type*} [Field K] {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

@[expose] noncomputable def expMat (d : ℕ) (N : Matrix ι ι K) : Matrix ι ι K :=
  ∑ j ∈ Finset.range d, ((j.factorial : K)⁻¹) • N ^ j

theorem map_expMat (Φ : Matrix ι ι K ≃ₐ[K] Matrix κ κ K) (d : ℕ) (N : Matrix ι ι K) :
    Φ (expMat d N) = expMat d (Φ N) := by
  simp only [expMat, map_sum, map_smul, map_pow]

theorem expMat_fin (d : ℕ) (N : Matrix (Fin d) (Fin d) K) : expMat d N = truncExp d N := rfl

theorem expMat_neg_mul_expMat {d : ℕ} (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) {N : Matrix ι ι K} (hN : N ^ d = 0) :
    expMat d (-N) * expMat d N = 1 := by
  set Φ := Matrix.reindexAlgEquiv K K e
  apply Φ.injective
  have h : (Φ N) ^ d = 0 := by rw [← map_pow, hN, map_zero]
  rw [map_mul, map_expMat, map_expMat, map_neg, map_one, expMat_fin, expMat_fin]
  exact truncExp_neg_mul_truncExp hd hK h

theorem expMat_mul_expMat_neg {d : ℕ} (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) {N : Matrix ι ι K} (hN : N ^ d = 0) :
    expMat d N * expMat d (-N) = 1 := by
  have h := expMat_neg_mul_expMat e hd hK (N := -N) (by rw [neg_pow, hN, mul_zero])
  rwa [neg_neg] at h

theorem expMat_injective {d : ℕ} (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) {N₁ N₂ : Matrix ι ι K} (h1 : N₁ ^ d = 0)
    (h2 : N₂ ^ d = 0) (h : expMat d N₁ = expMat d N₂) : N₁ = N₂ := by
  set Φ := Matrix.reindexAlgEquiv K K e
  apply Φ.injective
  have h1' : (Φ N₁) ^ d = 0 := by rw [← map_pow, h1, map_zero]
  have h2' : (Φ N₂) ^ d = 0 := by rw [← map_pow, h2, map_zero]
  have h' : truncExp d (Φ N₁) = truncExp d (Φ N₂) := by
    rw [← expMat_fin, ← expMat_fin, ← map_expMat, ← map_expMat, h]
  calc Φ N₁ = truncLog d (truncExp d (Φ N₁)) := (truncLog_truncExp hd hK h1').symm
    _ = truncLog d (truncExp d (Φ N₂)) := by rw [h']
    _ = Φ N₂ := truncLog_truncExp hd hK h2'

theorem commute_expMat_iff {d : ℕ} (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) {N : Matrix ι ι K} (hN : N ^ d = 0)
    (Y : Matrix ι ι K) : Commute Y (expMat d N) ↔ Commute Y N := by
  set Φ := Matrix.reindexAlgEquiv K K e
  have h : (Φ N) ^ d = 0 := by rw [← map_pow, hN, map_zero]
  have h1 := commute_truncExp_iff hd hK h (Φ Y)
  rw [← expMat_fin, ← map_expMat] at h1
  constructor
  · intro hc
    have : Commute (Φ Y) (Φ N) := h1.mp (hc.map Φ)
    apply Φ.injective
    simpa only [map_mul] using this.eq
  · intro hc
    have : Commute (Φ Y) (Φ (expMat d N)) := h1.mpr (hc.map Φ)
    apply Φ.injective
    simpa only [map_mul] using this.eq

theorem expMat_sub_one_pow {d : ℕ} (e : ι ≃ Fin d) (hd : 1 ≤ d) {N : Matrix ι ι K}
    (hN : N ^ d = 0) : (expMat d N - 1) ^ d = 0 := by
  set Φ := Matrix.reindexAlgEquiv K K e
  apply Φ.injective
  have h : (Φ N) ^ d = 0 := by rw [← map_pow, hN, map_zero]
  rw [map_pow, map_sub, map_expMat, map_one, map_zero, expMat_fin]
  exact truncExp_sub_one_pow hd h

theorem expMat_pow_char {d p : ℕ} [Fact p.Prime] [CharP K p] (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hdp : d ≤ p) {N : Matrix ι ι K} (hN : N ^ d = 0) : expMat d N ^ p = 1 := by
  have hne : Nonempty ι := ⟨e.symm ⟨0, hd⟩⟩
  have h1 : (expMat d N - 1) ^ p = 0 := by
    rw [← Nat.sub_add_cancel hdp, pow_add, expMat_sub_one_pow e hd hN, mul_zero]
  calc expMat d N ^ p = (1 + (expMat d N - 1)) ^ p := by rw [add_sub_cancel]
    _ = 1 ^ p + (expMat d N - 1) ^ p := add_pow_char_of_commute p (Commute.one_left _)
    _ = 1 := by rw [one_pow, h1, add_zero]

theorem expMat_conj (g : (Matrix ι ι K)ˣ) (d : ℕ) (N : Matrix ι ι K) :
    expMat d ((g : Matrix ι ι K) * N * (↑(g⁻¹) : Matrix ι ι K)) =
      g * expMat d N * (↑(g⁻¹) : Matrix ι ι K) := by
  simp only [expMat, Units.conj_pow, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
    smul_mul_assoc]

theorem expMat_map (σ : K →+* K) (d : ℕ) (N : Matrix ι ι K) :
    expMat d (N.map σ) = (expMat d N).map σ := by
  ext i j
  simp only [expMat, ← Matrix.map_pow, Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply,
    smul_eq_mul, map_sum, map_mul, map_inv₀, map_natCast]

theorem transpose_expMat_mul (d : ℕ) {N J : Matrix ι ι K} (hNJ : Nᵀ * J + J * N = 0) :
    (expMat d N)ᵀ * J = J * expMat d (-N) := by
  have hpow : ∀ j : ℕ, (N ^ j)ᵀ * J = ((-1 : K) ^ j) • (J * N ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have h1 : Nᵀ * J = -(J * N) := eq_neg_of_add_eq_zero_left hNJ
      calc (N ^ (j + 1))ᵀ * J = Nᵀ * ((N ^ j)ᵀ * J) := by
            rw [pow_succ, transpose_mul, Matrix.mul_assoc]
        _ = Nᵀ * (((-1 : K) ^ j) • (J * N ^ j)) := by rw [ih]
        _ = ((-1 : K) ^ j) • (Nᵀ * J * N ^ j) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
        _ = ((-1 : K) ^ j) • ((-(J * N)) * N ^ j) := by rw [h1]
        _ = ((-1 : K) ^ (j + 1)) • (J * N ^ (j + 1)) := by
            rw [Matrix.neg_mul, smul_neg, pow_succ (-1 : K) j, mul_neg_one, neg_smul,
              Matrix.mul_assoc, ← pow_succ']
  have hneg : ∀ j : ℕ, (-N) ^ j = ((-1 : K) ^ j) • N ^ j := fun j => by
    rw [← neg_one_smul K N, smul_pow]
  simp only [expMat, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.sum_mul,
    Matrix.smul_mul, hpow, Matrix.mul_sum, Matrix.mul_smul, hneg, smul_smul]

theorem expMat_isometry {d : ℕ} (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) {N J : Matrix ι ι K} (hNJ : Nᵀ * J + J * N = 0)
    (hN : N ^ d = 0) : (expMat d N)ᵀ * J * expMat d N = J := by
  rw [transpose_expMat_mul d hNJ, Matrix.mul_assoc, expMat_neg_mul_expMat e hd hK hN,
    Matrix.mul_one]

@[expose] noncomputable def logMat (d : ℕ) (u : Matrix ι ι K) : Matrix ι ι K :=
  ∑ j ∈ Finset.Ico 1 d, ((-1 : K) ^ (j + 1) * (j : K)⁻¹) • (u - 1) ^ j

theorem map_logMat (Φ : Matrix ι ι K ≃ₐ[K] Matrix κ κ K) (d : ℕ) (u : Matrix ι ι K) :
    Φ (logMat d u) = logMat d (Φ u) := by
  simp only [logMat, map_sum, map_smul, map_pow, map_sub, map_one]

theorem logMat_fin (d : ℕ) (u : Matrix (Fin d) (Fin d) K) : logMat d u = truncLog d u := rfl

theorem expMat_logMat {d : ℕ} (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hK : ∀ n : ℕ, 0 < n → n < d → (n : K) ≠ 0) {u : Matrix ι ι K} (hu : (u - 1) ^ d = 0) :
    expMat d (logMat d u) = u := by
  set Φ := Matrix.reindexAlgEquiv K K e
  apply Φ.injective
  have h : (Φ u - 1) ^ d = 0 := by
    rw [← map_one Φ, ← map_sub, ← map_pow, hu, map_zero]
  rw [map_expMat, map_logMat, expMat_fin, logMat_fin]
  exact truncExp_truncLog hd hK h

theorem logMat_pow_eq_zero {d : ℕ} (e : ι ≃ Fin d) {u : Matrix ι ι K} (hu : (u - 1) ^ d = 0) :
    logMat d u ^ d = 0 := by
  set Φ := Matrix.reindexAlgEquiv K K e
  apply Φ.injective
  have h : (Φ u - 1) ^ d = 0 := by
    rw [← map_one Φ, ← map_sub, ← map_pow, hu, map_zero]
  rw [map_pow, map_logMat, logMat_fin, map_zero]
  exact truncLog_pow h

theorem logMat_skew {d p : ℕ} [Fact p.Prime] [CharP K p] (e : ι ≃ Fin d) (hd : 1 ≤ d)
    (hdp : d ≤ p) {J L u : Matrix ι ι K} (hJL : J * L = 1) (hLJ : L * J = 1)
    (hu : (u - 1) ^ d = 0) (huJ : uᵀ * J * u = J) :
    (logMat d u)ᵀ * J + J * logMat d u = 0 := by
  set Φ := Matrix.reindexAlgEquiv K K e
  have hΦt : ∀ M : Matrix ι ι K, Φ Mᵀ = (Φ M)ᵀ := fun M => by
    simp [Φ, Matrix.coe_reindexAlgEquiv]
  let C : (Matrix (Fin d) (Fin d) K)ˣ := ⟨Φ J, Φ L, by rw [← map_mul, hJL, map_one],
    by rw [← map_mul, hLJ, map_one]⟩
  have hnil : IsNilpotent (Φ u - 1) := by
    refine ⟨d, ?_⟩
    rw [← map_one Φ, ← map_sub, ← map_pow, hu, map_zero]
  have hiso : (Φ u)ᵀ * (C : Matrix (Fin d) (Fin d) K) * Φ u = C := by
    show (Φ u)ᵀ * Φ J * Φ u = Φ J
    rw [← hΦt, ← map_mul, ← map_mul, huJ]
  obtain ⟨-, -, -, -, -, -, -, -, hC⟩ :=
    small_bilinear_isometry_unipotent_logarithm_calculus (K := K) (p := p) hd hdp
  obtain ⟨-, hskew⟩ := (hC C).2 (Φ u) hnil hiso
  have h1 : (↑(C⁻¹) : Matrix (Fin d) (Fin d) K) = Φ L := rfl
  rw [h1, ← logMat_fin] at hskew
  have hskew' : L * (logMat d u)ᵀ * J = -logMat d u := by
    apply Φ.injective
    rw [map_neg, map_mul, map_mul, hΦt, map_logMat]
    exact hskew
  calc (logMat d u)ᵀ * J + J * logMat d u
      = J * (L * (logMat d u)ᵀ * J) + J * logMat d u := by
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJL, Matrix.one_mul]
    _ = 0 := by rw [hskew', Matrix.mul_neg, neg_add_cancel]

end CFSG.RankThree.PartOne.KCExpLog
