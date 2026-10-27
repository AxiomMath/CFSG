module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UModel
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UConj
public import CFSG.LocalAnalysis.UniquenessCase.UCInspPair
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LieType.BorelTits.Basic
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
open scoped MatrixGroups

section Core

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem su_cube_facts (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ p ^ f) (hq : p ^ f % 3 = 1)
    {d : SU σ 3} (hd3 : d ^ 3 = 1) (hd1 : d ≠ 1) :
    ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 ∧
      ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 ∧
      conjTr σ ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * antidiag 3 *
        ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = antidiag 3 ∧
      ∀ c : K, ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠
        c • (1 : Matrix (Fin 3) (Fin 3) K) := by
  obtain ⟨hdet, hiso⟩ := mem_SU.1 d.2
  set M : Matrix (Fin 3) (Fin 3) K := ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hM
  have hcube : M * M * M = 1 := by
    have h1 : (d : GL (Fin 3) K) ^ 3 = 1 := by
      have := congrArg (fun x : SU σ 3 => (x : GL (Fin 3) K)) hd3
      simpa using this
    have h2 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [pow_succ] using h2
  refine ⟨hcube, hdet, hiso, ?_⟩
  intro c hc
  have hc3 : c ^ 3 = 1 := by
    have h1 := hcube
    rw [hc] at h1
    have h2 := congrFun (congrFun h1 0) 0
    have h2' : c * (c * c) = 1 := by
      simpa [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_apply] using h2
    linear_combination h2'
  have hcQ : c ^ (p ^ f) = c := by
    obtain ⟨k, hk⟩ : ∃ k, p ^ f = 3 * k + 1 := ⟨(p ^ f) / 3, by omega⟩
    rw [hk, pow_succ, pow_mul, hc3, one_pow, one_mul]
  have hσc : σ c = c := by rw [hσ]; exact hcQ
  have hnorm : σ c * c = 1 := by
    have h4 := hiso
    rw [hc] at h4
    have e : conjTr σ (c • (1 : Matrix (Fin 3) (Fin 3) K)) = σ c • 1 := by
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [conjTr]
      · simp [conjTr, Matrix.one_apply, hij, Ne.symm hij]
    have e2 : (σ c • (1 : Matrix (Fin 3) (Fin 3) K)) * antidiag 3 * (c • 1) =
        (σ c * c) • antidiag 3 := by
      simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
      rw [mul_comm]
    rw [e, e2] at h4
    have h6 : (σ c * c - 1) • (antidiag 3 : Matrix (Fin 3) (Fin 3) K) = 0 := by
      rw [sub_smul, h4, one_smul, sub_self]
    rcases smul_eq_zero.1 h6 with h | h
    · exact sub_eq_zero.1 h
    · exfalso
      apply det_antidiag_three (K := K)
      rw [h]
      exact Matrix.det_zero
  have hc1 : c = 1 := by
    have h7 : c * c = 1 := by rw [hσc] at hnorm; exact hnorm
    linear_combination hc3 - c * h7
  apply hd1
  apply Subtype.ext
  apply Units.ext
  show M = 1
  rw [hc, hc1, one_smul]

theorem inspL3_core_U (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ p ^ f)
    (hσσ : ∀ c : K, σ (σ c) = c) (hf : 1 ≤ f) (hK : Nat.card K = (p ^ f) ^ 2)
    (hq : p ^ f % 3 = 1) (D : Subgroup (SU σ 3)) (hD : Nat.card D = 3) :
    ∃ (ℓ : ℕ) (R : Subgroup (SU σ 3)), ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ InspPair ℓ D R := by
  obtain ⟨ω, hω, hωQ⟩ := exists_cube_root (F := K) hK hq
  have hσω : σ ω = ω := by rw [hσ]; exact hωQ
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_pow_mod_one hf hq
  have hnorm : ∀ c : K, σ c = c → c ≠ 0 → ∃ β : K, σ β * β = c := by
    intro c hc hc0
    obtain ⟨β, hβ⟩ := exists_norm_eq hK (by rw [← hσ]; exact hc) hc0
    exact ⟨β, by rw [hσ]; exact hβ⟩
  obtain ⟨ℓ, S₀, Φ, Z₀, hℓ, hℓ2, hℓ3, hℓN, hS₀h, hS₀d, hΦS, hΦ3, hΦdet, hΦns, hZS, hZℓ, hZne,
    hZdet, hrel⟩ := exists_model_U σ hσ hK hq
  obtain ⟨d, hDd, hd3, hd1⟩ := exists_gen_of_card_three D hD
  obtain ⟨hMcube, hMdet, hMiso, hMns⟩ := su_cube_facts σ hσ hq hd3 hd1
  obtain ⟨B₂, hB₂det, hB₂J, hMB₂⟩ := exists_normalForm σ hσσ h3 hω hσω hnorm (antidiag 3)
    (conjTr_antidiag σ 3) det_antidiag_three _ hMiso hMcube hMdet hMns
  obtain ⟨B₁, hB₁det, hB₁S, hΦB₁⟩ := exists_normalForm σ hσσ h3 hω hσω hnorm S₀ hS₀h hS₀d Φ hΦS
    hΦ3 hΦdet hΦns
  obtain ⟨G₁, hG₁⟩ : ∃ G : GL (Fin 3) K, (G : Matrix (Fin 3) (Fin 3) K) = B₁ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B₁ hB₁det, rfl⟩
  obtain ⟨G₂, hG₂⟩ : ∃ G : GL (Fin 3) K, (G : Matrix (Fin 3) (Fin 3) K) = B₂ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero B₂ hB₂det, rfl⟩
  obtain ⟨Φg, hΦg⟩ : ∃ G : GL (Fin 3) K, (G : Matrix (Fin 3) (Fin 3) K) = Φ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Φ (by rw [hΦdet]; exact one_ne_zero), rfl⟩
  obtain ⟨Z₀g, hZ₀g⟩ : ∃ G : GL (Fin 3) K, (G : Matrix (Fin 3) (Fin 3) K) = Z₀ :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero Z₀ (by rw [hZdet]; exact one_ne_zero), rfl⟩
  obtain ⟨B₁i, hB₁i⟩ : ∃ X : Matrix (Fin 3) (Fin 3) K,
      X = ((G₁⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := ⟨_, rfl⟩
  have hB₁B₁i : B₁ * B₁i = 1 := by rw [hB₁i, ← hG₁]; exact Units.mul_inv G₁
  have hB₁iB₁ : B₁i * B₁ = 1 := by rw [hB₁i, ← hG₁]; exact Units.inv_mul G₁
  obtain ⟨Pg, hPg⟩ : ∃ P : GL (Fin 3) K, P = G₂ * G₁⁻¹ := ⟨_, rfl⟩
  have hPm : (Pg : Matrix (Fin 3) (Fin 3) K) = B₂ * B₁i := by
    rw [hPg, Units.val_mul, hG₂, hB₁i]
  have hmat : ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (B₂ * B₁i) =
      (B₂ * B₁i) * Φ := by
    calc ((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (B₂ * B₁i)
        = (((d : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * B₂) * B₁i :=
          (Matrix.mul_assoc _ _ _).symm
      _ = (B₂ * diagonal ![ω, 1, ω ^ 2]) * B₁i := by rw [hMB₂]
      _ = B₂ * (B₁i * (B₁ * diagonal ![ω, 1, ω ^ 2])) * B₁i := by
          rw [← Matrix.mul_assoc B₁i, hB₁iB₁, Matrix.one_mul]
      _ = B₂ * (B₁i * (Φ * B₁)) * B₁i := by rw [hΦB₁]
      _ = (B₂ * B₁i) * Φ * (B₁ * B₁i) := by simp only [Matrix.mul_assoc]
      _ = (B₂ * B₁i) * Φ := by rw [hB₁B₁i, Matrix.mul_one]
  have hdP : (d : GL (Fin 3) K) * Pg = Pg * Φg := by
    apply Units.ext
    rw [Units.val_mul (d : GL (Fin 3) K) Pg, Units.val_mul Pg Φg, hPm, hΦg]
    exact hmat
  have hcj : (d : GL (Fin 3) K) = Pg * Φg * Pg⁻¹ := eq_mul_inv_of_mul_eq hdP
  have hΦZ : Φg * Z₀g = Z₀g ^ Nat.card K * Φg := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, hΦg, hZ₀g]
    exact hrel
  have hΦZ' : Φg * Z₀g * Φg⁻¹ = Z₀g ^ Nat.card K := by
    rw [mul_inv_eq_iff_eq_mul]
    exact hΦZ
  obtain ⟨Zg, hZg⟩ : ∃ Z : GL (Fin 3) K, Z = Pg * Z₀g * Pg⁻¹ := ⟨_, rfl⟩
  have hdZ : (d : GL (Fin 3) K) * Zg * (d : GL (Fin 3) K)⁻¹ = Zg ^ Nat.card K := by
    have h1 : (d : GL (Fin 3) K) * Zg * (d : GL (Fin 3) K)⁻¹ =
        Pg * (Φg * Z₀g * Φg⁻¹) * Pg⁻¹ := by
      rw [hcj, hZg]
      group
    rw [h1, hΦZ', hZg, conj_pow]
  have hZgmat : (Zg : Matrix (Fin 3) (Fin 3) K) =
      (B₂ * B₁i) * Z₀ * ((Pg⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [hZg, Units.val_mul, Units.val_mul Pg, hPm, hZ₀g]
  have hPPi : (B₂ * B₁i) * ((Pg⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
    rw [← hPm]
    exact Units.mul_inv Pg
  have hKey : conjTr σ (B₂ * B₁i) * antidiag 3 * (B₂ * B₁i) = S₀ :=
    key_isometry σ hB₁B₁i hB₁S hB₂J
  have hZgmem : Zg ∈ SU σ 3 := by
    rw [mem_SU]
    refine ⟨?_, ?_⟩
    · rw [hZgmat, ← hPm, Matrix.det_mul, Matrix.det_mul, hZdet, mul_one, ← Matrix.det_mul,
        Units.mul_inv, Matrix.det_one]
    · rw [hZgmat]
      exact conj_isometry σ hPPi hKey hZS
  obtain ⟨z, hz⟩ : ∃ z : SU σ 3, (z : GL (Fin 3) K) = Zg := ⟨⟨Zg, hZgmem⟩, rfl⟩
  have hZ₀gℓ : Z₀g ^ ℓ = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hZ₀g, hZℓ]
    rfl
  have hz_pow : z ^ ℓ = 1 := by
    apply Subtype.ext
    show (z : GL (Fin 3) K) ^ ℓ = 1
    rw [hz, hZg, conj_pow, hZ₀gℓ, mul_one, mul_inv_cancel]
  have hz_ne : z ≠ 1 := by
    intro h
    apply hZne
    have h1 : Pg * Z₀g * Pg⁻¹ = 1 := by
      rw [← hZg, ← hz]
      exact congrArg Subtype.val h
    have h2 : Z₀g = 1 := by simpa using h1
    have h3' := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2
    rw [← hZ₀g]
    simpa using h3'
  have hdz : d * z * d⁻¹ = z ^ Nat.card K := by
    apply Subtype.ext
    show (d : GL (Fin 3) K) * (z : GL (Fin 3) K) * (d : GL (Fin 3) K)⁻¹ =
      (z : GL (Fin 3) K) ^ Nat.card K
    rw [hz]
    exact hdZ
  have hpair := inspPair_of_triple hℓ hd3 hz_pow hz_ne hdz hℓN
  refine ⟨ℓ, Subgroup.zpowers z, hℓ, hℓ2, hℓ3, ?_⟩
  rw [hDd]
  exact hpair

end Core

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
