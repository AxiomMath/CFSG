module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4DiagPSL
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputs811CoordDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4

open Matrix CFSG.Open

variable {K : Type} [Field K]

private theorem permMatrix_orthogonal_entries (σ : Equiv.Perm (Fin 4)) :
    (σ.permMatrix K)ᵀ * σ.permMatrix K = 1 ∧ σ.permMatrix K * (σ.permMatrix K)ᵀ = 1 ∧
      ∀ i j, σ.permMatrix K i j = 0 ∨ σ.permMatrix K i j = 1 := by
  refine ⟨?_, ?_, fun i j => ?_⟩
  · rw [transpose_permMatrix, ← permMatrix_mul, mul_inv_cancel, permMatrix_one]
  · rw [transpose_permMatrix, ← permMatrix_mul, inv_mul_cancel, permMatrix_one]
  · rw [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs <;> simp

private theorem permMatrix_mul_diagonal_mul_transpose (σ : Equiv.Perm (Fin 4)) (d : Fin 4 → K) :
    σ.permMatrix K * Matrix.diagonal d * (σ.permMatrix K)ᵀ =
      Matrix.diagonal fun i => d (σ i) := by
  rw [transpose_permMatrix, Equiv.Perm.permMatrix, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv, Matrix.submatrix_submatrix]
  rw [Equiv.Perm.inv_def, Equiv.symm_symm]
  simp only [Function.comp_id, Function.id_comp]
  exact Matrix.submatrix_diagonal_equiv d σ

private theorem exists_diag_sign_fix {ε : K} (hε : ε * ε = 1) :
    ∃ t : Fin 4 → K, (∀ k, t k * t k = 1) ∧ ∏ k, t k = ε ∧ ∀ k, t k = 1 ∨ t k = ε := by
  refine ⟨![ε, 1, 1, 1], fun k => ?_, ?_, fun k => ?_⟩
  · fin_cases k <;> simp [hε]
  · simp [Fin.prod_univ_four]
  · fin_cases k <;> simp

private theorem exists_det_one_signed_of_orthogonal {S : Matrix (Fin 4) (Fin 4) K}
    (h1 : Sᵀ * S = 1) (h2 : S * Sᵀ = 1) (hent : ∀ i j, S i j = 0 ∨ S i j = 1) :
    ∃ n : Matrix (Fin 4) (Fin 4) K, n.det = 1 ∧ nᵀ * n = 1 ∧ n * nᵀ = 1 ∧
      (∀ i j, n i j = 0 ∨ n i j = 1 ∨ n i j = -1) ∧
      ∀ d : Fin 4 → K, n * Matrix.diagonal d * nᵀ = S * Matrix.diagonal d * Sᵀ := by
  have hε2 : S.det * S.det = 1 := by
    have h := congrArg Matrix.det h2
    rwa [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
  have hε' : S.det = 1 ∨ S.det = -1 := mul_self_eq_one_iff.mp hε2
  obtain ⟨t, ht2, htprod, ht1⟩ := exists_diag_sign_fix hε2
  have hDD : Matrix.diagonal t * Matrix.diagonal t = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext k
    exact ht2 k
  refine ⟨S * Matrix.diagonal t, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul, Matrix.det_diagonal, htprod]
    exact hε2
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc Sᵀ, h1, Matrix.one_mul, hDD]
  · rw [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal t), hDD, Matrix.one_mul, h2]
  · intro i j
    rw [Matrix.mul_diagonal]
    rcases hent i j with h | h <;> rcases ht1 j with h' | h' <;> rcases hε' with h'' | h'' <;>
      simp [h, h', h'']
  · intro d
    have hdd : Matrix.diagonal t * Matrix.diagonal d * Matrix.diagonal t =
        Matrix.diagonal d := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext k
      calc t k * d k * t k = d k * (t k * t k) := by ring
        _ = d k := by rw [ht2 k, mul_one]
    calc S * Matrix.diagonal t * Matrix.diagonal d * (S * Matrix.diagonal t)ᵀ
        = S * (Matrix.diagonal t * Matrix.diagonal d * Matrix.diagonal t) * Sᵀ := by
          rw [Matrix.transpose_mul, Matrix.diagonal_transpose]; simp only [Matrix.mul_assoc]
      _ = S * Matrix.diagonal d * Sᵀ := by rw [hdd]

theorem exists_signedPermMatrix (σ : Equiv.Perm (Fin 4)) :
    ∃ n : Matrix (Fin 4) (Fin 4) K, n.det = 1 ∧ nᵀ * n = 1 ∧ n * nᵀ = 1 ∧
      (∀ i j, n i j = 0 ∨ n i j = 1 ∨ n i j = -1) ∧
      ∀ d : Fin 4 → K, n * Matrix.diagonal d * nᵀ = Matrix.diagonal fun i => d (σ i) := by
  obtain ⟨h1, h2, hent⟩ := permMatrix_orthogonal_entries (K := K) σ
  obtain ⟨n, hdet, hn1, hn2, hnent, hnconj⟩ := exists_det_one_signed_of_orthogonal h1 h2 hent
  exact ⟨n, hdet, hn1, hn2, hnent,
    fun d => (hnconj d).trans (permMatrix_mul_diagonal_mul_transpose σ d)⟩

theorem exists_signedPerm_conj_stdDiagHom (ζ : CubeRoot K) (σ : Equiv.Perm (Fin 4)) :
    ∃ n : GL (Fin 4) K, (n : Matrix (Fin 4) (Fin 4) K).det = 1 ∧
      (n : Matrix (Fin 4) (Fin 4) K)ᵀ * (n : Matrix (Fin 4) (Fin 4) K) = 1 ∧
      (∀ i j, (n : Matrix (Fin 4) (Fin 4) K) i j = 0 ∨ (n : Matrix (Fin 4) (Fin 4) K) i j = 1 ∨
        (n : Matrix (Fin 4) (Fin 4) K) i j = -1) ∧
      ∀ v : Multiplicative (Fin 4 → ZMod 3), n * stdDiagHom ζ v * n⁻¹ =
        stdDiagHom ζ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)) := by
  obtain ⟨n, hdet, hTn, hnT, hent, hconj⟩ := exists_signedPermMatrix (K := K) σ
  refine ⟨⟨n, nᵀ, hnT, hTn⟩, hdet, hTn, hent, fun v => ?_⟩
  apply Units.ext
  have h1 : (((⟨n, nᵀ, hnT, hTn⟩ : GL (Fin 4) K) * stdDiagHom ζ v *
      (⟨n, nᵀ, hnT, hTn⟩ : GL (Fin 4) K)⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      n * Matrix.diagonal (fun i => (ζ.pow (Multiplicative.toAdd v i -
        ∑ j, Multiplicative.toAdd v j) : K)) * nᵀ := rfl
  rw [h1, hconj]
  change _ = Matrix.diagonal (fun i => (ζ.pow (Multiplicative.toAdd v (σ i) -
    ∑ j, Multiplicative.toAdd v (σ j)) : K))
  congr 1
  funext i
  rw [Equiv.sum_comp σ (Multiplicative.toAdd v)]

theorem neg_one_pow_eq_neg_one_of_card_eq_sq [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) :
    (-1 : K) ^ q = -1 := by
  rcases Nat.even_or_odd q with hq | hq
  · have hchar : ringChar K = 2 := by
      haveI := Fintype.ofFinite K
      rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, hK]
      exact Nat.even_iff.mp (Nat.even_pow.mpr ⟨hq, by norm_num⟩)
    have h1 : (-1 : K) = 1 := neg_one_eq_one_iff.mpr hchar
    rw [h1, one_pow]
  · exact hq.neg_one_pow

theorem mem_statedSU_of_signedPerm {q : ℕ} (hq : q ≠ 0) (hneg : (-1 : K) ^ q = -1)
    {n : GL (Fin 4) K} (hdet : (n : Matrix (Fin 4) (Fin 4) K).det = 1)
    (horth : (n : Matrix (Fin 4) (Fin 4) K)ᵀ * (n : Matrix (Fin 4) (Fin 4) K) = 1)
    (hent : ∀ i j, (n : Matrix (Fin 4) (Fin 4) K) i j = 0 ∨
      (n : Matrix (Fin 4) (Fin 4) K) i j = 1 ∨ (n : Matrix (Fin 4) (Fin 4) K) i j = -1) :
    n ∈ StatedSU 4 q K := by
  refine Subgroup.subset_closure ⟨hdet, ?_⟩
  have hfix : (n : Matrix (Fin 4) (Fin 4) K).map (· ^ q) = (n : Matrix (Fin 4) (Fin 4) K) := by
    ext i j
    rcases hent i j with h | h | h <;> simp [h, hq, hneg]
  rw [hfix]
  exact horth

theorem d₀_le_statedSU {q : ℕ} (h3 : 3 ∣ q + 1) (ζ : CubeRoot K) :
    D₀ ζ ≤ StatedSU 4 q K := by
  have hq : q ≠ 0 := by omega
  rintro x ⟨v, rfl⟩
  refine Subgroup.subset_closure ⟨det_stdDiagHom ζ v, ?_⟩
  have hcoe : ((stdDiagHom ζ v : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal (fun i => (ζ.pow (Multiplicative.toAdd v i -
        ∑ j, Multiplicative.toAdd v j) : K)) := rfl
  rw [hcoe, Matrix.diagonal_map (by simp [zero_pow hq]), Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  obtain ⟨m, hm⟩ := h3
  have h3' : ((ζ.pow (Multiplicative.toAdd v i - ∑ j, Multiplicative.toAdd v j) : Kˣ) : K) ^ 3
      = 1 := by
    rw [← Units.val_pow_eq_pow_val]
    simp only [CubeRoot.pow]
    rw [← pow_mul, mul_comm, pow_mul, ζ.pow_three, one_pow, Units.val_one]
  rw [← pow_succ, hm, pow_mul, h3', one_pow]

private theorem stdDiagHomH_eq_one_iff (ζ : CubeRoot K) {H : Subgroup (GL (Fin 4) K)}
    (hD : D₀ ζ ≤ H) (v : Multiplicative (Fin 4 → ZMod 3)) :
    stdDiagHomH ζ hD v = 1 ↔ ∃ t : ZMod 3, Multiplicative.toAdd v = fun _ => t := by
  have hv : stdDiagHomH ζ hD v = 1 ↔ stdDiagHom ζ v = 1 := by
    rw [← OneMemClass.coe_eq_one]
    rfl
  rw [hv, card_D₀_stdDiagHom_eq_one_iff]
  have key : ∀ w : Fin 4 → ZMod 3, (∀ i, w i = ∑ j, w j) ↔ ∃ t : ZMod 3, w = fun _ => t := by
    decide +kernel
  exact key _

private theorem exists_perm_of_mem_normalizer_stdDiagHomH (ζ : CubeRoot K)
    {H : Subgroup (GL (Fin 4) K)} (hD : D₀ ζ ≤ H) {n : H}
    (hn : n ∈ Subgroup.normalizer (((D₀ ζ).subgroupOf H : Subgroup H) : Set H)) :
    ∃ ρ : Equiv.Perm (Fin 4), ∀ v : Multiplicative (Fin 4 → ZMod 3),
      n * stdDiagHomH ζ hD v * n⁻¹ =
        stdDiagHomH ζ hD (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (ρ i)) := by
  have hg : ((n : H) : GL (Fin 4) K) ∈
      Subgroup.normalizer ((D₀ ζ : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K)) := by
    have hmem : n ∈ (Subgroup.normalizer
        ((D₀ ζ : Subgroup (GL (Fin 4) K)) : Set (GL (Fin 4) K))).subgroupOf H := by
      rw [Subgroup.subgroupOf_normalizer_eq hD]
      exact hn
    exact (Subgroup.mem_subgroupOf).mp hmem
  obtain ⟨ρ, hρ⟩ := monomial_of_normalizes ζ hg
  refine ⟨ρ, fun v => ?_⟩
  apply Subtype.ext
  simpa [stdDiagHomH] using hρ v

theorem isSumZeroCoords_stdDiagHomH (ζ : CubeRoot K) {H : Subgroup (GL (Fin 4) K)}
    (hD : D₀ ζ ≤ H)
    (hreal : ∀ σ : Equiv.Perm (Fin 4), ∃ n ∈ H, ∀ v : Multiplicative (Fin 4 → ZMod 3),
      n * stdDiagHom ζ v * n⁻¹ =
        stdDiagHom ζ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i))) :
    IsSumZeroCoords ((D₀ ζ).subgroupOf H) (stdDiagHomH ζ hD) := by
  refine ⟨(MonoidHom.subgroupOf_range_eq_of_le (stdDiagHom ζ) hD).symm,
    stdDiagHomH_eq_one_iff ζ hD, fun n hn => exists_perm_of_mem_normalizer_stdDiagHomH ζ hD hn,
    fun σ => ?_⟩
  obtain ⟨n, hnH, hn⟩ := hreal σ
  refine ⟨⟨n, hnH⟩, fun v => ?_⟩
  apply Subtype.ext
  simpa [stdDiagHomH] using hn v

theorem exists_realizer_statedSL (ζ : CubeRoot K) (σ : Equiv.Perm (Fin 4)) :
    ∃ n ∈ StatedSL 4 K, ∀ v : Multiplicative (Fin 4 → ZMod 3),
      n * stdDiagHom ζ v * n⁻¹ =
        stdDiagHom ζ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)) := by
  obtain ⟨n, hdet, -, -, hn⟩ := exists_signedPerm_conj_stdDiagHom ζ σ
  exact ⟨n, StatedAPI.mem_statedSL_of_det hdet, hn⟩

theorem exists_realizer_statedSU {q : ℕ} (hq : q ≠ 0) (hneg : (-1 : K) ^ q = -1)
    (ζ : CubeRoot K) (σ : Equiv.Perm (Fin 4)) :
    ∃ n ∈ StatedSU 4 q K, ∀ v : Multiplicative (Fin 4 → ZMod 3),
      n * stdDiagHom ζ v * n⁻¹ =
        stdDiagHom ζ (Multiplicative.ofAdd fun i => Multiplicative.toAdd v (σ i)) := by
  obtain ⟨n, hdet, horth, hent, hn⟩ := exists_signedPerm_conj_stdDiagHom ζ σ
  exact ⟨n, mem_statedSU_of_signedPerm hq hneg hdet horth hent, hn⟩

theorem isSumZeroCoords_statedSL [Finite K] (ζ : CubeRoot K) :
    IsSumZeroCoords ((D₀ ζ).subgroupOf (StatedSL 4 K)) (stdDiagHomH ζ (d₀_le_sl ζ)) := by
  exact isSumZeroCoords_stdDiagHomH ζ (d₀_le_sl ζ) (exists_realizer_statedSL ζ)

theorem isSumZeroCoords_statedSU {q : ℕ} (hneg : (-1 : K) ^ q = -1)
    (h3 : 3 ∣ q + 1) (ζ : CubeRoot K) :
    IsSumZeroCoords ((D₀ ζ).subgroupOf (StatedSU 4 q K))
      (stdDiagHomH ζ (d₀_le_statedSU h3 ζ)) := by
  have hq : q ≠ 0 := by omega
  exact isSumZeroCoords_stdDiagHomH ζ (d₀_le_statedSU h3 ζ) (exists_realizer_statedSU hq hneg ζ)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.K6L4
