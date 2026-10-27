module

public import CFSG.CGT.Stroth77.L4Sylow.Embed
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Q35K1Hat
import CFSG.CGT.Stroth77.L4Sylow.Center
import CFSG.LocalAnalysis.Mason73.Elements
import TauCeti.LinearAlgebra.Matrix.Diagonal
import CFSG.LocalAnalysis.Mason73.Abelian

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.CGT.Stroth77.L4Sylow CFSG.LocalAnalysis.Mason73 CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv


@[expose] def uc22s2112r34q35_zvec (n : ℕ) : Fin 4 → ZMod (2 ^ n) :=
  ![0, 0, ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n)), ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))]

@[expose] def uc22s2112r34q35_cvec (n : ℕ) : Fin 4 → ZMod (2 ^ n) :=
  fun _ => ((2 ^ (n - 1) : ℕ) : ZMod (2 ^ n))

private theorem uc22s2112r34q35_zvec_eq (n : ℕ) :
    uc22s2112r34q35_zvec n = (fun _ : Fin 4 => hh n) - hv n χz := by
  funext i
  fin_cases i <;> simp [uc22s2112r34q35_zvec, hv, χz, hh]

private theorem uc22s2112r34q35_zvec_sub_pv_isConst {n : ℕ} (hn : 1 ≤ n) (σ : Fin81.R0) :
    IsConst (uc22s2112r34q35_zvec n - pv (σ : Perm (Fin 4)) (uc22s2112r34q35_zvec n)) := by
  have hE : (fun _ : Fin 4 => hh n) - hv n χz -
      pv (σ : Perm (Fin 4)) ((fun _ : Fin 4 => hh n) - hv n χz) =
      -(hv n χz - pv (σ : Perm (Fin 4)) (hv n χz)) := by
    funext i
    change (hh n - hv n χz i) - (hh n - hv n χz ((σ : Perm (Fin 4))⁻¹ i)) =
      -(hv n χz i - hv n χz ((σ : Perm (Fin 4))⁻¹ i))
    ring
  rw [uc22s2112r34q35_zvec_eq, hE, isConst_neg_iff, pv_hv]
  exact (hv_sub_hv_isConst_iff hn χz (fun i => χz ((σ : Perm (Fin 4))⁻¹ i))).2
    (χz_pv_const _ σ.2)

private theorem uc22s2112r34q35_hat_zvec_mul {n : ℕ} (hn : 1 ≤ n) (b : L4Hat n) :
    ∃ c : Fin 4 → ZMod (2 ^ n), IsConst c ∧
      hat (uc22s2112r34q35_zvec n) 1 * b =
        hat c 1 * (b * hat (uc22s2112r34q35_zvec n) 1) := by
  refine ⟨uc22s2112r34q35_zvec n - pv (b.right : Perm (Fin 4))
      (uc22s2112r34q35_zvec n), uc22s2112r34q35_zvec_sub_pv_isConst hn b.right, ?_⟩
  rw [← hat_left b]
  rw [hat_mul, hat_mul, hat_mul]
  simp only [OneMemClass.coe_one, one_mul, mul_one, pv_one]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    simp only
    ring
  · rfl

private theorem uc22s2112r34q35_zeta_hh {K : Type} [Field K] {n : ℕ} (D : L4Data K n)
    (hn : 1 ≤ n) : (D.ζ : K) ^ (hh n).val = -1 := by
  have h := D.chi_signZ hn (-1)
  rw [signZ_neg_one, D.chi_apply, Units.val_pow_eq_pow_val] at h
  simpa using h

private theorem uc22s2112r34q35_embed_zvec {K : Type} [Field K] {n : ℕ} (D : L4Data K n)
    (hn : 1 ≤ n) :
    ((D.embed (hat (uc22s2112r34q35_zvec n) 1) : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![1, 1, -1, -1] := by
  rw [D.coe_embed]
  simp only [OneMemClass.coe_one, inv_one,
    Matrix.permMatrix_one, mul_one]
  have hzeta : (D.ζ : K) ^ (((2 : ZMod (2 ^ n)) ^ (n - 1))).val = -1 := by
    simpa only [hh, Nat.cast_pow, Nat.cast_ofNat] using uc22s2112r34q35_zeta_hh D hn
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uc22s2112r34q35_zvec]
  all_goals exact hzeta

private theorem uc22s2112r34q35_embed_cvec {K : Type} [Field K] {n : ℕ} (D : L4Data K n)
    (hn : 1 ≤ n) :
    D.embed (hat (uc22s2112r34q35_cvec n) 1) = -1 := by
  apply Units.ext
  rw [D.coe_embed]
  simp only [OneMemClass.coe_one, inv_one,
    Matrix.permMatrix_one, mul_one]
  have hcvec : (fun i : Fin 4 => (D.ζ : K) ^ (Multiplicative.toAdd
      (Multiplicative.ofAdd (uc22s2112r34q35_cvec n)) i).val) =
      fun _ : Fin 4 => (-1 : K) := by
    funext i
    simpa only [uc22s2112r34q35_cvec, toAdd_ofAdd, hh]
      using uc22s2112r34q35_zeta_hh D hn
  rw [hcvec]
  have hneg1 : (-1 : Matrix (Fin 4) (Fin 4) K) = Matrix.diagonal (fun _ => (-1 : K)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  exact hneg1.symm

private theorem uc22s2112r34q35_neg_one_ne_one {K : Type} [Field K] {n : ℕ}
    (D : L4Data K n) (hn : 2 ≤ n) : (-1 : K) ≠ 1 := by
  intro h
  have h1 : (D.ζ : K) ^ (2 ^ (n - 1)) = 1 := by
    rw [D.zeta_pow_two_pow_pred (by omega), h]
  have h2 : D.ζ ^ (2 ^ (n - 1)) = 1 :=
    Units.ext (by rw [Units.val_pow_eq_pow_val, h1, Units.val_one])
  rw [← orderOf_dvd_iff_pow_eq_one, D.orderOf_ζ] at h2
  have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
  exact absurd (Nat.le_of_dvd (by positivity) h2) (not_le.mpr hlt)

private def uc22s2112r34q35_blk4 {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

private theorem uc22s2112r34q35_blk4_mul {K : Type} [Field K]
    (A A' B B' : Matrix (Fin 2) (Fin 2) K) :
    uc22s2112r34q35_blk4 A B * uc22s2112r34q35_blk4 A' B' =
      uc22s2112r34q35_blk4 (A * A') (B * B') := by
  rw [uc22s2112r34q35_blk4, uc22s2112r34q35_blk4, uc22s2112r34q35_blk4,
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

private theorem uc22s2112r34q35_blk4_one {K : Type} [Field K] :
    uc22s2112r34q35_blk4 (1 : Matrix (Fin 2) (Fin 2) K) 1 = 1 := by
  rw [uc22s2112r34q35_blk4, Matrix.fromBlocks_one, Matrix.reindex_apply,
    Matrix.submatrix_one_equiv]

private theorem uc22s2112r34q35_blk4_inj {K : Type} [Field K]
    {A A' B B' : Matrix (Fin 2) (Fin 2) K}
    (h : uc22s2112r34q35_blk4 A B = uc22s2112r34q35_blk4 A' B') : A = A' ∧ B = B' := by
  have h' := (Matrix.reindex finSumFinEquiv finSumFinEquiv).injective h
  obtain ⟨hA, -, -, hB⟩ := Matrix.fromBlocks_inj.mp h'
  exact ⟨hA, hB⟩

private theorem uc22s2112r34q35_blk4_pow {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (k : ℕ) :
    (uc22s2112r34q35_blk4 A B) ^ k =
      uc22s2112r34q35_blk4 (A ^ k) (B ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, uc22s2112r34q35_blk4_one]
  | succ k ih => rw [pow_succ, ih, uc22s2112r34q35_blk4_mul, pow_succ, pow_succ]

private theorem uc22s2112r34q35_blk4_castAdd_castAdd {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    uc22s2112r34q35_blk4 A B (Fin.castAdd 2 i) (Fin.castAdd 2 j) = A i j := by
  rw [uc22s2112r34q35_blk4, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₁₁]

private theorem uc22s2112r34q35_blk4_natAdd_natAdd {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    uc22s2112r34q35_blk4 A B (Fin.natAdd 2 i) (Fin.natAdd 2 j) = B i j := by
  rw [uc22s2112r34q35_blk4, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₂₂]

private theorem uc22s2112r34q35_blk4_castAdd_natAdd {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    uc22s2112r34q35_blk4 A B (Fin.castAdd 2 i) (Fin.natAdd 2 j) = 0 := by
  rw [uc22s2112r34q35_blk4, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₂]
  simp

private theorem uc22s2112r34q35_blk4_natAdd_castAdd {K : Type} [Field K]
    (A B : Matrix (Fin 2) (Fin 2) K) (i j : Fin 2) :
    uc22s2112r34q35_blk4 A B (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0 := by
  rw [uc22s2112r34q35_blk4, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_natAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₂₁]
  simp

theorem uc22s2112r34q35_eq_one_of_normalizes_embed {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 2 ≤ n) (D : L4Data K n) (R : Subgroup (L4Hat n)) {e₁ e₂ : Fin 4 → ZMod (2 ^ n)}
    (hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) e₁ - e₁) ∨ ¬ IsConst (pv (π : Perm (Fin 4)) e₂ - e₂))
    (he₁ : hat e₁ 1 ∈ R) (he₂ : hat e₂ 1 ∈ R) {y₀₁ y₂₃ y₀₂ : L4Hat n} (hy₀₁ : y₀₁ ∈ R)
    (hy₂₃ : y₂₃ ∈ R) (hy₀₂ : y₀₂ ∈ R) (h₀₁ : y₀₁.right = uc22s2112r34q35_r01)
    (h₂₃ : y₂₃.right = uc22s2112r34q35_r23) (h₀₂ : y₀₂.right = uc22s2112r34q35_r02)
    (hz : hat (uc22s2112r34q35_zvec n) 1 ∈ R) {h : GL (Fin 4) K} {s : ℕ} (hs : s.Prime)
    (hs2 : s ≠ 2) (hh : h ^ s = 1) (hGL : ¬ s ∣ Nat.card (GL (Fin 2) K))
    (hN : ∀ a ∈ R, ∃ a' ∈ R, h * D.embed a * h⁻¹ = D.embed a')
    (hN' : ∀ a ∈ R, ∃ a' ∈ R, h⁻¹ * D.embed a * h = D.embed a') : h = 1 := by
  have hneg : (-1 : K) ≠ 1 := uc22s2112r34q35_neg_one_ne_one D hn
  obtain ⟨a₀, ha₀R, hconj⟩ := hN (hat (uc22s2112r34q35_zvec n) 1) hz
  have hcomm : ∀ b ∈ R, uc22s2112r34q35_CommConst a₀ b := by
    intro b hb
    obtain ⟨b', hb'R, hb'conj⟩ := hN' b hb
    have hb'conj' : h * D.embed b' * h⁻¹ = D.embed b := by
      calc h * D.embed b' * h⁻¹ = h * (h⁻¹ * D.embed b * h) * h⁻¹ := by rw [hb'conj]
        _ = D.embed b := by group
    obtain ⟨c, hc_const, hc_step⟩ :=
      uc22s2112r34q35_hat_zvec_mul (by omega) b'
    have hEc_mem : D.embed (hat c 1) ∈ CFSG.Open.StatedScalars (Fin 4) K := by
      rw [D.embed_mem_statedScalars_iff]
      exact ⟨rfl, fun i j => hc_const i j⟩
    have hEc_center : D.embed (hat c 1) ∈ Subgroup.center (GL (Fin 4) K) := by
      rw [← CFSG.Open.StatedAPI.statedScalars_eq_center]
      exact hEc_mem
    have hEc_comm (g : GL (Fin 4) K) :
        D.embed (hat c 1) * g = g * D.embed (hat c 1) :=
      ((Subgroup.mem_center_iff.mp hEc_center) g).symm
    have hEc_conj : h * D.embed (hat c 1) * h⁻¹ = D.embed (hat c 1) := by
      calc h * D.embed (hat c 1) * h⁻¹ = (D.embed (hat c 1) * h) * h⁻¹ := by
            rw [← hEc_comm h]
        _ = D.embed (hat c 1) := by group
    have hmat : D.embed a₀ * D.embed b =
        D.embed (hat c 1) * (D.embed b * D.embed a₀) := by
      calc D.embed a₀ * D.embed b
          = (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹) *
              (h * D.embed b' * h⁻¹) := by rw [hconj, hb'conj']
        _ = h * (D.embed (hat (uc22s2112r34q35_zvec n) 1) * D.embed b') * h⁻¹ := by
              group
        _ = h * D.embed (hat (uc22s2112r34q35_zvec n) 1 * b') * h⁻¹ := by
              rw [← map_mul]
        _ = h * D.embed (hat c 1 * (b' * hat (uc22s2112r34q35_zvec n) 1)) * h⁻¹ := by
              rw [hc_step]
        _ = h * (D.embed (hat c 1) *
              (D.embed b' * D.embed (hat (uc22s2112r34q35_zvec n) 1))) * h⁻¹ := by
              rw [map_mul, map_mul]
        _ = D.embed (hat c 1) *
              ((h * D.embed b' * h⁻¹) *
                (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹)) := by
              rw [show h * (D.embed (hat c 1) *
                    (D.embed b' * D.embed (hat (uc22s2112r34q35_zvec n) 1))) * h⁻¹ =
                  (h * D.embed (hat c 1) * h⁻¹) *
                    ((h * D.embed b' * h⁻¹) *
                      (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹)) by
                    group,
                hEc_conj]
        _ = D.embed (hat c 1) * (D.embed b * D.embed a₀) := by
              rw [hb'conj', hconj]
    refine ⟨c, hc_const, D.embed_injective ?_⟩
    calc D.embed (a₀ * b) = D.embed a₀ * D.embed b := map_mul _ _ _
      _ = D.embed (hat c 1) * (D.embed b * D.embed a₀) := hmat
      _ = D.embed (hat c 1 * (b * a₀)) := by rw [← map_mul, ← map_mul]
  obtain ⟨ha₀right, hd01, hd23, hd2⟩ :=
    uc22s2112r34q35_hat_shape_of_commConst hn hsep h₀₁ h₂₃ h₀₂
      (hcomm _ he₁) (hcomm _ he₂) (hcomm _ hy₀₁) (hcomm _ hy₂₃) (hcomm _ hy₀₂)
  set d := Multiplicative.toAdd a₀.left with hd
  have ha₀eq : a₀ = hat d 1 := by
    rw [← hat_left a₀, ha₀right]
  let u : Kˣ := D.chi (Multiplicative.ofAdd (d 0))
  let v : Kˣ := D.chi (Multiplicative.ofAdd (d 2))
  have hEaMat : ((D.embed a₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      Matrix.diagonal ![(u : K), (u : K), (v : K), (v : K)] := by
    rw [ha₀eq, D.coe_embed]
    simp only [OneMemClass.coe_one, inv_one,
      Matrix.permMatrix_one, mul_one]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [u, v, D.chi_apply, Units.val_pow_eq_pow_val, hd01, hd23]
  have hdd : d 0 + d 0 = d 2 + d 2 := by
    linear_combination hd2
  have huv2 : u ^ 2 = v ^ 2 := by
    calc u ^ 2 = D.chi (Multiplicative.ofAdd (d 0 + d 0)) := by
          change D.chi (Multiplicative.ofAdd (d 0)) ^ 2 = _
          rw [← map_pow]
          congr 1
          rw [pow_two, ← ofAdd_add]
      _ = D.chi (Multiplicative.ofAdd (d 2 + d 2)) := by rw [hdd]
      _ = v ^ 2 := by
          change _ = D.chi (Multiplicative.ofAdd (d 2)) ^ 2
          rw [← map_pow]
          congr 1
          rw [pow_two, ← ofAdd_add]
  have hratio : (v * u⁻¹) ^ 2 = 1 := by
    rw [mul_pow, inv_pow, huv2]
    exact mul_inv_cancel (v ^ 2)
  have hratioK : ((v : K) * (u : K)⁻¹) ^ 2 = 1 := by
    have hcoe : ((v : K) * (u : K)⁻¹) = ((v * u⁻¹ : Kˣ) : K) := by
      rw [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [hcoe, ← Units.val_pow_eq_pow_val, hratio, Units.val_one]
  rcases sq_eq_one_iff.mp hratioK with hvu | hvu
  ·
    have hv_eq : (v : K) = (u : K) := by
      have h1 := congrArg (fun x : K => x * (u : K)) hvu
      simpa [mul_assoc, u.ne_zero] using h1
    have ha₀_scalar : D.embed a₀ = Matrix.GeneralLinearGroup.scalar (Fin 4) u := by
      apply Units.ext
      rw [hEaMat]
      have hvec : (![(u : K), (u : K), (v : K), (v : K)] : Fin 4 → K) =
        fun _ => (u : K) := by
        funext i
        fin_cases i <;> simp [hv_eq]
      rw [hvec, Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply]
    have hEa_comm (g : GL (Fin 4) K) :
        D.embed a₀ * g = g * D.embed a₀ := by
      rw [ha₀_scalar]
      exact Matrix.GeneralLinearGroup.scalar_commute u g
    have hEz_eq : D.embed (hat (uc22s2112r34q35_zvec n) 1) = D.embed a₀ := by
      calc D.embed (hat (uc22s2112r34q35_zvec n) 1) =
          h⁻¹ * (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹) * h := by
            group
        _ = h⁻¹ * D.embed a₀ * h := by rw [hconj]
        _ = D.embed a₀ := by
            calc h⁻¹ * D.embed a₀ * h = h⁻¹ * (D.embed a₀ * h) := by group
              _ = h⁻¹ * (h * D.embed a₀) := by rw [hEa_comm h]
              _ = D.embed a₀ := by group
    have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K)) hEz_eq) 0) 0
    have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin 4) K =>
      (g : Matrix (Fin 4) (Fin 4) K)) hEz_eq) 2) 2
    rw [uc22s2112r34q35_embed_zvec D (by omega), hEaMat] at h1 h2
    simp [hv_eq] at h1 h2
    exact absurd (h2.trans h1.symm) hneg
  ·
    have hv_eq : (v : K) = -(u : K) := by
      have h1 := congrArg (fun x : K => x * (u : K)) hvu
      simpa [mul_assoc, u.ne_zero] using h1
    have hEa_eq : D.embed a₀ = Matrix.GeneralLinearGroup.scalar (Fin 4) u *
        D.embed (hat (uc22s2112r34q35_zvec n) 1) := by
      apply Units.ext
      rw [hEaMat, Units.val_mul, uc22s2112r34q35_embed_zvec D (by omega),
        Matrix.GeneralLinearGroup.coe_scalar]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.scalar_apply, hv_eq]
    set S : GL (Fin 4) K := Matrix.GeneralLinearGroup.scalar (Fin 4) u with hS
    have hEz_conj : h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹ =
        S * D.embed (hat (uc22s2112r34q35_zvec n) 1) := by
      rw [← hEa_eq]
      exact hconj
    have hS_comm (g : GL (Fin 4) K) : S * g = g * S :=
      Matrix.GeneralLinearGroup.scalar_commute u g
    have hS_conj : h * S * h⁻¹ = S := by
      calc h * S * h⁻¹ = (S * h) * h⁻¹ := by rw [hS_comm h]
        _ = S := by group
    have hSk : ∀ k : ℕ, h * S ^ k * h⁻¹ = S ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc h * S ^ (k + 1) * h⁻¹ =
              (h * S ^ k * h⁻¹) * (h * S * h⁻¹) := by group
            _ = S ^ k * S := by rw [ih, hS_conj]
            _ = S ^ (k + 1) := by rw [pow_succ]
    have hpow : ∀ k : ℕ,
        h ^ k * D.embed (hat (uc22s2112r34q35_zvec n) 1) * (h⁻¹) ^ k =
          S ^ k * D.embed (hat (uc22s2112r34q35_zvec n) 1) := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
          calc h ^ (k + 1) * D.embed (hat (uc22s2112r34q35_zvec n) 1) *
                (h⁻¹) ^ (k + 1) =
              h * (h ^ k * D.embed (hat (uc22s2112r34q35_zvec n) 1) *
                (h⁻¹) ^ k) * h⁻¹ := by group
            _ = h * (S ^ k * D.embed (hat (uc22s2112r34q35_zvec n) 1)) * h⁻¹ := by
                rw [ih]
            _ = S ^ k * (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹) := by
                rw [show h * (S ^ k * D.embed (hat (uc22s2112r34q35_zvec n) 1)) * h⁻¹ =
                  (h * S ^ k * h⁻¹) *
                    (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹) by group,
                  hSk k]
            _ = S ^ k * (S * D.embed (hat (uc22s2112r34q35_zvec n) 1)) := by
                rw [hEz_conj]
            _ = S ^ (k + 1) * D.embed (hat (uc22s2112r34q35_zvec n) 1) := by
                rw [pow_succ]
                group
    have hSs : S ^ s = 1 := by
      have h1 := hpow s
      rw [hh, inv_pow, hh, inv_one, one_mul, mul_one] at h1
      have h2 := congrArg (fun x : GL (Fin 4) K =>
        x * (D.embed (hat (uc22s2112r34q35_zvec n) 1))⁻¹) h1
      simpa [mul_assoc] using h2.symm
    have hus : u ^ s = 1 := by
      have h1 : Matrix.GeneralLinearGroup.scalar (Fin 4) (u ^ s) = 1 := by
        rw [map_pow, ← hS]
        exact hSs
      have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin 4) K =>
        (g : Matrix (Fin 4) (Fin 4) K)) h1) 0) 0
      rw [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one,
        Matrix.scalar_apply, Matrix.one_apply] at h2
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, Units.val_one]
      exact h2
    have hEz_sq : D.embed (hat (uc22s2112r34q35_zvec n) 1) ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, uc22s2112r34q35_embed_zvec D (by omega),
        Units.val_one, pow_two, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simp
    have hEa_sq : D.embed a₀ ^ 2 = 1 := by
      rw [pow_two]
      calc D.embed a₀ * D.embed a₀ =
          (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹) *
            (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹) := by rw [hconj]
        _ = h * (D.embed (hat (uc22s2112r34q35_zvec n) 1) *
              D.embed (hat (uc22s2112r34q35_zvec n) 1)) * h⁻¹ := by group
        _ = 1 := by rw [← pow_two, hEz_sq]; group
    have hu2 : u ^ 2 = 1 := by
      have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin 4) K =>
        (g : Matrix (Fin 4) (Fin 4) K)) hEa_sq) 0) 0
      rw [Units.val_pow_eq_pow_val, hEaMat, Units.val_one, pow_two,
        Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq] at h1
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, pow_two, Units.val_one]
      exact h1
    obtain ⟨k, hk⟩ := hs.odd_of_ne_two hs2
    have hu1 : u = 1 := by
      calc u = (u ^ 2) ^ k * u := by rw [hu2, one_pow, one_mul]
        _ = u ^ (2 * k) * u := by rw [pow_mul]
        _ = u ^ (2 * k + 1) := by rw [pow_succ]
        _ = u ^ s := by rw [← hk]
        _ = 1 := hus
    have hS_one : S = 1 := by
      change Matrix.GeneralLinearGroup.scalar (Fin 4) u = 1
      rw [hu1, map_one]
    have hEz_comm : h * D.embed (hat (uc22s2112r34q35_zvec n) 1) =
        D.embed (hat (uc22s2112r34q35_zvec n) 1) * h := by
      calc h * D.embed (hat (uc22s2112r34q35_zvec n) 1) =
          (h * D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹) * h := by group
        _ = D.embed (hat (uc22s2112r34q35_zvec n) 1) * h := by
            rw [hEz_conj, hS_one, one_mul]
    have hcomm_mat : Commute (Matrix.diagonal ![1, 1, -1, -1])
        (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) := by
      have h1 := congrArg (fun g : GL (Fin 4) K =>
        (g : Matrix (Fin 4) (Fin 4) K)) hEz_comm
      rw [Units.val_mul, Units.val_mul,
        uc22s2112r34q35_embed_zvec D (by omega)] at h1
      exact h1.symm
    have hoff₁ : ∀ i j : Fin 2,
        (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
          (Fin.castAdd 2 i) (Fin.natAdd 2 j) = 0 := by
      intro i j
      exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_mat (by
        fin_cases i <;> fin_cases j <;> simpa using hneg.symm)
    have hoff₂ : ∀ i j : Fin 2,
        (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
          (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0 := by
      intro i j
      exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_mat (by
        fin_cases i <;> fin_cases j <;> simpa using hneg)
    let A : Matrix (Fin 2) (Fin 2) K := fun i j =>
      (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
        (Fin.castAdd 2 i) (Fin.castAdd 2 j)
    let B : Matrix (Fin 2) (Fin 2) K := fun i j =>
      (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
        (Fin.natAdd 2 i) (Fin.natAdd 2 j)
    have hmat : (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
        uc22s2112r34q35_blk4 A B := by
      ext i j
      revert j
      refine Fin.addCases (m := 2) (n := 2) (motive := fun i =>
        ∀ j, (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) i j =
          uc22s2112r34q35_blk4 A B i j) ?_ ?_ i
      · intro i j
        refine Fin.addCases (m := 2) (n := 2) (motive := fun j =>
          (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
            (Fin.castAdd 2 i) j =
            uc22s2112r34q35_blk4 A B (Fin.castAdd 2 i) j) ?_ ?_ j
        · intro j
          rw [uc22s2112r34q35_blk4_castAdd_castAdd]
        · intro j
          rw [uc22s2112r34q35_blk4_castAdd_natAdd, hoff₁ i j]
      · intro i j
        refine Fin.addCases (m := 2) (n := 2) (motive := fun j =>
          (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
            (Fin.natAdd 2 i) j =
            uc22s2112r34q35_blk4 A B (Fin.natAdd 2 i) j) ?_ ?_ j
        · intro j
          rw [uc22s2112r34q35_blk4_natAdd_castAdd, hoff₂ i j]
        · intro j
          rw [uc22s2112r34q35_blk4_natAdd_natAdd]
    have hEz_comm_inv : h⁻¹ * D.embed (hat (uc22s2112r34q35_zvec n) 1) =
        D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹ := by
      calc h⁻¹ * D.embed (hat (uc22s2112r34q35_zvec n) 1) =
          h⁻¹ * (D.embed (hat (uc22s2112r34q35_zvec n) 1) * h) * h⁻¹ := by group
        _ = h⁻¹ * (h * D.embed (hat (uc22s2112r34q35_zvec n) 1)) * h⁻¹ := by
            rw [← hEz_comm]
        _ = D.embed (hat (uc22s2112r34q35_zvec n) 1) * h⁻¹ := by group
    have hcomm_mat_inv : Commute (Matrix.diagonal ![1, 1, -1, -1])
        (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) := by
      have h1 := congrArg (fun g : GL (Fin 4) K =>
        (g : Matrix (Fin 4) (Fin 4) K)) hEz_comm_inv
      rw [Units.val_mul, Units.val_mul,
        uc22s2112r34q35_embed_zvec D (by omega)] at h1
      exact h1.symm
    have hoff₁' : ∀ i j : Fin 2,
        (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
          (Fin.castAdd 2 i) (Fin.natAdd 2 j) = 0 := by
      intro i j
      exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_mat_inv (by
        fin_cases i <;> fin_cases j <;> simpa using hneg.symm)
    have hoff₂' : ∀ i j : Fin 2,
        (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
          (Fin.natAdd 2 i) (Fin.castAdd 2 j) = 0 := by
      intro i j
      exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_mat_inv (by
        fin_cases i <;> fin_cases j <;> simpa using hneg)
    let A' : Matrix (Fin 2) (Fin 2) K := fun i j =>
      (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
        (Fin.castAdd 2 i) (Fin.castAdd 2 j)
    let B' : Matrix (Fin 2) (Fin 2) K := fun i j =>
      (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
        (Fin.natAdd 2 i) (Fin.natAdd 2 j)
    have hmat' : (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) =
        uc22s2112r34q35_blk4 A' B' := by
      ext i j
      revert j
      refine Fin.addCases (m := 2) (n := 2) (motive := fun i =>
        ∀ j, (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) i j =
          uc22s2112r34q35_blk4 A' B' i j) ?_ ?_ i
      · intro i j
        refine Fin.addCases (m := 2) (n := 2) (motive := fun j =>
          (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
            (Fin.castAdd 2 i) j =
            uc22s2112r34q35_blk4 A' B' (Fin.castAdd 2 i) j) ?_ ?_ j
        · intro j
          rw [uc22s2112r34q35_blk4_castAdd_castAdd]
        · intro j
          rw [uc22s2112r34q35_blk4_castAdd_natAdd, hoff₁' i j]
      · intro i j
        refine Fin.addCases (m := 2) (n := 2) (motive := fun j =>
          (((h⁻¹ : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K)
            (Fin.natAdd 2 i) j =
            uc22s2112r34q35_blk4 A' B' (Fin.natAdd 2 i) j) ?_ ?_ j
        · intro j
          rw [uc22s2112r34q35_blk4_natAdd_castAdd, hoff₂' i j]
        · intro j
          rw [uc22s2112r34q35_blk4_natAdd_natAdd]
    have hAA' : A * A' = 1 := by
      have h1 : uc22s2112r34q35_blk4 (A * A') (B * B') = 1 := by
        rw [← uc22s2112r34q35_blk4_mul, ← hmat, ← hmat']
        exact Units.mul_inv h
      exact (uc22s2112r34q35_blk4_inj (h1.trans (uc22s2112r34q35_blk4_one).symm)).1
    have hA'A : A' * A = 1 := by
      have h1 : uc22s2112r34q35_blk4 (A' * A) (B' * B) = 1 := by
        rw [← uc22s2112r34q35_blk4_mul, ← hmat', ← hmat]
        exact Units.inv_mul h
      exact (uc22s2112r34q35_blk4_inj (h1.trans (uc22s2112r34q35_blk4_one).symm)).1
    have hBB' : B * B' = 1 := by
      have h1 : uc22s2112r34q35_blk4 (A * A') (B * B') = 1 := by
        rw [← uc22s2112r34q35_blk4_mul, ← hmat, ← hmat']
        exact Units.mul_inv h
      exact (uc22s2112r34q35_blk4_inj (h1.trans (uc22s2112r34q35_blk4_one).symm)).2
    have hB'B : B' * B = 1 := by
      have h1 : uc22s2112r34q35_blk4 (A' * A) (B' * B) = 1 := by
        rw [← uc22s2112r34q35_blk4_mul, ← hmat', ← hmat]
        exact Units.inv_mul h
      exact (uc22s2112r34q35_blk4_inj (h1.trans (uc22s2112r34q35_blk4_one).symm)).2
    let Au : GL (Fin 2) K := ⟨A, A', hAA', hA'A⟩
    let Bu : GL (Fin 2) K := ⟨B, B', hBB', hB'B⟩
    have hAs : A ^ s = 1 := by
      have h1 : (uc22s2112r34q35_blk4 A B) ^ s = 1 := by
        rw [← hmat]
        rw [← Units.val_pow_eq_pow_val, hh, Units.val_one]
      have h2 : uc22s2112r34q35_blk4 (A ^ s) (B ^ s) =
          uc22s2112r34q35_blk4 1 1 := by
        rw [← uc22s2112r34q35_blk4_pow, h1, uc22s2112r34q35_blk4_one]
      exact (uc22s2112r34q35_blk4_inj h2).1
    have hBs : B ^ s = 1 := by
      have h1 : (uc22s2112r34q35_blk4 A B) ^ s = 1 := by
        rw [← hmat]
        rw [← Units.val_pow_eq_pow_val, hh, Units.val_one]
      have h2 : uc22s2112r34q35_blk4 (A ^ s) (B ^ s) =
          uc22s2112r34q35_blk4 1 1 := by
        rw [← uc22s2112r34q35_blk4_pow, h1, uc22s2112r34q35_blk4_one]
      exact (uc22s2112r34q35_blk4_inj h2).2
    have hAu_s : Au ^ s = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      change A ^ s = 1
      exact hAs
    have hBu_s : Bu ^ s = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      change B ^ s = 1
      exact hBs
    have hAu1 : Au = 1 := by
      have hdiv : orderOf Au ∣ s := orderOf_dvd_of_pow_eq_one hAu_s
      have hcard : orderOf Au ∣ Nat.card (GL (Fin 2) K) := orderOf_dvd_natCard Au
      rcases (Nat.dvd_prime hs).mp hdiv with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd (h1 ▸ hcard) hGL
    have hBu1 : Bu = 1 := by
      have hdiv : orderOf Bu ∣ s := orderOf_dvd_of_pow_eq_one hBu_s
      have hcard : orderOf Bu ∣ Nat.card (GL (Fin 2) K) := orderOf_dvd_natCard Bu
      rcases (Nat.dvd_prime hs).mp hdiv with h1 | h1
      · exact orderOf_eq_one_iff.mp h1
      · exact absurd (h1 ▸ hcard) hGL
    have hA1 : A = 1 := by
      have h1 := congrArg Units.val hAu1
      simpa [Au] using h1
    have hB1 : B = 1 := by
      have h1 := congrArg Units.val hBu1
      simpa [Bu] using h1
    have hmat1 : (((h : GL (Fin 4) K)) : Matrix (Fin 4) (Fin 4) K) = 1 := by
      rw [hmat, hA1, hB1, uc22s2112r34q35_blk4_one]
    exact Units.ext hmat1


@[expose] def uc22s2112r34q35_blk5 {K : Type} [Field K] (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    Matrix (Fin 5) (Fin 5) K :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (Matrix.scalar (Fin 1) c))

private theorem uc22s2112r34q35_blk5_mul {K : Type} [Field K]
    (A A' : Matrix (Fin 4) (Fin 4) K) (c c' : K) :
    uc22s2112r34q35_blk5 A c * uc22s2112r34q35_blk5 A' c' =
      uc22s2112r34q35_blk5 (A * A') (c * c') := by
  rw [uc22s2112r34q35_blk5, uc22s2112r34q35_blk5, uc22s2112r34q35_blk5,
    Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  rw [show Matrix.scalar (Fin 1) c * Matrix.scalar (Fin 1) c' =
      Matrix.scalar (Fin 1) (c * c') from (map_mul _ _ _).symm]

private theorem uc22s2112r34q35_blk5_one {K : Type} [Field K] :
    uc22s2112r34q35_blk5 (1 : Matrix (Fin 4) (Fin 4) K) 1 = 1 := by
  rw [uc22s2112r34q35_blk5, show Matrix.scalar (Fin 1) (1 : K) = 1 from map_one _,
    Matrix.fromBlocks_one, Matrix.reindex_apply, Matrix.submatrix_one_equiv]

private theorem uc22s2112r34q35_det_blk5 {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    (uc22s2112r34q35_blk5 A c).det = A.det * c := by
  rw [uc22s2112r34q35_blk5, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fin_one, Matrix.scalar_apply]
  simp

private theorem uc22s2112r34q35_blk5_pow {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) (k : ℕ) :
    (uc22s2112r34q35_blk5 A c) ^ k =
      uc22s2112r34q35_blk5 (A ^ k) (c ^ k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, pow_zero, uc22s2112r34q35_blk5_one]
  | succ k ih => rw [pow_succ, ih, uc22s2112r34q35_blk5_mul, pow_succ, pow_succ]

private theorem uc22s2112r34q35_blk5_castAdd_castAdd {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) (i j : Fin 4) :
    uc22s2112r34q35_blk5 A c (Fin.castAdd 1 i) (Fin.castAdd 1 j) = A i j := by
  rw [uc22s2112r34q35_blk5, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₁₁]

private theorem uc22s2112r34q35_blk5_last {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) :
    uc22s2112r34q35_blk5 A c (Fin.last 4) (Fin.last 4) = c := by
  rw [uc22s2112r34q35_blk5, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_last, Matrix.fromBlocks_apply₂₂, Matrix.scalar_apply]
  simp

private theorem uc22s2112r34q35_blk5_castAdd_last {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) (i : Fin 4) :
    uc22s2112r34q35_blk5 A c (Fin.castAdd 1 i) (Fin.last 4) = 0 := by
  rw [uc22s2112r34q35_blk5, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_last,
    Matrix.fromBlocks_apply₁₂]
  simp

private theorem uc22s2112r34q35_blk5_last_castAdd {K : Type} [Field K]
    (A : Matrix (Fin 4) (Fin 4) K) (c : K) (j : Fin 4) :
    uc22s2112r34q35_blk5 A c (Fin.last 4) (Fin.castAdd 1 j) = 0 := by
  rw [uc22s2112r34q35_blk5, Matrix.reindex_apply, Matrix.submatrix_apply,
    finSumFinEquiv_symm_last, finSumFinEquiv_symm_apply_castAdd,
    Matrix.fromBlocks_apply₂₁]
  simp

private theorem uc22s2112r34q35_blk5_inj {K : Type} [Field K]
    {A A' : Matrix (Fin 4) (Fin 4) K} {c c' : K}
    (h : uc22s2112r34q35_blk5 A c = uc22s2112r34q35_blk5 A' c') : A = A' := by
  ext i j
  have h1 := congrFun (congrFun h (Fin.castAdd 1 i)) (Fin.castAdd 1 j)
  simpa [uc22s2112r34q35_blk5_castAdd_castAdd] using h1

private theorem uc22s2112r34q35_hat_cvec_central {n : ℕ} (b : L4Hat n) :
    hat (uc22s2112r34q35_cvec n) 1 * b = b * hat (uc22s2112r34q35_cvec n) 1 := by
  rw [← hat_left b]
  rw [hat_mul, hat_mul]
  simp only [OneMemClass.coe_one, one_mul, mul_one, pv_one]
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    simp only [toAdd_ofAdd, Pi.add_apply, pv, uc22s2112r34q35_cvec]
    ring
  · rfl

@[expose] noncomputable def uc22s2112r34q35_blockDet (K : Type) [Field K] :
    GL (Fin 4) K →* GL (Fin 5) K where
  toFun A :=
    { val := uc22s2112r34q35_blk5 (A : Matrix (Fin 4) (Fin 4) K)
        (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K)
      inv := uc22s2112r34q35_blk5 ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        ((Matrix.GeneralLinearGroup.det A : Kˣ) : K)
      val_inv := by
        change uc22s2112r34q35_blk5 (A : Matrix (Fin 4) (Fin 4) K)
            (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) *
          uc22s2112r34q35_blk5 ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
            ((Matrix.GeneralLinearGroup.det A : Kˣ) : K) = 1
        rw [uc22s2112r34q35_blk5_mul]
        have hA : (A : Matrix (Fin 4) (Fin 4) K) *
            ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        have hc : (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) *
            ((Matrix.GeneralLinearGroup.det A : Kˣ) : K) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        rw [hA, hc, uc22s2112r34q35_blk5_one]
      inv_val := by
        change uc22s2112r34q35_blk5 ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
            ((Matrix.GeneralLinearGroup.det A : Kˣ) : K) *
          uc22s2112r34q35_blk5 (A : Matrix (Fin 4) (Fin 4) K)
            (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) = 1
        rw [uc22s2112r34q35_blk5_mul]
        have hA : ((A⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
            (A : Matrix (Fin 4) (Fin 4) K) = 1 := by
          rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
        have hc : ((Matrix.GeneralLinearGroup.det A : Kˣ) : K) *
            (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) = 1 := by
          rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [hA, hc, uc22s2112r34q35_blk5_one] }
  map_one' := by
    apply Units.ext
    change uc22s2112r34q35_blk5 (1 : Matrix (Fin 4) (Fin 4) K)
        (((Matrix.GeneralLinearGroup.det (1 : GL (Fin 4) K))⁻¹ : Kˣ) : K) = 1
    rw [map_one, inv_one, Units.val_one, uc22s2112r34q35_blk5_one]
  map_mul' A B := by
    apply Units.ext
    change uc22s2112r34q35_blk5 ((A * B : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        (((Matrix.GeneralLinearGroup.det (A * B))⁻¹ : Kˣ) : K) =
      uc22s2112r34q35_blk5 (A : Matrix (Fin 4) (Fin 4) K)
          (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) *
        uc22s2112r34q35_blk5 (B : Matrix (Fin 4) (Fin 4) K)
          (((Matrix.GeneralLinearGroup.det B)⁻¹ : Kˣ) : K)
    have hscalar : (((Matrix.GeneralLinearGroup.det (A * B))⁻¹ : Kˣ) : K) =
        (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) *
          (((Matrix.GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) := by
      rw [map_mul]
      have h2 : (((Matrix.GeneralLinearGroup.det A *
            Matrix.GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) =
          (((Matrix.GeneralLinearGroup.det B)⁻¹ : Kˣ) : K) *
            (((Matrix.GeneralLinearGroup.det A)⁻¹ : Kˣ) : K) := by
        rw [mul_inv_rev, Units.val_mul]
      rw [h2]
      ring
    rw [uc22s2112r34q35_blk5_mul, Units.val_mul, hscalar]

theorem uc22s2112r34q35_eq_one_of_normalizes_blockDet_embed {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (D : L4Data K n) (R : Subgroup (L4Hat n)) {e₁ e₂ : Fin 4 → ZMod (2 ^ n)}
    (hsep : ∀ π : Fin81.R0, π ≠ 1 →
      ¬ IsConst (pv (π : Perm (Fin 4)) e₁ - e₁) ∨ ¬ IsConst (pv (π : Perm (Fin 4)) e₂ - e₂))
    (he₁ : hat e₁ 1 ∈ R) (he₂ : hat e₂ 1 ∈ R) {y₀₁ y₂₃ y₀₂ : L4Hat n} (hy₀₁ : y₀₁ ∈ R)
    (hy₂₃ : y₂₃ ∈ R) (hy₀₂ : y₀₂ ∈ R) (h₀₁ : y₀₁.right = uc22s2112r34q35_r01)
    (h₂₃ : y₂₃.right = uc22s2112r34q35_r23) (h₀₂ : y₀₂.right = uc22s2112r34q35_r02)
    (hz : hat (uc22s2112r34q35_zvec n) 1 ∈ R) (hc : hat (uc22s2112r34q35_cvec n) 1 ∈ R)
    {h : GL (Fin 5) K} {s : ℕ} (hs : s.Prime) (hs2 : s ≠ 2) (hh : h ^ s = 1)
    (hGL : ¬ s ∣ Nat.card (GL (Fin 2) K)) (hK : ¬ s ∣ Nat.card K - 1)
    (hN : ∀ a ∈ R, ∃ a' ∈ R, h * uc22s2112r34q35_blockDet K (D.embed a) * h⁻¹ =
      uc22s2112r34q35_blockDet K (D.embed a'))
    (hN' : ∀ a ∈ R, ∃ a' ∈ R, h⁻¹ * uc22s2112r34q35_blockDet K (D.embed a) * h =
      uc22s2112r34q35_blockDet K (D.embed a')) : h = 1 := by
  have hneg : (-1 : K) ≠ 1 := uc22s2112r34q35_neg_one_ne_one D hn
  let iota : L4Hat n →* GL (Fin 5) K :=
    (uc22s2112r34q35_blockDet K).comp D.embed
  have iota_inj : Function.Injective iota := by
    intro a b hab
    apply D.embed_injective
    apply Units.ext
    have h1 := congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) hab
    exact uc22s2112r34q35_blk5_inj h1
  let t : GL (Fin 5) K := iota (hat (uc22s2112r34q35_cvec n) 1)
  have ht_val : (t : Matrix (Fin 5) (Fin 5) K) =
      uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K) 1 := by
    change ((uc22s2112r34q35_blockDet K (D.embed (hat (uc22s2112r34q35_cvec n) 1)) :
      GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = _
    rw [uc22s2112r34q35_embed_cvec D (by omega)]
    change uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K)
        (((Matrix.GeneralLinearGroup.det (-1 : GL (Fin 4) K))⁻¹ : Kˣ) : K) = _
    have hdet : Matrix.GeneralLinearGroup.det (-1 : GL (Fin 4) K) = 1 := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one,
        show ((-1 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1 from rfl,
        Matrix.det_neg, Fintype.card_fin, Matrix.det_one, mul_one]
      ring
    rw [hdet, inv_one, Units.val_one]
  have ht_ne : t ≠ 1 := by
    intro h1
    have h2 := congrFun (congrFun (congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) h1) (Fin.castAdd 1 0)) (Fin.castAdd 1 0)
    rw [Units.val_one, ht_val, uc22s2112r34q35_blk5_castAdd_castAdd] at h2
    simp [Matrix.neg_apply] at h2
    exact hneg h2
  have ht_sq : t * t = 1 := by
    apply Units.ext
    rw [Units.val_mul, Units.val_one, ht_val, uc22s2112r34q35_blk5_mul]
    have h1 : (-1 : Matrix (Fin 4) (Fin 4) K) * (-1) = 1 := by
      rw [neg_mul_neg, one_mul]
    rw [h1, one_mul, uc22s2112r34q35_blk5_one]
  obtain ⟨a₀, ha₀R, hconj⟩ := hN (hat (uc22s2112r34q35_cvec n) 1) hc
  have hconj' : h * t * h⁻¹ = iota a₀ := by
    change h * uc22s2112r34q35_blockDet K
        (D.embed (hat (uc22s2112r34q35_cvec n) 1)) * h⁻¹ =
      uc22s2112r34q35_blockDet K (D.embed a₀)
    exact hconj
  have hcomm : ∀ b ∈ R, a₀ * b = b * a₀ := by
    intro b hb
    obtain ⟨b', hb'R, hb'conj⟩ := hN' b hb
    have hb'conj_iota : h⁻¹ * iota b * h = iota b' := by
      change h⁻¹ * (uc22s2112r34q35_blockDet K) (D.embed b) * h =
        (uc22s2112r34q35_blockDet K) (D.embed b')
      exact hb'conj
    have hb'conj' : h * iota b' * h⁻¹ = iota b := by
      calc h * iota b' * h⁻¹ = h * (h⁻¹ * iota b * h) * h⁻¹ := by rw [hb'conj_iota]
        _ = iota b := by group
    have ht_comm : t * iota b' = iota b' * t := by
      change iota (hat (uc22s2112r34q35_cvec n) 1) * iota b' =
        iota b' * iota (hat (uc22s2112r34q35_cvec n) 1)
      rw [← map_mul, ← map_mul, uc22s2112r34q35_hat_cvec_central b']
    have hc_b' : iota a₀ * iota b = iota b * iota a₀ := by
      calc iota a₀ * iota b =
          (h * t * h⁻¹) * (h * iota b' * h⁻¹) := by rw [hconj', hb'conj']
        _ = h * (t * iota b') * h⁻¹ := by group
        _ = h * (iota b' * t) * h⁻¹ := by rw [ht_comm]
        _ = (h * iota b' * h⁻¹) * (h * t * h⁻¹) := by group
        _ = iota b * iota a₀ := by rw [hb'conj', hconj']
    exact iota_inj (by simpa only [map_mul] using hc_b')
  obtain ⟨ha₀right, ha₀_const⟩ :=
    uc22s2112r34q35_hat_const_of_comm hn hsep h₀₁ h₂₃ h₀₂
      (hcomm _ he₁) (hcomm _ he₂) (hcomm _ hy₀₁) (hcomm _ hy₂₃) (hcomm _ hy₀₂)
  set c := Multiplicative.toAdd a₀.left with hcdef
  have ha₀eq : a₀ = hat c 1 := by
    rw [← hat_left a₀, ha₀right]
  have ha₀_sq : iota a₀ * iota a₀ = 1 := by
    calc iota a₀ * iota a₀ = (h * t * h⁻¹) * (h * t * h⁻¹) := by rw [hconj']
      _ = h * (t * t) * h⁻¹ := by group
      _ = 1 := by rw [ht_sq]; group
  let M : Matrix (Fin 4) (Fin 4) K := (D.embed a₀ : GL (Fin 4) K)
  let d : K := (((Matrix.GeneralLinearGroup.det (D.embed a₀))⁻¹ : Kˣ) : K)
  have hM_sq : M * M = 1 := by
    have h1 := congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) ha₀_sq
    rw [Units.val_mul, Units.val_one] at h1
    have h1' : ((uc22s2112r34q35_blockDet K (D.embed a₀) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) *
        ((uc22s2112r34q35_blockDet K (D.embed a₀) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = 1 := by
      simpa [iota] using h1
    have hbd : ((uc22s2112r34q35_blockDet K (D.embed a₀) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = uc22s2112r34q35_blk5 M d := rfl
    rw [hbd] at h1'
    rw [uc22s2112r34q35_blk5_mul] at h1'
    exact uc22s2112r34q35_blk5_inj (h1'.trans (uc22s2112r34q35_blk5_one).symm)
  have hdiag : M = Matrix.diagonal (fun i => (D.ζ : K) ^ (c i).val) := by
    rw [show M = ((D.embed a₀ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) from rfl,
      ha₀eq, D.coe_embed]
    simp only [OneMemClass.coe_one, inv_one,
      Matrix.permMatrix_one, mul_one, toAdd_ofAdd]
  have h2c : ∀ i, 2 * c i = 0 := by
    intro i
    have hentry : (D.ζ : K) ^ (c i).val * (D.ζ : K) ^ (c i).val = 1 := by
      have h := congrFun (congrFun hM_sq i) i
      rw [hdiag, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
        Matrix.one_apply_eq] at h
      exact h
    have hpow2 : (D.ζ : K) ^ (2 * (c i).val) = 1 := by
      rw [two_mul, pow_add]
      exact hentry
    have hord : (D.ζ : K) ^ (2 ^ n) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← D.orderOf_ζ, pow_orderOf_eq_one, Units.val_one]
    have hcast : (2 * c i : ZMod (2 ^ n)) =
        ((2 * (c i).val : ℕ) : ZMod (2 ^ n)) := by
      conv_lhs => rw [← ZMod.natCast_zmod_val (c i)]
      conv_rhs => rw [Nat.cast_mul, Nat.cast_ofNat]
    have hpow : (D.ζ : K) ^ ((2 * c i).val) = 1 := by
      rw [hcast, ZMod.val_natCast]
      rw [← pow_eq_pow_mod (2 * (c i).val) hord]
      exact hpow2
    exact (D.pow_val_eq_pow_val_iff (x := 2 * c i) (y := 0)).1 (by
      rw [hpow, ZMod.val_zero, pow_zero])
  have ha₀_ne : iota a₀ ≠ 1 := by
    intro h1
    apply ht_ne
    calc t = h⁻¹ * (h * t * h⁻¹) * h := by group
      _ = h⁻¹ * iota a₀ * h := by rw [hconj']
      _ = h⁻¹ * 1 * h := by rw [h1]
      _ = 1 := by group
  have hc_ne : ∀ i, c i ≠ 0 := by
    intro i hi
    apply ha₀_ne
    have hczero : c = 0 := by
      funext j
      have h := ha₀_const i j
      rw [hi] at h
      exact h.symm
    rw [ha₀eq, hczero]
    exact map_one iota
  have hc_hh : ∀ i, c i = CFSG.LocalAnalysis.Mason73.hh n := by
    intro i
    have hx : c i ≠ 0 := hc_ne i
    have h2 := h2c i
    have hval_ne : (c i).val ≠ 0 := by
      intro h0
      exact hx (ZMod.val_eq_zero _ |>.mp h0)
    have hval_lt : (c i).val < 2 ^ n := ZMod.val_lt _
    have hval2 : (2 * (c i).val) % 2 ^ n = 0 := by
      have h := congrArg ZMod.val h2
      rw [ZMod.val_zero] at h
      have hcast : (2 * c i : ZMod (2 ^ n)) =
          ((2 * (c i).val : ℕ) : ZMod (2 ^ n)) := by
        conv_lhs => rw [← ZMod.natCast_zmod_val (c i)]
        conv_rhs => rw [Nat.cast_mul, Nat.cast_ofNat]
      rwa [hcast, ZMod.val_natCast] at h
    have hdvd : 2 ^ n ∣ 2 * (c i).val := Nat.dvd_of_mod_eq_zero hval2
    have hne : 2 * (c i).val ≠ 0 := Nat.mul_ne_zero (by norm_num) hval_ne
    have hlt : 2 * (c i).val < 2 * 2 ^ n :=
      Nat.mul_lt_mul_of_pos_left hval_lt (by norm_num)
    have heq : 2 * (c i).val = 2 ^ n :=
      Nat.eq_of_dvd_of_lt_two_mul hne hdvd hlt
    have h2pow : 2 ^ n = 2 * 2 ^ (n - 1) := by
      calc 2 ^ n = 2 ^ ((n - 1) + 1) := by rw [Nat.sub_add_cancel (by omega)]
        _ = 2 * 2 ^ (n - 1) := by rw [pow_succ']
    have hval_eq : (c i).val = 2 ^ (n - 1) :=
      Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (by rw [heq, h2pow])
    rw [← ZMod.natCast_zmod_val (c i), hval_eq]
  have hc_eq : c = uc22s2112r34q35_cvec n := by
    funext i
    rw [hc_hh i]
    rfl
  have ha₀_cvec : a₀ = hat (uc22s2112r34q35_cvec n) 1 := by
    rw [ha₀eq, hc_eq]
  have ht_conj : h * t * h⁻¹ = t := by
    rw [hconj', ha₀_cvec]
  have ht_comm_h : h * t = t * h := by
    calc h * t = (h * t * h⁻¹) * h := by group
      _ = t * h := by rw [ht_conj]
  let v : Fin 5 → K := ![(-1 : K), (-1), (-1), (-1), 1]
  have ht_diag : (t : Matrix (Fin 5) (Fin 5) K) = Matrix.diagonal v := by
    rw [ht_val]
    ext i j
    revert j
    refine Fin.addCases (m := 4) (n := 1) (motive := fun i =>
      ∀ j, uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K) 1 i j =
        Matrix.diagonal v i j) ?_ ?_ i
    · intro i j
      refine Fin.addCases (m := 4) (n := 1) (motive := fun j =>
        uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K) 1
          (Fin.castAdd 1 i) j = Matrix.diagonal v (Fin.castAdd 1 i) j) ?_ ?_ j
      · intro j
        rw [uc22s2112r34q35_blk5_castAdd_castAdd]
        have hv : v (Fin.castAdd 1 i) = -1 := by
          fin_cases i <;> rfl
        by_cases h : i = j
        · subst h
          simp [Matrix.diagonal, Matrix.neg_apply, hv]
        · have hne : Fin.castAdd 1 i ≠ Fin.castAdd 1 j := by
            intro hc
            exact h (Fin.castAdd_inj.mp hc)
          simp [Matrix.diagonal, Matrix.neg_apply, Matrix.one_apply, hne]
          exact h
      · intro j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        change uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K) 1
          (Fin.castAdd 1 i) (Fin.last 4) = Matrix.diagonal v (Fin.castAdd 1 i) (Fin.last 4)
        rw [uc22s2112r34q35_blk5_castAdd_last]
        have hne : Fin.castAdd 1 i ≠ (4 : Fin 5) := by
          intro h
          have h' := congrArg Fin.val h
          simp [Fin.castAdd] at h'
          omega
        simp [v, Matrix.diagonal, hne]
    · intro i j
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K) 1
        (Fin.last 4) j = Matrix.diagonal v (Fin.last 4) j

      refine Fin.addCases (m := 4) (n := 1) (motive := fun j =>
        uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K) 1
          (Fin.last 4) j = Matrix.diagonal v (Fin.last 4) j) ?_ ?_ j
      · intro j
        rw [uc22s2112r34q35_blk5_last_castAdd]
        have hne : (4 : Fin 5) ≠ Fin.castAdd 1 j := by
          intro h
          have h' := congrArg Fin.val h
          simp [Fin.castAdd] at h'
          omega
        simp [v, Matrix.diagonal, hne]
      · intro j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        change uc22s2112r34q35_blk5 (-1 : Matrix (Fin 4) (Fin 4) K) 1
          (Fin.last 4) (Fin.last 4) = Matrix.diagonal v (Fin.last 4) (Fin.last 4)
        rw [uc22s2112r34q35_blk5_last]
        simp [v, Matrix.diagonal]
  have hcomm_v : Commute (Matrix.diagonal v)
      (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) := by
    have h1 := congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) ht_comm_h
    rw [Units.val_mul, Units.val_mul, ht_diag] at h1
    exact h1.symm
  have hoff₁ : ∀ i : Fin 4,
      (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
        (Fin.castAdd 1 i) (Fin.last 4) = 0 := by
    intro i
    exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_v (by
      fin_cases i <;> simp [v, hneg])
  have hoff₂ : ∀ i : Fin 4,
      (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
        (Fin.last 4) (Fin.castAdd 1 i) = 0 := by
    intro i
    exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_v (by
      fin_cases i <;> simp [v, hneg.symm])
  have ht_comm_h_inv : h⁻¹ * t = t * h⁻¹ := by
    calc h⁻¹ * t = h⁻¹ * (t * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * t) * h⁻¹ := by rw [← ht_comm_h]
      _ = t * h⁻¹ := by group
  have hcomm_v_inv : Commute (Matrix.diagonal v)
      (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) := by
    have h1 := congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) ht_comm_h_inv
    rw [Units.val_mul, Units.val_mul, ht_diag] at h1
    exact h1.symm
  have hoff₁' : ∀ i : Fin 4,
      (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
        (Fin.castAdd 1 i) (Fin.last 4) = 0 := by
    intro i
    exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_v_inv (by
      fin_cases i <;> simp [v, hneg])
  have hoff₂' : ∀ i : Fin 4,
      (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
        (Fin.last 4) (Fin.castAdd 1 i) = 0 := by
    intro i
    exact TauCeti.apply_eq_zero_of_commute_diagonal hcomm_v_inv (by
      fin_cases i <;> simp [v, hneg.symm])
  let A : Matrix (Fin 4) (Fin 4) K := fun i j =>
    (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
      (Fin.castAdd 1 i) (Fin.castAdd 1 j)
  let μ : K := (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
    (Fin.last 4) (Fin.last 4)
  have hmat : (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) =
      uc22s2112r34q35_blk5 A μ := by
    ext i j
    revert j
    refine Fin.addCases (m := 4) (n := 1) (motive := fun i =>
      ∀ j, (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) i j =
        uc22s2112r34q35_blk5 A μ i j) ?_ ?_ i
    · intro i j
      refine Fin.addCases (m := 4) (n := 1) (motive := fun j =>
        (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.castAdd 1 i) j =
          uc22s2112r34q35_blk5 A μ (Fin.castAdd 1 i) j) ?_ ?_ j
      · intro j
        rw [uc22s2112r34q35_blk5_castAdd_castAdd]
      · intro j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        change (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.castAdd 1 i) (Fin.last 4) =
          uc22s2112r34q35_blk5 A μ (Fin.castAdd 1 i) (Fin.last 4)
        rw [uc22s2112r34q35_blk5_castAdd_last, hoff₁ i]
    · intro i j
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
        (Fin.last 4) j = uc22s2112r34q35_blk5 A μ (Fin.last 4) j

      refine Fin.addCases (m := 4) (n := 1) (motive := fun j =>
        (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.last 4) j =
          uc22s2112r34q35_blk5 A μ (Fin.last 4) j) ?_ ?_ j
      · intro j
        rw [uc22s2112r34q35_blk5_last_castAdd, hoff₂ j]
      · intro j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        change (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.last 4) (Fin.last 4) =
          uc22s2112r34q35_blk5 A μ (Fin.last 4) (Fin.last 4)
        rw [uc22s2112r34q35_blk5_last]
  let A' : Matrix (Fin 4) (Fin 4) K := fun i j =>
    (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
      (Fin.castAdd 1 i) (Fin.castAdd 1 j)
  let μ' : K := (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
    (Fin.last 4) (Fin.last 4)
  have hmat' : (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) =
      uc22s2112r34q35_blk5 A' μ' := by
    ext i j
    revert j
    refine Fin.addCases (m := 4) (n := 1) (motive := fun i =>
      ∀ j, (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) i j =
        uc22s2112r34q35_blk5 A' μ' i j) ?_ ?_ i
    · intro i j
      refine Fin.addCases (m := 4) (n := 1) (motive := fun j =>
        (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.castAdd 1 i) j =
          uc22s2112r34q35_blk5 A' μ' (Fin.castAdd 1 i) j) ?_ ?_ j
      · intro j
        rw [uc22s2112r34q35_blk5_castAdd_castAdd]
      · intro j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        change (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.castAdd 1 i) (Fin.last 4) =
          uc22s2112r34q35_blk5 A' μ' (Fin.castAdd 1 i) (Fin.last 4)
        rw [uc22s2112r34q35_blk5_castAdd_last, hoff₁' i]
    · intro i j
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      change (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
        (Fin.last 4) j = uc22s2112r34q35_blk5 A' μ' (Fin.last 4) j

      refine Fin.addCases (m := 4) (n := 1) (motive := fun j =>
        (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.last 4) j =
          uc22s2112r34q35_blk5 A' μ' (Fin.last 4) j) ?_ ?_ j
      · intro j
        rw [uc22s2112r34q35_blk5_last_castAdd, hoff₂' j]
      · intro j
        have hj : j = 0 := Subsingleton.elim j 0
        subst hj
        change (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K)
          (Fin.last 4) (Fin.last 4) =
          uc22s2112r34q35_blk5 A' μ' (Fin.last 4) (Fin.last 4)
        rw [uc22s2112r34q35_blk5_last]
  have hblk_s : (uc22s2112r34q35_blk5 A μ) ^ s = 1 := by
    rw [← hmat, ← Units.val_pow_eq_pow_val, hh, Units.val_one]
  have hA_s : A ^ s = 1 := by
    have h1 : uc22s2112r34q35_blk5 (A ^ s) (μ ^ s) = 1 := by
      rw [← uc22s2112r34q35_blk5_pow]
      exact hblk_s
    have h2 : uc22s2112r34q35_blk5 (A ^ s) (μ ^ s) =
        uc22s2112r34q35_blk5 1 1 := by
      rw [h1, uc22s2112r34q35_blk5_one]
    exact uc22s2112r34q35_blk5_inj h2
  have hmu_s : μ ^ s = 1 := by
    have h1 := congrFun (congrFun hblk_s (Fin.last 4)) (Fin.last 4)
    rw [uc22s2112r34q35_blk5_pow, uc22s2112r34q35_blk5_last,
      Matrix.one_apply_eq] at h1
    exact h1
  have hmu_ne : μ ≠ 0 := by
    intro h0
    have h1 := hmu_s
    rw [h0, zero_pow (Nat.Prime.pos hs).ne'] at h1
    exact zero_ne_one h1
  have hmuu_s : (Units.mk0 μ hmu_ne) ^ s = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hmu_s, Units.val_one]
  have hmuu1 : Units.mk0 μ hmu_ne = 1 := by
    have hdiv : orderOf (Units.mk0 μ hmu_ne) ∣ s :=
      orderOf_dvd_of_pow_eq_one hmuu_s
    have hcard : orderOf (Units.mk0 μ hmu_ne) ∣ Nat.card Kˣ :=
      orderOf_dvd_natCard _
    rw [Nat.card_units] at hcard
    rcases (Nat.dvd_prime hs).mp hdiv with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · exact absurd (h1 ▸ hcard) hK
  have hmu1 : μ = 1 := by
    have h1 := congrArg Units.val hmuu1
    simpa using h1
  have hμμ' : μ * μ' = 1 := by
    have h1 : uc22s2112r34q35_blk5 (A * A') (μ * μ') = 1 := by
      rw [← uc22s2112r34q35_blk5_mul, ← hmat, ← hmat']
      exact Units.mul_inv h
    have h2 := congrFun (congrFun h1 (Fin.last 4)) (Fin.last 4)
    rw [uc22s2112r34q35_blk5_last, Matrix.one_apply_eq] at h2
    exact h2
  have hμ'1 : μ' = 1 := by
    rw [hmu1, one_mul] at hμμ'
    exact hμμ'
  have hAA' : A * A' = 1 := by
    have h1 : uc22s2112r34q35_blk5 (A * A') (μ * μ') = 1 := by
      rw [← uc22s2112r34q35_blk5_mul, ← hmat, ← hmat']
      exact Units.mul_inv h
    have h2 : uc22s2112r34q35_blk5 (A * A') (μ * μ') =
        uc22s2112r34q35_blk5 1 1 := by
      rw [h1, uc22s2112r34q35_blk5_one]
    exact uc22s2112r34q35_blk5_inj h2
  have hA'A : A' * A = 1 := by
    have h1 : uc22s2112r34q35_blk5 (A' * A) (μ' * μ) = 1 := by
      rw [← uc22s2112r34q35_blk5_mul, ← hmat', ← hmat]
      exact Units.inv_mul h
    have h2 : uc22s2112r34q35_blk5 (A' * A) (μ' * μ) =
        uc22s2112r34q35_blk5 1 1 := by
      rw [h1, uc22s2112r34q35_blk5_one]
    exact uc22s2112r34q35_blk5_inj h2
  let Aunit : GL (Fin 4) K := ⟨A, A', hAA', hA'A⟩
  have hmat1' : (((h⁻¹ : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) =
      uc22s2112r34q35_blk5 A' 1 := by
    rw [hmat', hμ'1]
  have hN_A : ∀ a ∈ R, ∃ a' ∈ R,
      Aunit * D.embed a * Aunit⁻¹ = D.embed a' := by
    intro a ha
    obtain ⟨a', ha'R, ha'conj⟩ := hN a ha
    refine ⟨a', ha'R, ?_⟩
    apply Units.ext
    change A * (D.embed a : Matrix (Fin 4) (Fin 4) K) * A' =
      (D.embed a' : Matrix (Fin 4) (Fin 4) K)
    have h1 := congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) ha'conj
    rw [Units.val_mul, Units.val_mul, hmat, hmat1'] at h1
    have hbd : ((uc22s2112r34q35_blockDet K (D.embed a) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) =
        uc22s2112r34q35_blk5 (D.embed a : Matrix (Fin 4) (Fin 4) K)
          (((Matrix.GeneralLinearGroup.det (D.embed a))⁻¹ : Kˣ) : K) := rfl
    have hbd' : ((uc22s2112r34q35_blockDet K (D.embed a') : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) =
        uc22s2112r34q35_blk5 (D.embed a' : Matrix (Fin 4) (Fin 4) K)
          (((Matrix.GeneralLinearGroup.det (D.embed a'))⁻¹ : Kˣ) : K) := rfl
    rw [hbd, hbd'] at h1
    rw [uc22s2112r34q35_blk5_mul, uc22s2112r34q35_blk5_mul] at h1
    simp only [mul_one] at h1
    exact uc22s2112r34q35_blk5_inj h1
  have hN'_A : ∀ a ∈ R, ∃ a' ∈ R,
      Aunit⁻¹ * D.embed a * Aunit = D.embed a' := by
    intro a ha
    obtain ⟨a', ha'R, ha'conj⟩ := hN' a ha
    refine ⟨a', ha'R, ?_⟩
    apply Units.ext
    change A' * (D.embed a : Matrix (Fin 4) (Fin 4) K) * A =
      (D.embed a' : Matrix (Fin 4) (Fin 4) K)
    have h1 := congrArg (fun g : GL (Fin 5) K =>
      (g : Matrix (Fin 5) (Fin 5) K)) ha'conj
    rw [Units.val_mul, Units.val_mul, hmat1', hmat] at h1
    have hbd : ((uc22s2112r34q35_blockDet K (D.embed a) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) =
        uc22s2112r34q35_blk5 (D.embed a : Matrix (Fin 4) (Fin 4) K)
          (((Matrix.GeneralLinearGroup.det (D.embed a))⁻¹ : Kˣ) : K) := rfl
    have hbd' : ((uc22s2112r34q35_blockDet K (D.embed a') : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) =
        uc22s2112r34q35_blk5 (D.embed a' : Matrix (Fin 4) (Fin 4) K)
          (((Matrix.GeneralLinearGroup.det (D.embed a'))⁻¹ : Kˣ) : K) := rfl
    rw [hbd, hbd'] at h1
    rw [uc22s2112r34q35_blk5_mul, uc22s2112r34q35_blk5_mul] at h1
    simp only [one_mul] at h1
    exact uc22s2112r34q35_blk5_inj h1
  have hAunit_s : Aunit ^ s = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val]
    change A ^ s = 1
    exact hA_s
  have hAunit1 : Aunit = 1 :=
    uc22s2112r34q35_eq_one_of_normalizes_embed hn D R hsep he₁ he₂ hy₀₁ hy₂₃ hy₀₂
      h₀₁ h₂₃ h₀₂ hz hs hs2 hAunit_s hGL hN_A hN'_A
  have hA1 : A = 1 := by
    have h1 := congrArg Units.val hAunit1
    simpa [Aunit] using h1
  have hmat_final : (((h : GL (Fin 5) K)) : Matrix (Fin 5) (Fin 5) K) = 1 := by
    rw [hmat, hmu1, hA1, uc22s2112r34q35_blk5_one]
  exact Units.ext hmat_final




end CFSG.LocalAnalysis.UniquenessCase.UC22
