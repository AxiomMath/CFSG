module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Classify
public import CFSG.CharacterTheory.Semidihedral.MatrixTorus

public noncomputable section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open Matrix CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag

variable {K : Type} [Field K]

private def a1413OrdSwap2 (K : Type) [Field K] : Matrix (Fin 2) (Fin 2) K := !![0, 1; 1, 0]

private def a1413OrdSwapMat (K : Type) [Field K] :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K :=
  fromBlocks (a1413OrdSwap2 K) 0 0 (a1413OrdSwap2 K)

private theorem a1413OrdSwap2_mul_self : a1413OrdSwap2 K * a1413OrdSwap2 K = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a1413OrdSwap2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem a1413OrdSwap2_mul_diag2 (a b : K) :
    a1413OrdSwap2 K * diag2 a b * a1413OrdSwap2 K = diag2 b a := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [a1413OrdSwap2, diag2, Matrix.mul_apply, Fin.sum_univ_two]

private theorem a1413OrdSwapMat_mul_blk (g h : Matrix (Fin 2) (Fin 2) K) :
    a1413OrdSwapMat K * blk g h * a1413OrdSwapMat K = blk h g := by
  simp only [a1413OrdSwapMat, blk, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, a1413OrdSwap2_mul_diag2]

private theorem a1413OrdSwapMat_transpose : (a1413OrdSwapMat K)ᵀ = a1413OrdSwapMat K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [a1413OrdSwapMat, a1413OrdSwap2, Matrix.transpose_apply]

private theorem a1413OrdSwapMat_mul_self : a1413OrdSwapMat K * a1413OrdSwapMat K = 1 := by
  simp only [a1413OrdSwapMat, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, a1413OrdSwap2_mul_self, Matrix.fromBlocks_one]

private theorem a1413OrdSwapMat_symplectic :
    (a1413OrdSwapMat K)ᵀ * formJ 2 K * a1413OrdSwapMat K = formJ 2 K := by
  rw [a1413OrdSwapMat_transpose, formJ_eq_blk, a1413OrdSwapMat_mul_blk]

private def a1413OrdSwapSp : StatedSp 2 K :=
  toSp (a1413OrdSwapMat K) (a1413OrdSwapMat_symplectic (K := K))

private theorem a1413OrdSwapSp_mul_self :
    a1413OrdSwapSp (K := K) * a1413OrdSwapSp (K := K) = 1 := by
  apply sp_ext
  simp [a1413OrdSwapSp, a1413OrdSwapMat_mul_self, Subgroup.coe_mul, Units.val_mul]

private theorem a1413OrdSwapMat_entry :
    (a1413OrdSwapMat K) (Sum.inl 0) (Sum.inl 0) = 0 := by
  simp [a1413OrdSwapMat, a1413OrdSwap2]

private theorem a1413OrdSwapSp_entry :
    (((a1413OrdSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0) = 0 := by
  unfold a1413OrdSwapSp
  rw [coe_toSp, a1413OrdSwapMat_entry]

private theorem a1413OrdSwapSp_ne_one :
    (((a1413OrdSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 1 := by
  intro h
  have he : (((a1413OrdSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0) = 1 := by
    rw [h]; simp
  rw [a1413OrdSwapSp_entry] at he
  exact zero_ne_one he

private theorem a1413OrdSwapSp_ne_neg_one :
    (((a1413OrdSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ -1 := by
  intro h
  have he : (((a1413OrdSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (Sum.inl 0) (Sum.inl 0) = -1 := by
    rw [h]; simp
  rw [a1413OrdSwapSp_entry] at he
  exact (neg_ne_zero.mpr one_ne_zero) he.symm

private theorem a1413Ord_conjSwap_blkSL (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    a1413OrdSwapSp (K := K) * blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) =
      blkSL K (x⁻¹, x) := by
  apply sp_ext
  unfold a1413OrdSwapSp
  simp only [Subgroup.coe_mul, Units.val_mul, coe_toSp, coe_blkSL]
  exact a1413OrdSwapMat_mul_blk _ _

private lemma a1413Ord_sigma'_entry (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((((blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) : StatedSp 2 K) :
        GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inl 0)) = 0 := by
  unfold a1413OrdSwapSp
  simp only [Subgroup.coe_mul, Units.val_mul, coe_toSp, coe_blkSL, a1413OrdSwapMat, blk,
    Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero,
    zero_add, Matrix.fromBlocks_apply₁₁]
  simp [Matrix.mul_apply, Fin.sum_univ_two, diag2, a1413OrdSwap2]

private theorem a1413Ord_sigma'_ne_one (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ 1 := by
  intro h
  have he : ((((blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inl 0)) = 1 := by
    rw [h]; simp
  rw [a1413Ord_sigma'_entry] at he
  exact zero_ne_one he

private theorem a1413Ord_sigma'_ne_neg_one (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    (((blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) ≠ -1 := by
  intro h
  have he : ((((blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
      (Sum.inl 0) (Sum.inl 0)) = -1 := by
    rw [h]; simp
  rw [a1413Ord_sigma'_entry] at he
  exact (neg_ne_zero.mpr one_ne_zero) he.symm

private theorem a1413Ord_sigma_sq (x : Matrix.SpecialLinearGroup (Fin 2) K) :
    (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) *
      (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) = 1 := by
  calc (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) *
        (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K))
      = blkSL K (x, x⁻¹) * (a1413OrdSwapSp (K := K) * blkSL K (x, x⁻¹) *
          a1413OrdSwapSp (K := K)) := by group
    _ = blkSL K (x, x⁻¹) * blkSL K (x⁻¹, x) := by rw [a1413Ord_conjSwap_blkSL]
    _ = blkSL K ((x, x⁻¹) * (x⁻¹, x)) := by rw [← map_mul]
    _ = blkSL K 1 := by
      rw [show (x, x⁻¹) * (x⁻¹, x) = 1 from
        Prod.ext (mul_inv_cancel x) (by simpa using mul_inv_cancel x⁻¹)]
    _ = 1 := map_one _

private lemma a1413Ord_half_dvd_of_dvd {N k : ℕ} (hN2 : 2 ∣ N) (h : N ∣ k) :
    N / 2 ∣ k := by
  have h1 : N / 2 ∣ N := ⟨2, by rw [mul_comm, Nat.mul_div_cancel' hN2]⟩
  exact dvd_trans h1 h

private lemma a1413Ord_half_dvd_of_dvd_two_mul {N k : ℕ} (hN2 : 2 ∣ N) (h : N ∣ 2 * k) :
    N / 2 ∣ k := by
  have h' : 2 * (N / 2) ∣ 2 * k := by rwa [Nat.mul_div_cancel' hN2]
  exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < (2 : ℕ))).mp h'

private lemma a1413Ord_prod_pow (x : Matrix.SpecialLinearGroup (Fin 2) K) (k : ℕ) :
    ((x⁻¹, x) : Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) ^ k = ((x⁻¹) ^ k, x ^ k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih, pow_succ, pow_succ]; rfl

private lemma a1413Ord_pow_eq_pm_one_iff (x : Matrix.SpecialLinearGroup (Fin 2) K)
    (N : ℕ) (hN2 : 2 ∣ N) (hxN : orderOf x = N) (h2 : (2 : K) ≠ 0) (k : ℕ) :
    (x ^ k = 1 ∨ x ^ k = -1) ↔ N / 2 ∣ k := by
  constructor
  · rintro (h | h)
    · have hdvd : N ∣ k := by
        rw [← hxN, orderOf_dvd_iff_pow_eq_one]
        exact h
      exact a1413Ord_half_dvd_of_dvd hN2 hdvd
    · have hsq : (x ^ k) ^ 2 = 1 := by rw [h]; norm_num
      have hdvd : N ∣ 2 * k := by
        rw [← hxN, orderOf_dvd_iff_pow_eq_one, show 2 * k = k * 2 by ring, pow_mul]
        exact hsq
      exact a1413Ord_half_dvd_of_dvd_two_mul hN2 hdvd
  · intro h
    have h2k : x ^ (2 * k) = 1 := by
      obtain ⟨m, rfl⟩ := h
      rw [show 2 * (N / 2 * m) = N * m by rw [← mul_assoc, Nat.mul_div_cancel' hN2]]
      rw [pow_mul, ← hxN, pow_orderOf_eq_one, one_pow]
    have hsq : (x ^ k) ^ 2 = 1 := by
      rw [← pow_mul, show k * 2 = 2 * k by ring, h2k]
    have hgg : ((x ^ k : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) * ((x ^ k : Matrix.SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K) = 1 := by
      have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) K =>
        (z : Matrix (Fin 2) (Fin 2) K)) hsq
      simpa [Matrix.SpecialLinearGroup.coe_mul, pow_two] using this
    rcases eq_one_or_neg_one_of_sq h2 (x ^ k).2 hgg with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h

private lemma a1413Ord_exists_sl2_good_order (K : Type) [Field K] [Finite K]
    (hodd : Odd (Nat.card K)) (h7 : 7 ≤ Nat.card K) :
    ∃ (x : Matrix.SpecialLinearGroup (Fin 2) K) (N : ℕ), 4 ∣ N ∧ 8 ≤ N ∧
      orderOf x = N ∧ ∀ k : ℕ, (x ^ k = 1 ∨ x ^ k = -1) ↔ N / 2 ∣ k := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  have hmod := Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hodd)
  rcases hmod with h1 | h3
  · let a : Kˣ := -1
    have hsq : IsSquare (-(a : K)) := by
      rw [show -(a : K) = 1 by simp [a]]
      exact IsSquare.one
    have hcyc : IsCyclic (CFSG.Semidihedral.MatrixTorus.Torus K a) :=
      CFSG.Semidihedral.MatrixTorus.split_torus_cyclic K a h2 hsq
    have hcard : Nat.card (CFSG.Semidihedral.MatrixTorus.Torus K a) = Nat.card K - 1 :=
      CFSG.Semidihedral.MatrixTorus.split_torus_card K a h2 hsq
    obtain ⟨x₀, hx₀⟩ := (isCyclic_iff_exists_orderOf_eq_natCard
      (α := CFSG.Semidihedral.MatrixTorus.Torus K a)).mp hcyc
    have h4N : 4 ∣ Nat.card K - 1 :=
      ⟨Nat.card K / 4, by have := Nat.mod_add_div (Nat.card K) 4; omega⟩
    have h8N : 8 ≤ Nat.card K - 1 := by
      have := Nat.mod_add_div (Nat.card K) 4; omega
    have hxN : orderOf ((x₀ : CFSG.Semidihedral.MatrixTorus.Torus K a) :
        Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K - 1 := by
      rw [Subgroup.orderOf_coe, hx₀, hcard]
    refine ⟨(x₀ : Matrix.SpecialLinearGroup (Fin 2) K), Nat.card K - 1, h4N, h8N, hxN, ?_⟩
    intro k
    exact a1413Ord_pow_eq_pm_one_iff _ _ (dvd_trans (by norm_num : 2 ∣ 4) h4N) hxN h2 k
  · let a : Kˣ := 1
    haveI : Fintype K := Fintype.ofFinite K
    have hnsq : ¬ IsSquare (-(a : K)) := by
      rw [show -(a : K) = -1 by simp [a], FiniteField.isSquare_neg_one_iff, not_not,
        ← Nat.card_eq_fintype_card]
      exact h3
    have hcyc : IsCyclic (CFSG.Semidihedral.MatrixTorus.Torus K a) :=
      CFSG.Semidihedral.MatrixTorus.nonsplit_torus_cyclic K a hnsq
    have hcard : Nat.card (CFSG.Semidihedral.MatrixTorus.Torus K a) = Nat.card K + 1 :=
      CFSG.Semidihedral.MatrixTorus.nonsplit_torus_card K a hnsq
    obtain ⟨x₀, hx₀⟩ := (isCyclic_iff_exists_orderOf_eq_natCard
      (α := CFSG.Semidihedral.MatrixTorus.Torus K a)).mp hcyc
    have h4N : 4 ∣ Nat.card K + 1 :=
      ⟨Nat.card K / 4 + 1, by have := Nat.mod_add_div (Nat.card K) 4; omega⟩
    have h8N : 8 ≤ Nat.card K + 1 := by omega
    have hxN : orderOf ((x₀ : CFSG.Semidihedral.MatrixTorus.Torus K a) :
        Matrix.SpecialLinearGroup (Fin 2) K) = Nat.card K + 1 := by
      rw [Subgroup.orderOf_coe, hx₀, hcard]
    refine ⟨(x₀ : Matrix.SpecialLinearGroup (Fin 2) K), Nat.card K + 1, h4N, h8N, hxN, ?_⟩
    intro k
    exact a1413Ord_pow_eq_pm_one_iff _ _ (dvd_trans (by norm_num : 2 ∣ 4) h4N) hxN h2 k

private lemma a1413Ord_proj_blkSL_eq_one_iff (x : Matrix.SpecialLinearGroup (Fin 2) K)
    (k : ℕ) : proj 2 K (blkSL K ((x⁻¹) ^ k, x ^ k)) = 1 ↔ x ^ k = 1 ∨ x ^ k = -1 := by
  rw [proj_blkSL_eq_one_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
    · left
      have h' : (x⁻¹) ^ k = 1 := Subtype.ext h1
      rw [inv_pow] at h'
      exact inv_eq_one.mp h'
    · right
      have h' : (x⁻¹) ^ k = -1 := Subtype.ext h1
      rw [inv_pow] at h'
      rw [← inv_inv (x ^ k), h', inv_neg, inv_one]
  · rintro (h | h)
    · left
      refine ⟨?_, ?_⟩
      · have h' : (x⁻¹) ^ k = 1 := by rw [inv_pow, h, inv_one]
        rw [h']; simp
      · rw [h]; simp
    · right
      refine ⟨?_, ?_⟩
      · have h' : (x⁻¹) ^ k = -1 := by rw [inv_pow, h, inv_neg, inv_one]
        rw [h']; simp
      · rw [h]; simp

theorem psp4_exists_bad_pair {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h7 : 7 ≤ Nat.card K) :
    ∃ g : StatedProj (StatedSp 2 K), Even (orderOf (u1 K * (g * u1 K * g⁻¹))) ∧
      2 < orderOf (u1 K * (g * u1 K * g⁻¹)) := by
  have h2 : (2 : K) ≠ 0 := CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card K hodd
  obtain ⟨x, N, h4N, h8N, hxN, hxpm⟩ := a1413Ord_exists_sl2_good_order K hodd h7
  have hN2 : 2 ∣ N := dvd_trans (by norm_num : 2 ∣ 4) h4N
  have hσ2 : (((a1413OrdSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((a1413OrdSwapSp (K := K) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    have h := a1413OrdSwapSp_mul_self (K := K)
    have hc := congrArg (fun z : StatedSp 2 K => (((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) h
    simpa [Subgroup.coe_mul, Units.val_mul] using hc
  obtain ⟨g₁, hg₁⟩ := exists_conj_T1 h2 (a1413OrdSwapSp (K := K)) hσ2
    (a1413OrdSwapSp_ne_one (K := K)) (a1413OrdSwapSp_ne_neg_one (K := K))
  have hσ'2 : (((blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *
      (((blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K) : StatedSp 2 K) :
      GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) = 1 := by
    have h := a1413Ord_sigma_sq x
    have hc := congrArg (fun z : StatedSp 2 K => (((z : GL (Fin 2 ⊕ Fin 2) K) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K))) h
    simpa [Subgroup.coe_mul, Units.val_mul] using hc
  obtain ⟨g₂, hg₂⟩ := exists_conj_T1 h2 (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) hσ'2
    (a1413Ord_sigma'_ne_one x) (a1413Ord_sigma'_ne_neg_one x)
  let r₁ : StatedProj (StatedSp 2 K) := proj 2 K g₁
  let r₂ : StatedProj (StatedSp 2 K) := proj 2 K g₂
  have hσconj : proj 2 K (a1413OrdSwapSp (K := K)) = r₁ * u1 K * r₁⁻¹ := by
    have h1 : r₁⁻¹ * proj 2 K (a1413OrdSwapSp (K := K)) * r₁ = u1 K := by
      have hc := congrArg (proj 2 K) hg₁
      dsimp only [r₁]
      simpa only [map_mul, map_inv, u1] using hc
    rw [← h1]; group
  have hσ'conj : proj 2 K (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) =
      r₂ * u1 K * r₂⁻¹ := by
    have h1 : r₂⁻¹ * proj 2 K (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) * r₂ = u1 K := by
      have hc := congrArg (proj 2 K) hg₂
      dsimp only [r₂]
      simpa only [map_mul, map_inv, u1] using hc
    rw [← h1]; group
  have hprod : proj 2 K (a1413OrdSwapSp (K := K)) *
      proj 2 K (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) =
      proj 2 K (blkSL K (x⁻¹, x)) := by
    rw [← map_mul, ← mul_assoc, a1413Ord_conjSwap_blkSL]
  have hu1 : u1 K = r₁⁻¹ * proj 2 K (a1413OrdSwapSp (K := K)) * r₁ := by
    rw [hσconj]; group
  have hgconj : (r₁⁻¹ * r₂) * u1 K * (r₁⁻¹ * r₂)⁻¹ =
      r₁⁻¹ * proj 2 K (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K)) * r₁ := by
    rw [hσ'conj]; group
  have hmain1 : u1 K * ((r₁⁻¹ * r₂) * u1 K * (r₁⁻¹ * r₂)⁻¹) =
      r₁⁻¹ * (proj 2 K (a1413OrdSwapSp (K := K)) *
        proj 2 K (blkSL K (x, x⁻¹) * a1413OrdSwapSp (K := K))) * r₁ := by
    rw [hgconj, hu1]; group
  have hmain : u1 K * ((r₁⁻¹ * r₂) * u1 K * (r₁⁻¹ * r₂)⁻¹) =
      r₁⁻¹ * proj 2 K (blkSL K (x⁻¹, x)) * r₁ := by
    rw [hmain1, hprod]
  have horder : orderOf (u1 K * ((r₁⁻¹ * r₂) * u1 K * (r₁⁻¹ * r₂)⁻¹)) =
      orderOf (proj 2 K (blkSL K (x⁻¹, x))) := by
    rw [hmain]
    exact (SemiconjBy.orderOf_eq r₁⁻¹ (x := proj 2 K (blkSL K (x⁻¹, x)))
      (y := r₁⁻¹ * proj 2 K (blkSL K (x⁻¹, x)) * r₁) (by unfold SemiconjBy; group)).symm
  have hker : ∀ k : ℕ, (proj 2 K (blkSL K (x⁻¹, x))) ^ k = 1 ↔ N / 2 ∣ k := by
    intro k
    rw [show (proj 2 K (blkSL K (x⁻¹, x))) ^ k =
        proj 2 K (blkSL K ((x⁻¹) ^ k, x ^ k)) from by
      rw [← map_pow (proj 2 K) (blkSL K (x⁻¹, x)) k, ← map_pow (blkSL K) (x⁻¹, x) k,
        a1413Ord_prod_pow x k]]
    exact (a1413Ord_proj_blkSL_eq_one_iff x k).trans (hxpm k)
  have hord : orderOf (proj 2 K (blkSL K (x⁻¹, x))) = N / 2 := by
    rw [orderOf_eq_iff (by omega : 0 < N / 2)]
    refine ⟨(hker (N / 2)).mpr (dvd_refl _), ?_⟩
    intro m hm hm0 h1
    exact Nat.not_dvd_of_pos_of_lt hm0 hm ((hker m).mp h1)
  have hEven : Even (N / 2) := by
    rw [even_iff_two_dvd]
    exact (Nat.dvd_div_iff_mul_dvd hN2).mpr (by rw [show (2 : ℕ) * 2 = 4 by norm_num]; exact h4N)
  have hgt : 2 < N / 2 := by omega
  exact ⟨r₁⁻¹ * r₂, by rw [horder, hord]; exact hEven, by rw [horder, hord]; exact hgt⟩

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
