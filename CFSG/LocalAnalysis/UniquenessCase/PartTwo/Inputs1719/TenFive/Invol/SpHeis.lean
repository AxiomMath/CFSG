module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.Heis
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticTwoRadical
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive

open CFSG.Open Subgroup Matrix
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

variable {r : ℕ} {K : Type} [Field K]

@[expose] def spForm (y z : Fin r ⊕ Fin r → K) : K :=
  y ⬝ᵥ (formJ r K *ᵥ z)

@[expose] def spT (c a : Fin r ⊕ Fin r → K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  vecMulVec a (formJ r K *ᵥ c)

@[expose] def spN (a c : Fin r ⊕ Fin r → K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  spT c a + spT a c

private theorem formJ_transpose : (formJ r K)ᵀ = -formJ r K := by
  simp [formJ, Matrix.fromBlocks_transpose, Matrix.fromBlocks_neg]

theorem spT_mulVec (c a y : Fin r ⊕ Fin r → K) : spT c a *ᵥ y = spForm y c • a := by
  rw [spT, Matrix.vecMulVec_mulVec, op_smul_eq_smul, spForm, dotProduct_comm]

theorem spForm_swap (y z : Fin r ⊕ Fin r → K) : spForm z y = -spForm y z := by
  rw [spForm, spForm, Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.vecMul_transpose,
    formJ_transpose, Matrix.vecMul_neg]
  simp

theorem spForm_self (y : Fin r ⊕ Fin r → K) : spForm y y = 0 := by
  simp [spForm, dotProduct, Fintype.sum_sum_type, mulVec, fromBlocks, Matrix.one_apply, mul_comm]

theorem spT_mul_spT (c a c' a' : Fin r ⊕ Fin r → K) :
    spT c a * spT c' a' = spForm a' c • spT c' a := by
  simp only [spT]
  rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_smul, spForm, dotProduct_comm]

theorem spN_comm (a c : Fin r ⊕ Fin r → K) : spN a c = spN c a :=
  add_comm _ _

private theorem vecMul_formJ_eq_neg (a : Fin r ⊕ Fin r → K) :
    a ᵥ* formJ r K = -(formJ r K *ᵥ a) := by
  have h := Matrix.vecMul_transpose (formJ r K) a
  rw [formJ_transpose, Matrix.vecMul_neg] at h
  exact neg_eq_iff_eq_neg.mp h

private theorem transpose_spT_mul_formJ (c a : Fin r ⊕ Fin r → K) :
    (spT c a)ᵀ * formJ r K = -vecMulVec (formJ r K *ᵥ c) (formJ r K *ᵥ a) := by
  rw [spT, Matrix.transpose_vecMulVec, Matrix.vecMulVec_mul, vecMul_formJ_eq_neg,
    Matrix.vecMulVec_neg]

private theorem formJ_mul_spT (c a : Fin r ⊕ Fin r → K) :
    formJ r K * spT c a = vecMulVec (formJ r K *ᵥ a) (formJ r K *ᵥ c) := by
  rw [spT, Matrix.mul_vecMulVec]

theorem isSp_spN (a c : Fin r ⊕ Fin r → K) :
    (spN a c)ᵀ * formJ r K + formJ r K * spN a c = 0 := by
  rw [spN, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, transpose_spT_mul_formJ,
    transpose_spT_mul_formJ, formJ_mul_spT, formJ_mul_spT]
  abel

theorem spN_mul_self {a c : Fin r ⊕ Fin r → K} (h : spForm a c = 0) : spN a c * spN a c = 0 := by
  rw [spN, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, spT_mul_spT, spT_mul_spT,
    spT_mul_spT, spT_mul_spT, spForm_self, spForm_self, spForm_swap a c, h]
  simp

theorem transpose_mul_formJ_mul_one_add (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0) :
    (1 + N)ᵀ * formJ r K * (1 + N) = formJ r K := by
  have hNJ : Nᵀ * formJ r K = -(formJ r K * N) := eq_neg_of_add_eq_zero_left hs
  have hzero : Nᵀ * formJ r K + formJ r K * N + Nᵀ * formJ r K * N = 0 := by
    rw [hs, zero_add, hNJ, Matrix.neg_mul, Matrix.mul_assoc, hN, Matrix.mul_zero, neg_zero]
  have h1 : (1 + N)ᵀ * formJ r K * (1 + N) =
      formJ r K + (Nᵀ * formJ r K + formJ r K * N + Nᵀ * formJ r K * N) := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
    noncomm_ring
  rw [h1, hzero, add_zero]

@[expose] def unipSp (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0) : StatedSp r K :=
  ⟨⟨1 + N, 1 - N, by rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hN,
      sub_zero, sub_add_cancel], by rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_add,
      Matrix.mul_one, hN, add_zero, add_sub_cancel_right]⟩,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr
      (transpose_mul_formJ_mul_one_add N hs hN)⟩

@[simp] theorem coe_unipSp (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0) :
    (((unipSp N hs hN : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = 1 + N :=
  rfl

theorem isSp_neg {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) : (-N)ᵀ * formJ r K + formJ r K * (-N) = 0 := by
  rw [transpose_neg, Matrix.neg_mul, Matrix.mul_neg, ← neg_add, hs, neg_zero]

theorem neg_mul_self_neg {N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (hN : N * N = 0) :
    (-N) * (-N) = 0 := by
  rw [neg_mul_neg, hN]

theorem unipSp_inv (N : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hs : Nᵀ * formJ r K + formJ r K * N = 0) (hN : N * N = 0) :
    (unipSp N hs hN)⁻¹ = unipSp (-N) (isSp_neg hs) (neg_mul_self_neg hN) := by
  apply inv_eq_of_mul_eq_one_right
  apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
  rw [Subgroup.coe_mul, Units.val_mul, coe_unipSp, coe_unipSp, Subgroup.coe_one, Units.val_one]
  have h : (1 + N) * (1 + -N) = 1 := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, Matrix.mul_neg, hN]
    abel
  exact h

section HeisSp

variable {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}

private def heisM (N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (x : Heis K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  x.a • N₁ + x.b • N₂ + x.c • (N₁ * N₂) + (x.a * x.b - x.c) • (N₂ * N₁)

private def heisMat (N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) (x : Heis K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K :=
  1 + heisM N₁ N₂ x

private theorem heisM_mul_aux {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) :
    (N₁ * N₂) * N₂ = 0 ∧ (N₁ * N₂) * (N₁ * N₂) = 0 ∧ (N₁ * N₂) * (N₂ * N₁) = 0 ∧
    (N₂ * N₁) * N₁ = 0 ∧ (N₂ * N₁) * (N₂ * N₁) = 0 ∧ (N₂ * N₁) * (N₁ * N₂) = 0 ∧
    N₁ * (N₁ * N₂) = 0 ∧ N₂ * (N₁ * N₂) = 0 ∧ N₁ * (N₂ * N₁) = 0 ∧ N₂ * (N₂ * N₁) = 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc (N₁ * N₂) N₁ N₂, h121, Matrix.zero_mul]
  · rw [Matrix.mul_assoc N₁ N₂ (N₂ * N₁), ← Matrix.mul_assoc N₂ N₂ N₁, h2, Matrix.zero_mul,
      Matrix.mul_zero]
  · rw [Matrix.mul_assoc, h1, Matrix.mul_zero]
  · rw [← Matrix.mul_assoc (N₂ * N₁) N₂ N₁, h212, Matrix.zero_mul]
  · rw [Matrix.mul_assoc N₂ N₁ (N₁ * N₂), ← Matrix.mul_assoc N₁ N₁ N₂, h1, Matrix.zero_mul,
      Matrix.mul_zero]
  · rw [← Matrix.mul_assoc, h1, Matrix.zero_mul]
  · simpa only [Matrix.mul_assoc] using h212
  · simpa only [Matrix.mul_assoc] using h121
  · rw [← Matrix.mul_assoc, h2, Matrix.zero_mul]

private theorem heisM_mul {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x y : Heis K) :
    heisM N₁ N₂ x * heisM N₁ N₂ y =
      (x.a * y.b) • (N₁ * N₂) + (x.b * y.a) • (N₂ * N₁) := by
  obtain ⟨hP2, hPP, hPQ, hQ1, hQQ, hQP, h1P, h2P, h1Q, h2Q⟩ :=
    heisM_mul_aux h1 h2 h121 h212
  simp only [heisM, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul, h1, h2, h121, h212, hP2, hPP, hPQ, hQ1, hQQ, hQP, h1P, h2P, h1Q, h2Q,
    smul_zero, add_zero, zero_add]
  module

private theorem heisM_add {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} (x y : Heis K) :
    heisM N₁ N₂ x + heisM N₁ N₂ y +
      ((x.a * y.b) • (N₁ * N₂) + (x.b * y.a) • (N₂ * N₁)) = heisM N₁ N₂ (x * y) := by
  simp only [heisM, Heis.mul_a, Heis.mul_b, Heis.mul_c]
  module

private theorem heisMat_mul {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x y : Heis K) :
    heisMat N₁ N₂ (x * y) = heisMat N₁ N₂ x * heisMat N₁ N₂ y := by
  have hm := heisM_mul h1 h2 h121 h212 x y
  have ha := heisM_add (N₁ := N₁) (N₂ := N₂) x y
  rw [heisMat, heisMat, heisMat]
  rw [show (1 + heisM N₁ N₂ x) * (1 + heisM N₁ N₂ y) =
      1 + (heisM N₁ N₂ x + heisM N₁ N₂ y +
        ((x.a * y.b) • (N₁ * N₂) + (x.b * y.a) • (N₂ * N₁))) by
    rw [← hm]
    noncomm_ring]
  rw [ha]

private theorem heisMat_one {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K} :
    heisMat N₁ N₂ (1 : Heis K) = 1 := by
  simp [heisMat, heisM]

private theorem heisM_P_mul {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) : (N₁ * N₂) * heisM N₁ N₂ x = 0 := by
  obtain ⟨hP2, hPP, hPQ, -, -, -, -, -, -, -⟩ := heisM_mul_aux h1 h2 h121 h212
  simp only [heisM, Matrix.mul_add, Matrix.mul_smul, h121, hP2, hPP, hPQ, smul_zero,
    add_zero]

private theorem heisM_Q_mul {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) : (N₂ * N₁) * heisM N₁ N₂ x = 0 := by
  obtain ⟨-, -, -, hQ1, hQQ, hQP, -, -, -, -⟩ := heisM_mul_aux h1 h2 h121 h212
  simp only [heisM, Matrix.mul_add, Matrix.mul_smul, hQ1, h212, hQQ, hQP, smul_zero,
    add_zero]

private theorem heisM_sq {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) :
    heisM N₁ N₂ x * heisM N₁ N₂ x = (x.a * x.b) • (N₁ * N₂ + N₂ * N₁) := by
  rw [heisM_mul h1 h2 h121 h212 x x, mul_comm x.b x.a, ← smul_add]

private theorem heisM_cube {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) : heisM N₁ N₂ x ^ 3 = 0 := by
  have hP := heisM_P_mul h1 h2 h121 h212 x
  have hQ := heisM_Q_mul h1 h2 h121 h212 x
  have h3 : heisM N₁ N₂ x ^ 3 = heisM N₁ N₂ x * heisM N₁ N₂ x * heisM N₁ N₂ x := by
    rw [pow_succ, pow_succ, pow_one]
  rw [h3, heisM_sq h1 h2 h121 h212 x, Matrix.smul_mul, Matrix.add_mul, hP, hQ, add_zero,
    smul_zero]

private theorem transpose_mul_formJ_mul {A B : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hA : Aᵀ * formJ r K = -(formJ r K * A)) (hB : Bᵀ * formJ r K = -(formJ r K * B)) :
    (A * B)ᵀ * formJ r K = formJ r K * (B * A) := by
  rw [Matrix.transpose_mul]
  calc Bᵀ * Aᵀ * formJ r K = Bᵀ * (Aᵀ * formJ r K) := by rw [Matrix.mul_assoc]
    _ = Bᵀ * (-(formJ r K * A)) := by rw [hA]
    _ = -((Bᵀ * formJ r K) * A) := by rw [Matrix.mul_neg, Matrix.mul_assoc]
    _ = -((-(formJ r K * B)) * A) := by rw [hB]
    _ = formJ r K * (B * A) := by rw [Matrix.neg_mul, neg_neg, Matrix.mul_assoc]

private theorem heisM_transpose_add {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0)
    (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0) (x : Heis K) :
    (heisM N₁ N₂ x)ᵀ * formJ r K + formJ r K * heisM N₁ N₂ x =
      (x.a * x.b) • (formJ r K * (N₁ * N₂) + formJ r K * (N₂ * N₁)) := by
  have hN1 : N₁ᵀ * formJ r K = -(formJ r K * N₁) := eq_neg_of_add_eq_zero_left hs₁
  have hN2 : N₂ᵀ * formJ r K = -(formJ r K * N₂) := eq_neg_of_add_eq_zero_left hs₂
  simp only [heisM, Matrix.transpose_add, Matrix.transpose_smul, Matrix.add_mul, Matrix.smul_mul,
    Matrix.mul_add, Matrix.mul_smul, hN1, hN2, transpose_mul_formJ_mul hN1 hN2,
    transpose_mul_formJ_mul hN2 hN1]
  module

private theorem heisM_transpose_mul {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0)
    (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) :
    (heisM N₁ N₂ x)ᵀ * formJ r K * heisM N₁ N₂ x =
      -((x.a * x.b) • (formJ r K * (N₁ * N₂) + formJ r K * (N₂ * N₁))) := by
  have hS := heisM_transpose_add hs₁ hs₂ x
  have hP := heisM_P_mul h1 h2 h121 h212 x
  have hQ := heisM_Q_mul h1 h2 h121 h212 x
  have hSq := heisM_sq h1 h2 h121 h212 x
  have hSM : ((x.a * x.b) • (formJ r K * (N₁ * N₂) + formJ r K * (N₂ * N₁))) *
      heisM N₁ N₂ x = 0 := by
    rw [Matrix.smul_mul]
    have h : (formJ r K * (N₁ * N₂) + formJ r K * (N₂ * N₁)) * heisM N₁ N₂ x = 0 := by
      rw [Matrix.add_mul, Matrix.mul_assoc (formJ r K) (N₁ * N₂) (heisM N₁ N₂ x),
        Matrix.mul_assoc (formJ r K) (N₂ * N₁) (heisM N₁ N₂ x), hP, hQ, Matrix.mul_zero,
        add_zero]
    rw [h, smul_zero]
  have hJM : formJ r K * (heisM N₁ N₂ x * heisM N₁ N₂ x) =
      (x.a * x.b) • (formJ r K * (N₁ * N₂) + formJ r K * (N₂ * N₁)) := by
    rw [hSq, Matrix.mul_smul, Matrix.mul_add]
  have hsplit : (heisM N₁ N₂ x)ᵀ * formJ r K =
      (x.a * x.b) • (formJ r K * (N₁ * N₂) + formJ r K * (N₂ * N₁)) -
        formJ r K * heisM N₁ N₂ x := by
    rw [← hS]
    abel
  rw [hsplit, Matrix.sub_mul, hSM, Matrix.mul_assoc, hJM, zero_sub]

private theorem heisM_transpose_add_self {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0)
    (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) :
    (heisM N₁ N₂ x)ᵀ * formJ r K + formJ r K * heisM N₁ N₂ x +
      (heisM N₁ N₂ x)ᵀ * formJ r K * heisM N₁ N₂ x = 0 := by
  rw [heisM_transpose_add hs₁ hs₂ x, heisM_transpose_mul hs₁ hs₂ h1 h2 h121 h212 x,
    add_neg_cancel]

private theorem one_add_isSp_of {M : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hM : Mᵀ * formJ r K + formJ r K * M + Mᵀ * formJ r K * M = 0) :
    (1 + M)ᵀ * formJ r K * (1 + M) = formJ r K := by
  have h1 : (1 + M)ᵀ * formJ r K * (1 + M) =
      formJ r K + (Mᵀ * formJ r K + formJ r K * M + Mᵀ * formJ r K * M) := by
    rw [Matrix.transpose_add, Matrix.transpose_one]
    noncomm_ring
  rw [h1, hM, add_zero]

private def heisSpFun (N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0)
    (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) : StatedSp r K :=
  ⟨⟨heisMat N₁ N₂ x, heisMat N₁ N₂ x⁻¹,
    by rw [← heisMat_mul h1 h2 h121 h212 x x⁻¹, mul_inv_cancel, heisMat_one],
    by rw [← heisMat_mul h1 h2 h121 h212 x⁻¹ x, inv_mul_cancel, heisMat_one]⟩,
   CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff.mpr (by
     simpa [heisMat] using
       one_add_isSp_of (heisM_transpose_add_self hs₁ hs₂ h1 h2 h121 h212 x))⟩

private theorem coe_heisSpFun (N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0)
    (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (x : Heis K) :
    (((heisSpFun N₁ N₂ hs₁ hs₂ h1 h2 h121 h212 x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) = heisMat N₁ N₂ x :=
  rfl

private def heisSpHom (N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0)
    (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) : Heis K →* StatedSp r K where
  toFun := heisSpFun N₁ N₂ hs₁ hs₂ h1 h2 h121 h212
  map_one' := by
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [coe_heisSpFun, Subgroup.coe_one, Units.val_one]
    exact heisMat_one
  map_mul' x y := by
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [Subgroup.coe_mul, Units.val_mul, coe_heisSpFun, coe_heisSpFun, coe_heisSpFun]
    exact heisMat_mul h1 h2 h121 h212 x y

private theorem heisM_eq_zero_of_proj_eq_one {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0)
    (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (hr : 1 ≤ r) {x : Heis K}
    (hx : (proj r K) (heisSpFun N₁ N₂ hs₁ hs₂ h1 h2 h121 h212 x) = 1) :
    heisM N₁ N₂ x = 0 := by
  classical
  have hscal : heisSpFun N₁ N₂ hs₁ hs₂ h1 h2 h121 h212 x ∈
      CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars r K := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj]
    exact hx
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.spScalars, Subgroup.mem_subgroupOf,
    CFSG.Open.StatedScalars, MonoidHom.mem_range] at hscal
  obtain ⟨d, hd⟩ := hscal
  have hdM : heisMat N₁ N₂ x = (d : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have h := congrArg (fun g : GL (Fin r ⊕ Fin r) K =>
      (g : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) hd
    rw [coe_heisSpFun] at h
    rw [← h, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      ← Matrix.smul_one_eq_diagonal]
  have hMscalar : heisM N₁ N₂ x =
      ((d : K) - 1) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have h' : (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + heisM N₁ N₂ x =
        (d : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
      rw [← heisMat, hdM]
    calc heisM N₁ N₂ x =
        ((1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + heisM N₁ N₂ x) - 1 := by abel
      _ = (d : K) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) - 1 := by rw [h']
      _ = ((d : K) - 1) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
          rw [sub_smul, one_smul]
  have hcube : heisM N₁ N₂ x ^ 3 = 0 := heisM_cube h1 h2 h121 h212 x
  have hpow : (((d : K) - 1) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) ^ 3 =
      (((d : K) - 1) ^ 3) • (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    simp [Matrix.smul_one_eq_diagonal, Matrix.diagonal_pow]
  have hr0 : 0 < r := by omega
  have hcz : ((d : K) - 1) ^ 3 = 0 := by
    rw [hMscalar, hpow] at hcube
    have h00 := congrFun (congrFun hcube (Sum.inl ⟨0, hr0⟩)) (Sum.inl ⟨0, hr0⟩)
    simpa using h00
  have hd1 : (d : K) = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hcz)
  rw [hMscalar, hd1, sub_self, zero_smul]

private theorem heis_eq_one_of_heisM_eq_zero {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h1 : N₁ * N₁ = 0) (h2 : N₂ * N₂ = 0) (h121 : N₁ * N₂ * N₁ = 0)
    (h212 : N₂ * N₁ * N₂ = 0) (h12 : N₁ * N₂ ≠ 0) (hPQ : N₁ * N₂ ≠ N₂ * N₁)
    {x : Heis K} (hM0 : heisM N₁ N₂ x = 0) : x = 1 := by
  have h1N : N₁ * (N₁ * N₂) = 0 := by rw [← Matrix.mul_assoc, h1, Matrix.zero_mul]
  have h1Q : N₁ * (N₂ * N₁) = 0 := by rw [← Matrix.mul_assoc]; exact h121
  have hPN : (N₁ * N₂) * N₂ = 0 := by rw [Matrix.mul_assoc, h2, Matrix.mul_zero]
  have hN1M : N₁ * heisM N₁ N₂ x = x.b • (N₁ * N₂) := by
    simp only [heisM, Matrix.mul_add, Matrix.mul_smul, h1, h1N, h1Q, smul_zero, zero_add,
      add_zero]
  have hMN2 : heisM N₁ N₂ x * N₂ = x.a • (N₁ * N₂) := by
    simp only [heisM, Matrix.add_mul, Matrix.smul_mul, h2, hPN, h212, smul_zero,
      add_zero]
  have hb0 : x.b = 0 := by
    have hbP : x.b • (N₁ * N₂) = 0 := by rw [← hN1M, hM0, Matrix.mul_zero]
    rcases smul_eq_zero.mp hbP with h | h
    · exact h
    · exact absurd h h12
  have ha0 : x.a = 0 := by
    have haP : x.a • (N₁ * N₂) = 0 := by rw [← hMN2, hM0, Matrix.zero_mul]
    rcases smul_eq_zero.mp haP with h | h
    · exact h
    · exact absurd h h12
  have hcP : heisM N₁ N₂ x = x.c • (N₁ * N₂ - N₂ * N₁) := by
    simp only [heisM, ha0, hb0, zero_mul, zero_sub, zero_smul, zero_add, add_zero]
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub]
  have hc0 : x.c = 0 := by
    have hsub : N₁ * N₂ - N₂ * N₁ ≠ 0 := sub_ne_zero.mpr hPQ
    have h : x.c • (N₁ * N₂ - N₂ * N₁) = 0 := by rw [← hcP, hM0]
    rcases smul_eq_zero.mp h with h | h
    · exact h
    · exact absurd h hsub
  ext <;> simp [ha0, hb0, hc0]

end HeisSp

theorem exists_heis_projectiveSp (hr : 1 ≤ r) {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0) (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0) (h₁₂₁ : N₁ * N₂ * N₁ = 0) (h₂₁₂ : N₂ * N₁ * N₂ = 0)
    (h₁₂ : N₁ * N₂ ≠ 0) (hPQ : N₁ * N₂ ≠ N₂ * N₁) :
    ∃ ι : Heis K →* StatedProj (StatedSp r K), Function.Injective ι ∧
      ι ⟨1, 0, 0⟩ = proj r K (unipSp N₁ hs₁ h₁) ∧
      ∀ (c : K) (hs : (c • (N₁ * N₂ - N₂ * N₁))ᵀ * formJ r K +
          formJ r K * (c • (N₁ * N₂ - N₂ * N₁)) = 0)
        (hN : c • (N₁ * N₂ - N₂ * N₁) * (c • (N₁ * N₂ - N₂ * N₁)) = 0),
        ι ⟨0, 0, c⟩ = proj r K (unipSp (c • (N₁ * N₂ - N₂ * N₁)) hs hN) := by
  refine ⟨(proj r K).comp (heisSpHom N₁ N₂ hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂), ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : (proj r K) (heisSpFun N₁ N₂ hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ x) = 1 := hx
    exact heis_eq_one_of_heisM_eq_zero h₁ h₂ h₁₂₁ h₂₁₂ h₁₂ hPQ
      (heisM_eq_zero_of_proj_eq_one hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ hr hx')
  · apply congrArg (proj r K)
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    change (((heisSpFun N₁ N₂ hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ ⟨1, 0, 0⟩ : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (((unipSp N₁ hs₁ h₁ : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    rw [coe_heisSpFun, coe_unipSp]
    show heisMat N₁ N₂ ⟨1, 0, 0⟩ = (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + N₁
    simp [heisMat, heisM]
  · intro c hs hN
    apply congrArg (proj r K)
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    change (((heisSpFun N₁ N₂ hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ ⟨0, 0, c⟩ : StatedSp r K) :
      GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      (((unipSp (c • (N₁ * N₂ - N₂ * N₁)) hs hN : StatedSp r K) :
        GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)
    rw [coe_heisSpFun, coe_unipSp]
    show heisMat N₁ N₂ ⟨0, 0, c⟩ =
      (1 : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) + c • (N₁ * N₂ - N₂ * N₁)
    simp only [heisMat, heisM, zero_smul, zero_mul,
      zero_sub, zero_add, add_zero]
    rw [neg_smul, ← sub_eq_add_neg, ← smul_sub]

theorem exists_heisSp (hr : 1 ≤ r) {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0) (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0) (h₁₂₁ : N₁ * N₂ * N₁ = 0) (h₂₁₂ : N₂ * N₁ * N₂ = 0)
    (h₁₂ : N₁ * N₂ ≠ 0) (hPQ : N₁ * N₂ ≠ N₂ * N₁) :
    ∃ φ : Heis K →* StatedSp r K, Function.Injective ((proj r K).comp φ) ∧
      ∀ x : Heis K, (((φ x : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
          1 + (x.a • N₁ + x.b • N₂ + x.c • (N₁ * N₂) + (x.a * x.b - x.c) • (N₂ * N₁)) := by
  refine ⟨heisSpHom N₁ N₂ hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂, ?_, fun x => rfl⟩
  rw [injective_iff_map_eq_one]
  intro x hx
  have hx' : (proj r K) (heisSpFun N₁ N₂ hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ x) = 1 := hx
  exact heis_eq_one_of_heisM_eq_zero h₁ h₂ h₁₂₁ h₂₁₂ h₁₂ hPQ
    (heisM_eq_zero_of_proj_eq_one hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ hr hx')

theorem good_unipSp [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hr : 1 ≤ r)
    {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0) (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0) (h₁₂₁ : N₁ * N₂ * N₁ = 0) (h₂₁₂ : N₂ * N₁ * N₂ = 0)
    (h₁₂ : N₁ * N₂ ≠ 0) (hPQ : N₁ * N₂ ≠ N₂ * N₁) :
    orderOf (proj r K (unipSp N₁ hs₁ h₁)) = p ∧ IsSpecialGood p (proj r K (unipSp N₁ hs₁ h₁)) := by
  obtain ⟨ι, hι, hι1, -⟩ := exists_heis_projectiveSp hr hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ h₁₂ hPQ
  constructor
  · rw [← hι1, orderOf_injective ι hι]
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (Heis.pow_prime_eq_one hp hp2 ⟨1, 0, 0⟩) (by
      intro h
      have ha : (1 : K) = 0 := by simpa using congrArg Heis.a h
      exact one_ne_zero ha)
  · rw [← hι1]
    exact isSpecialGood_of_heis hp hp2 hK h3 hι ⟨1, 0, 0⟩

theorem good_unipSp_center [Finite K] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) [CharP K p]
    (hK : Nat.card K = p ^ e) (h3 : 3 < p ^ e) (hr : 1 ≤ r)
    {N₁ N₂ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0) (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0) (h₁₂₁ : N₁ * N₂ * N₁ = 0) (h₂₁₂ : N₂ * N₁ * N₂ = 0)
    (h₁₂ : N₁ * N₂ ≠ 0) (hPQ : N₁ * N₂ ≠ N₂ * N₁) {c : K} (hc : c ≠ 0)
    (hs : (c • (N₁ * N₂ - N₂ * N₁))ᵀ * formJ r K + formJ r K * (c • (N₁ * N₂ - N₂ * N₁)) = 0)
    (hN : c • (N₁ * N₂ - N₂ * N₁) * (c • (N₁ * N₂ - N₂ * N₁)) = 0) :
    orderOf (proj r K (unipSp (c • (N₁ * N₂ - N₂ * N₁)) hs hN)) = p ∧
      IsSpecialGood p (proj r K (unipSp (c • (N₁ * N₂ - N₂ * N₁)) hs hN)) := by
  obtain ⟨ι, hι, -, hιc⟩ := exists_heis_projectiveSp hr hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ h₁₂ hPQ
  constructor
  · rw [← hιc c hs hN, orderOf_injective ι hι]
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime (Heis.pow_prime_eq_one hp hp2 ⟨0, 0, c⟩) (by
      intro h
      exact hc (by simpa using congrArg Heis.c h))
  · rw [← hιc c hs hN]
    exact isSpecialGood_of_heis hp hp2 hK h3 hι ⟨0, 0, c⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive
