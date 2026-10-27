module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixLabel
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.Assembly.GL83LieDefs
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpanH90
import CFSG.LocalAnalysis.StandardType.KGLangTorusInnerModel
import CFSG.LocalAnalysis.StandardType.KGLangTorusClassicalInner
import CFSG.LocalAnalysis.StandardType.KGLangTorusDatumOfModels
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaConjLabels
import CFSG.LocalAnalysis.StandardType.KGLangTorusNorm
import CFSG.LocalAnalysis.StandardType.KGLangTorusOrth
import CFSG.LocalAnalysis.StandardType.KGLangTorusSpan

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.StandardType CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

section Plumbing

private def kgLangCOmMAux_swap {𝕂 : Type} [Field 𝕂] {m : ℕ} : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂 :=
  Matrix.fromBlocks (0 : Matrix (Fin m) (Fin m) 𝕂) (1 : Matrix (Fin m) (Fin m) 𝕂)
    (1 : Matrix (Fin m) (Fin m) 𝕂) (0 : Matrix (Fin m) (Fin m) 𝕂)

private theorem kgLangCOmMAux_swap_transpose {𝕂 : Type} [Field 𝕂] {m : ℕ} :
    (kgLangCOmMAux_swap (𝕂 := 𝕂) (m := m)).transpose = kgLangCOmMAux_swap := by
  rw [kgLangCOmMAux_swap, Matrix.fromBlocks_transpose]
  simp only [Matrix.transpose_zero, Matrix.transpose_one]

private theorem kgLangCOmMAux_swap_mul {𝕂 : Type} [Field 𝕂] {m : ℕ} :
    kgLangCOmMAux_swap (𝕂 := 𝕂) (m := m) * kgLangCOmMAux_swap = 1 := by
  rw [kgLangCOmMAux_swap, Matrix.fromBlocks_multiply]
  simp only [mul_zero, zero_mul, add_zero, mul_one, one_mul, zero_add]
  rw [Matrix.fromBlocks_one]

private def kgLangCOmMAux_tail {𝕂 : Type} [Field 𝕂] (b : 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂 := !![0, b; b, 0]

private def kgLangCOmMAux_tailInv {𝕂 : Type} [Field 𝕂] (b : 𝕂) : Matrix (Fin 2) (Fin 2) 𝕂 := !![0, b⁻¹; b⁻¹, 0]

private theorem kgLangCOmMAux_tail_transpose {𝕂 : Type} [Field 𝕂] (b : 𝕂) :
    (kgLangCOmMAux_tail (𝕂 := 𝕂) b).transpose = kgLangCOmMAux_tail b := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [kgLangCOmMAux_tail]

private theorem kgLangCOmMAux_tail_mul_tailInv {𝕂 : Type} [Field 𝕂] {b : 𝕂} (hb : b ≠ 0) :
    kgLangCOmMAux_tail (𝕂 := 𝕂) b * kgLangCOmMAux_tailInv b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kgLangCOmMAux_tail, kgLangCOmMAux_tailInv, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp

private theorem kgLangCOmMAux_tailInv_mul_tail {𝕂 : Type} [Field 𝕂] {b : 𝕂} (hb : b ≠ 0) :
    kgLangCOmMAux_tailInv (𝕂 := 𝕂) b * kgLangCOmMAux_tail b = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [kgLangCOmMAux_tail, kgLangCOmMAux_tailInv, Matrix.mul_apply, Fin.sum_univ_two]
  · field_simp
  · field_simp

private noncomputable def kgLangCOmMAux_J {𝕂 : Type} [Field 𝕂] {m : ℕ} (b : 𝕂) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
  Matrix.fromBlocks (kgLangCOmMAux_swap (𝕂 := 𝕂) (m := m))
    (0 : Matrix (Fin m ⊕ Fin m) (Fin 2) 𝕂)
    (0 : Matrix (Fin 2) (Fin m ⊕ Fin m) 𝕂)
    (kgLangCOmMAux_tail (𝕂 := 𝕂) b)

private noncomputable def kgLangCOmMAux_Jinv {𝕂 : Type} [Field 𝕂] {m : ℕ} (b : 𝕂) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
  Matrix.fromBlocks (kgLangCOmMAux_swap (𝕂 := 𝕂) (m := m))
    (0 : Matrix (Fin m ⊕ Fin m) (Fin 2) 𝕂)
    (0 : Matrix (Fin 2) (Fin m ⊕ Fin m) 𝕂)
    (kgLangCOmMAux_tailInv (𝕂 := 𝕂) b)

private theorem kgLangCOmMAux_J_transpose {𝕂 : Type} [Field 𝕂] {m : ℕ} (b : 𝕂) :
    (kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b).transpose = kgLangCOmMAux_J b := by
  rw [kgLangCOmMAux_J, Matrix.fromBlocks_transpose,
    kgLangCOmMAux_swap_transpose, kgLangCOmMAux_tail_transpose]
  simp only [Matrix.transpose_zero]

private theorem kgLangCOmMAux_J_mul_Jinv {𝕂 : Type} [Field 𝕂] {m : ℕ} {b : 𝕂} (hb : b ≠ 0) :
    kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b * kgLangCOmMAux_Jinv b = 1 := by
  rw [kgLangCOmMAux_J, kgLangCOmMAux_Jinv, Matrix.fromBlocks_multiply]
  rw [kgLangCOmMAux_swap_mul, kgLangCOmMAux_tail_mul_tailInv (𝕂 := 𝕂) hb,
    ← Matrix.fromBlocks_one]
  congr 1 <;> simp [mul_zero, zero_mul, add_zero, zero_add]

private theorem kgLangCOmMAux_Jinv_mul_J {𝕂 : Type} [Field 𝕂] {m : ℕ} {b : 𝕂} (hb : b ≠ 0) :
    kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b * kgLangCOmMAux_J b = 1 := by
  rw [kgLangCOmMAux_J, kgLangCOmMAux_Jinv, Matrix.fromBlocks_multiply]
  rw [kgLangCOmMAux_swap_mul, kgLangCOmMAux_tailInv_mul_tail (𝕂 := 𝕂) hb,
    ← Matrix.fromBlocks_one]
  congr 1 <;> simp [mul_zero, zero_mul, add_zero, zero_add]

private theorem kgLangCOmMAux_polar_basis {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b c : 𝕂) (i j : LargeEvenMinusIdx m) :
    QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) (Pi.single i (1:𝕂)) (Pi.single j 1) =
      kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b i j := by
  rw [TableBOrth.coe_qMinusForm]
  unfold QuadraticMap.polar
  rcases i with (i | i) | i <;> try fin_cases i
  all_goals rcases j with (j | j) | j <;> try fin_cases j
  all_goals
    simp [kgLangCOmMAux_J, kgLangCOmMAux_swap, kgLangCOmMAux_tail, LargeEvenQMinus,
      Matrix.fromBlocks, Matrix.of_apply, Matrix.one_apply, Pi.single_apply, eq_comm,
      Finset.sum_ite_eq', Finset.mem_univ] <;>
    first | ring1 | (ring_nf <;> simp [CharTwo.two_eq_zero])

private theorem kgLangCOmMAux_polar_toMatrix {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b c : 𝕂) :
    (LinearMap.BilinForm.toMatrix (Pi.basisFun 𝕂 (LargeEvenMinusIdx m)))
      (QuadraticMap.polarBilin (TableBOrth.qMinusForm 𝕂 m b c)) =
      kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b := by
  ext i j
  rw [LinearMap.BilinForm.toMatrix_apply, QuadraticMap.polarBilin_apply_apply]
  simp only [Pi.basisFun_apply]
  exact kgLangCOmMAux_polar_basis b c i j

private theorem kgLangCOmMAux_polar_eq {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b c : 𝕂) (u v : LargeEvenMinusIdx m → 𝕂) :
    QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) u v =
      u ⬝ᵥ (kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b).mulVec v := by
  have h : QuadraticMap.polarBilin (TableBOrth.qMinusForm 𝕂 m b c) =
      Matrix.toBilin' (kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b) := by
    apply (LinearMap.BilinForm.toMatrix (Pi.basisFun 𝕂 (LargeEvenMinusIdx m))).injective
    rw [kgLangCOmMAux_polar_toMatrix]
    ext i j
    rw [LinearMap.BilinForm.toMatrix_apply, Matrix.toBilin'_apply', Pi.basisFun_apply]
    simp
  have h2 := congrArg (fun B => (B u) v) h
  rw [QuadraticMap.polarBilin_apply_apply, Matrix.toBilin'_apply'] at h2
  exact h2

private theorem kgLangCOmMAux_Jinv_transpose {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] {b : 𝕂} (hb : b ≠ 0) :
    (kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b).transpose =
      kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b := by
  calc (kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b).transpose
      = (kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b).transpose * 1 := (Matrix.mul_one _).symm
    _ = (kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b).transpose *
          (kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b * kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b) := by
          rw [kgLangCOmMAux_J_mul_Jinv (𝕂 := 𝕂) hb]
    _ = ((kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b).transpose *
          kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b) * kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b := by
          rw [Matrix.mul_assoc]
    _ = ((kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b).transpose *
          (kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b).transpose) *
          kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b := by
          rw [kgLangCOmMAux_J_transpose]
    _ = ((kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b *
          kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b).transpose) *
          kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b := by
          rw [Matrix.transpose_mul]
    _ = (1 : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).transpose *
          kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b := by
          rw [kgLangCOmMAux_J_mul_Jinv (𝕂 := 𝕂) hb]
    _ = kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b := by
          rw [Matrix.transpose_one, Matrix.one_mul]

private noncomputable def kgLangCOmMAux_tau {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b : 𝕂)
    (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
  kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b * x.transpose * kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b

private theorem kgLangCOmMAux_tau_add {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] {b : 𝕂}
    (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :
    kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b (x + y) =
      kgLangCOmMAux_tau b x + kgLangCOmMAux_tau b y := by
  simp only [kgLangCOmMAux_tau, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul]

private theorem kgLangCOmMAux_tau_one {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] {b : 𝕂} (hb : b ≠ 0) :
    kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b 1 = 1 := by
  rw [kgLangCOmMAux_tau, Matrix.transpose_one, Matrix.mul_one,
    kgLangCOmMAux_Jinv_mul_J (𝕂 := 𝕂) hb]

private theorem kgLangCOmMAux_sandwich {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] {b : 𝕂} (hb : b ≠ 0)
    (A B : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :
    kgLangCOmMAux_Jinv b * A * kgLangCOmMAux_J b *
        kgLangCOmMAux_Jinv b * B * kgLangCOmMAux_J b =
      kgLangCOmMAux_Jinv b * (A * B) * kgLangCOmMAux_J b := by
  have h : kgLangCOmMAux_Jinv b * A * kgLangCOmMAux_J b *
        kgLangCOmMAux_Jinv b * B * kgLangCOmMAux_J b =
      kgLangCOmMAux_Jinv b * A * (kgLangCOmMAux_J b * kgLangCOmMAux_Jinv b) * B *
        kgLangCOmMAux_J b := by
    simp only [Matrix.mul_assoc]
  rw [h, kgLangCOmMAux_J_mul_Jinv (𝕂 := 𝕂) hb]
  simp only [Matrix.mul_one, Matrix.mul_assoc]

private theorem kgLangCOmMAux_tau_mul_anti {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] {b : 𝕂} (hb : b ≠ 0)
    (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :
    kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b (x * y) =
      kgLangCOmMAux_tau b y * kgLangCOmMAux_tau b x := by
  simp only [kgLangCOmMAux_tau, Matrix.transpose_mul]
  have hs := (kgLangCOmMAux_sandwich (𝕂 := 𝕂) hb y.transpose x.transpose).symm
  simp only [Matrix.mul_assoc] at hs ⊢
  exact hs

private theorem kgLangCOmMAux_tau_tau {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] {b : 𝕂} (hb : b ≠ 0)
    (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :
    kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b (kgLangCOmMAux_tau b x) = x := by
  simp only [kgLangCOmMAux_tau, Matrix.transpose_mul, Matrix.transpose_transpose,
    kgLangCOmMAux_Jinv_transpose (𝕂 := 𝕂) hb, kgLangCOmMAux_J_transpose]
  rw [← Matrix.mul_assoc (kgLangCOmMAux_Jinv b) (kgLangCOmMAux_J b) (x * kgLangCOmMAux_Jinv b),
    kgLangCOmMAux_Jinv_mul_J (𝕂 := 𝕂) hb, Matrix.one_mul, Matrix.mul_assoc,
    kgLangCOmMAux_Jinv_mul_J (𝕂 := 𝕂) hb, Matrix.mul_one]

private theorem kgLangCOmMAux_polar_mulVec_gram {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b c : 𝕂)
    (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
    (u v : LargeEvenMinusIdx m → 𝕂) :
    QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) (x.mulVec u) (x.mulVec v) =
      u ⬝ᵥ ((x.transpose * kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b * x).mulVec v) := by
  rw [kgLangCOmMAux_polar_eq]
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec,
    ← Matrix.dotProduct_mulVec, Matrix.mul_assoc]

private theorem kgLangCOmMAux_tau_adjoint {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b c : 𝕂) (hb : b ≠ 0)
    (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
    (u v : LargeEvenMinusIdx m → 𝕂) :
    QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) (x.mulVec u) v =
      QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) u
        ((kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b x).mulVec v) := by
  rw [kgLangCOmMAux_polar_eq, kgLangCOmMAux_polar_eq, kgLangCOmMAux_tau]
  have hJ : kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b *
      (kgLangCOmMAux_Jinv (𝕂 := 𝕂) (m := m) b * x.transpose *
        kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b) =
      x.transpose * kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (kgLangCOmMAux_J b) (kgLangCOmMAux_Jinv b)
        (x.transpose * kgLangCOmMAux_J b),
      kgLangCOmMAux_J_mul_Jinv (𝕂 := 𝕂) hb, Matrix.one_mul]
  rw [Matrix.mulVec_mulVec, hJ]
  rw [Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_mulVec]

private theorem kgLangCOmMAux_gram_of_isometry {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b c : 𝕂)
    (g : GL (LargeEvenMinusIdx m) 𝕂)
    (hg : ∀ u v, QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c)
        (((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec u))
        (((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec v)) =
      QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) u v) :
    (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).transpose *
        kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b *
        (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
      kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b := by
  ext i j
  have h := hg (Pi.single i (1:𝕂)) (Pi.single j 1)
  rw [kgLangCOmMAux_polar_mulVec_gram, kgLangCOmMAux_polar_eq] at h
  simpa [dotProduct, Pi.single_apply, Finset.sum_ite_eq', Finset.mem_univ] using h

private theorem kgLangCOmMAux_tau_isometry {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] (b c : 𝕂) (hb : b ≠ 0)
    (g : GL (LargeEvenMinusIdx m) 𝕂)
    (hg : ∀ u v, QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c)
        (((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec u))
        (((g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec v)) =
      QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) u v) :
    kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b
        (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
      ((g⁻¹ : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
  have hgram := kgLangCOmMAux_gram_of_isometry b c g hg
  have hg' : (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).transpose *
        kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b =
      kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b *
        ((g⁻¹ : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
    have h := congrArg (fun M : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 =>
      M * ((g⁻¹ : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) hgram
    simp only [Matrix.mul_assoc] at h
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one] at h
    exact h
  rw [kgLangCOmMAux_tau, Matrix.mul_assoc, hg', ← Matrix.mul_assoc,
    kgLangCOmMAux_Jinv_mul_J (𝕂 := 𝕂) hb, Matrix.one_mul]

section Beta

private theorem kgLangCOmMAux_tailSeq_snd_ne_zero {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] [Finite 𝕂] {b c : 𝕂} (hb : b ≠ 0) (k : ℕ) :
    (CFSG.RankThree.PartOne.AUTSL.tailSeq b c k).2 ≠ 0 := by
  intro h
  have h1 := CFSG.RankThree.PartOne.AUTSL.tailSeq_snd_mul (b := b) (c := c) k
  rw [h, zero_mul] at h1
  exact (pow_ne_zero _ hb) h1.symm

private theorem kgLangCOmMAux_frobBlock_eq {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂] (b c : 𝕂) (k : ℕ) :
    LargeEvenFrobBlock m b c k =
      Matrix.fromBlocks (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
        (0 : Matrix (Fin m ⊕ Fin m) (Fin 2) 𝕂)
        (0 : Matrix (Fin 2) (Fin m ⊕ Fin m) 𝕂)
        (!![1, (CFSG.RankThree.PartOne.AUTSL.tailSeq b c k).1; 0,
          (CFSG.RankThree.PartOne.AUTSL.tailSeq b c k).2] : Matrix (Fin 2) (Fin 2) 𝕂) := by
  simp [LargeEvenFrobBlock, RecipeFieldOmega.omega_pow_two_pow_eq]

private noncomputable def kgLangCOmMAux_Ainv {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂] (b c : 𝕂) (k : ℕ) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
  Matrix.fromBlocks (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) 𝕂)
    (0 : Matrix (Fin m ⊕ Fin m) (Fin 2) 𝕂)
    (0 : Matrix (Fin 2) (Fin m ⊕ Fin m) 𝕂)
    (!![1, (CFSG.RankThree.PartOne.AUTSL.tailSeq b c k).1 *
        (CFSG.RankThree.PartOne.AUTSL.tailSeq b c k).2⁻¹; 0,
      (CFSG.RankThree.PartOne.AUTSL.tailSeq b c k).2⁻¹] : Matrix (Fin 2) (Fin 2) 𝕂)

private theorem kgLangCOmMAux_tail_mul_tailinv {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] [Finite 𝕂] {a d : 𝕂} (hd : d ≠ 0) :
    (!![1, a; 0, d] : Matrix (Fin 2) (Fin 2) 𝕂) * !![1, a * d⁻¹; 0, d⁻¹] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem kgLangCOmMAux_tailinv_mul_tail {𝕂 : Type} [Field 𝕂] [CharP 𝕂 2] [Finite 𝕂] {a d : 𝕂} (hd : d ≠ 0) :
    (!![1, a * d⁻¹; 0, d⁻¹] : Matrix (Fin 2) (Fin 2) 𝕂) * !![1, a; 0, d] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    field_simp <;> ring_nf <;> simp [CharTwo.two_eq_zero]

private theorem kgLangCOmMAux_frobBlock_mul_Ainv {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂] {b c : 𝕂} (hb : b ≠ 0) (k : ℕ) :
    LargeEvenFrobBlock m b c k * kgLangCOmMAux_Ainv b c k = 1 := by
  rw [kgLangCOmMAux_frobBlock_eq, kgLangCOmMAux_Ainv, Matrix.fromBlocks_multiply]
  rw [kgLangCOmMAux_tail_mul_tailinv (kgLangCOmMAux_tailSeq_snd_ne_zero hb k),
    ← Matrix.fromBlocks_one]
  congr 1 <;> simp [mul_zero, zero_mul, add_zero, zero_add]

private theorem kgLangCOmMAux_Ainv_mul_frobBlock {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂] {b c : 𝕂} (hb : b ≠ 0) (k : ℕ) :
    kgLangCOmMAux_Ainv b c k * LargeEvenFrobBlock m b c k = 1 := by
  rw [kgLangCOmMAux_frobBlock_eq, kgLangCOmMAux_Ainv, Matrix.fromBlocks_multiply]
  rw [kgLangCOmMAux_tailinv_mul_tail (kgLangCOmMAux_tailSeq_snd_ne_zero hb k),
    ← Matrix.fromBlocks_one]
  congr 1 <;> simp [mul_zero, zero_mul, add_zero, zero_add]

private noncomputable def kgLangCOmMAux_conjHom {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂]
    (A Ainv : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
    (h1 : A * Ainv = 1) (h2 : Ainv * A = 1) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 →+*
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 where
  toFun x := A * x * Ainv
  map_one' := by rw [Matrix.mul_one, h1]
  map_zero' := by rw [Matrix.mul_zero, Matrix.zero_mul]
  map_add' := by intro x y; rw [Matrix.mul_add, Matrix.add_mul]
  map_mul' := by
    intro x y
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Ainv A, h2, Matrix.one_mul]

private noncomputable def kgLangCOmMAux_beta {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂] (b c : 𝕂) (hb : b ≠ 0) (k : ℕ) :
    Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 →+*
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
  (kgLangCOmMAux_conjHom (LargeEvenFrobBlock m b c k) (kgLangCOmMAux_Ainv b c k)
    (kgLangCOmMAux_frobBlock_mul_Ainv hb k) (kgLangCOmMAux_Ainv_mul_frobBlock hb k)).comp
    (RingHom.mapMatrix ((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂))

private theorem kgLangCOmMAux_beta_apply {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂] (b c : 𝕂) (hb : b ≠ 0) (k : ℕ)
    (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :
    kgLangCOmMAux_beta b c hb k x =
      LargeEvenFrobBlock m b c k *
        RingHom.mapMatrix ((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂) x *
        kgLangCOmMAux_Ainv b c k := rfl

private theorem kgLangCOmMAux_beta_map_eq {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂] (b c : 𝕂) (hb : b ≠ 0) (k : ℕ)
    (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :
    RingHom.mapMatrix ((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂) x =
      x.map (fun t : 𝕂 => t ^ 2 ^ k) := by
  ext i j
  change ((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂) (x i j) = (x i j) ^ 2 ^ k
  exact CFSG.RankThree.PartOne.AUTSL.frobeniusEquiv_pow_apply k (x i j)

end Beta

private theorem kgLangCOmMAux_adjoin_comm_reduced {ι : Type} [Fintype ι] [DecidableEq ι]
    {𝕂 : Type} [Field 𝕂] [Finite 𝕂] [CharP 𝕂 2]
    (P : Subgroup (GL ι 𝕂)) (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hodd : Odd (Nat.card P)) :
    (∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
      ∀ y ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
        x * y = y * x) ∧
    ∀ x ∈ Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)),
      IsNilpotent x → x = 0 := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · haveI := hι
    exact ⟨fun x _ y _ => Subsingleton.elim _ _, fun x _ _ => Subsingleton.elim _ _⟩
  · set s : Set (Matrix ι ι 𝕂) :=
      (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _) with hs
    let S : Subalgebra 𝕂 (Matrix ι ι 𝕂) := Algebra.adjoin 𝕂 s
    have hs_pair : s.Pairwise Commute := by
      intro a ha b hb _
      obtain ⟨g, hg, rfl⟩ := ha
      obtain ⟨h, hh, rfl⟩ := hb
      show Commute (↑g : Matrix ι ι 𝕂) (↑h : Matrix ι ι 𝕂)
      rw [commute_iff_eq, ← Matrix.GeneralLinearGroup.coe_mul, ← Matrix.GeneralLinearGroup.coe_mul,
        hab g hg h hh]
    have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
      haveI : IsMulCommutative S := Algebra.isMulCommutative_adjoin 𝕂 hs_pair
      intro x hx y hy
      have hcommS : ∀ a b : S, a * b = b * a :=
        isMulCommutative_iff.mp (inferInstance : IsMulCommutative S)
      simpa using congrArg Subtype.val (hcommS ⟨x, hx⟩ ⟨y, hy⟩)
    refine ⟨hcomm, ?_⟩
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Algebra (ZMod 2) 𝕂 := ZMod.algebra 𝕂 2
    letI : Fintype 𝕂 := Fintype.ofFinite 𝕂
    let f := Module.finrank (ZMod 2) 𝕂
    let m := Nat.card P
    let k := f * Nat.totient m
    have hcard : 2 ^ f = Nat.card 𝕂 := FiniteField.pow_finrank_eq_natCard 2 𝕂
    have hm_pos : 0 < m := by
      haveI : Nonempty P := ⟨⟨1, one_mem P⟩⟩
      change 0 < Nat.card P
      exact Nat.card_pos
    have hf_pos : 0 < f := by
      change 0 < Module.finrank (ZMod 2) 𝕂
      exact Module.finrank_pos
    have hk_pos : 0 < k := by
      change 0 < f * Nat.totient m
      exact Nat.mul_pos hf_pos (Nat.totient_pos.mpr hm_pos)
    have hcop : Nat.Coprime 2 m := hodd.coprime_two_left
    have hk_mod : 2 ^ k ≡ 1 [MOD m] := by
      have h1 : (2 ^ Nat.totient m) ^ f ≡ 1 ^ f [MOD m] :=
        (Nat.ModEq.pow_totient hcop).pow f
      rw [one_pow] at h1
      have h2 : (2 ^ Nat.totient m) ^ f = 2 ^ k := by
        change (2 ^ Nat.totient m) ^ f = 2 ^ (f * Nat.totient m)
        rw [Nat.mul_comm, pow_mul]
      rwa [← h2]
    have hfixK : ∀ c : 𝕂, c ^ (2 ^ k) = c := by
      intro c
      have hq : 2 ^ k = (Nat.card 𝕂) ^ Nat.totient m := by
        change 2 ^ (f * Nat.totient m) = (Nat.card 𝕂) ^ Nat.totient m
        rw [← hcard, pow_mul]
      rw [hq, ← Fintype.card_eq_nat_card]
      exact FiniteField.pow_card_pow (Nat.totient m) c
    have hfixS : ∀ x ∈ S, x ^ (2 ^ k) = x := by
      intro x hxS
      refine Algebra.adjoin_induction (p := fun x _ => x ^ (2 ^ k) = x) ?_ ?_ ?_ ?_ hxS
      · intro y hy
        obtain ⟨g, hg, rfl⟩ := hy
        have hgm : (↑g : Matrix ι ι 𝕂) ^ m = 1 := by
          have h : g ^ m = 1 := by
            have h' := congrArg Subtype.val (pow_card_eq_one' (G := P) (x := ⟨g, hg⟩))
            simp only [Subgroup.coe_pow] at h'
            simpa [m] using h'
          have h2 := congrArg (fun u : GL ι 𝕂 => (u : Matrix ι ι 𝕂)) h
          simpa using h2
        have h := pow_eq_pow_of_modEq (x := (↑g : Matrix ι ι 𝕂)) hk_mod hgm
        rwa [pow_one] at h
      · intro r
        have hr : algebraMap 𝕂 (Matrix ι ι 𝕂) r = Matrix.scalar ι r := by
          simp [Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
        rw [hr, ← map_pow, hfixK r]
      · intro a b ha hb ha' hb'
        rw [add_pow_char_pow_of_commute (p := 2) (n := k) (hcomm a ha b hb), ha', hb']
      · intro a b ha hb ha' hb'
        rw [Commute.mul_pow (hcomm a ha b hb) (2 ^ k), ha', hb']
    intro x hxS hnil
    obtain ⟨n, hn⟩ := hnil
    have hiter : ∀ t : ℕ, x ^ ((2 ^ k) ^ t) = x := by
      intro t
      induction t with
      | zero => simp
      | succ t ih => rw [pow_succ, pow_mul, ih]; exact hfixS x hxS
    have h2k_ge_two : 2 ≤ 2 ^ k := by
      calc (2 : ℕ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk_pos
    have hle : n ≤ (2 ^ k) ^ n :=
      (le_of_lt Nat.lt_two_pow_self).trans (Nat.pow_le_pow_left h2k_ge_two n)
    have hzero : x ^ ((2 ^ k) ^ n) = 0 := by
      rw [show (2 ^ k) ^ n = n + ((2 ^ k) ^ n - n) from (Nat.add_sub_cancel' hle).symm]
      rw [pow_add, hn, zero_mul]
    rw [hiter n] at hzero
    exact hzero

private theorem kgLangCOmMAux_tau_scalar {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] {b : 𝕂}
    (hb : b ≠ 0) (r : 𝕂) :
    kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b (Matrix.scalar (LargeEvenMinusIdx m) r) =
      Matrix.scalar (LargeEvenMinusIdx m) r := by
  have htrans : (Matrix.scalar (LargeEvenMinusIdx m) r).transpose =
      Matrix.scalar (LargeEvenMinusIdx m) r := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.scalar_apply, Matrix.diagonal_apply, eq_comm]
  have hcomm : Commute (Matrix.scalar (LargeEvenMinusIdx m) r)
      (kgLangCOmMAux_J (𝕂 := 𝕂) (m := m) b) :=
    Matrix.scalar_commute r (fun r' => Commute.all r r') _
  rw [kgLangCOmMAux_tau, htrans]
  calc kgLangCOmMAux_Jinv b * Matrix.scalar (LargeEvenMinusIdx m) r * kgLangCOmMAux_J b
      = kgLangCOmMAux_Jinv b * (Matrix.scalar (LargeEvenMinusIdx m) r * kgLangCOmMAux_J b) := by
        rw [Matrix.mul_assoc]
    _ = kgLangCOmMAux_Jinv b * (kgLangCOmMAux_J b * Matrix.scalar (LargeEvenMinusIdx m) r) := by
        rw [hcomm.eq]
    _ = (kgLangCOmMAux_Jinv b * kgLangCOmMAux_J b) * Matrix.scalar (LargeEvenMinusIdx m) r := by
        rw [Matrix.mul_assoc]
    _ = Matrix.scalar (LargeEvenMinusIdx m) r := by
        rw [kgLangCOmMAux_Jinv_mul_J (𝕂 := 𝕂) hb, Matrix.one_mul]

private theorem kgLangCOmMAux_beta_scalar {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2] [Finite 𝕂]
    (b c : 𝕂) (hb : b ≠ 0) (k : ℕ) (r : 𝕂) :
    kgLangCOmMAux_beta b c hb k (Matrix.scalar (LargeEvenMinusIdx m) r) =
      Matrix.scalar (LargeEvenMinusIdx m)
        (((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂) r) := by
  rw [kgLangCOmMAux_beta_apply]
  have hmap : RingHom.mapMatrix ((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂)
      (Matrix.scalar (LargeEvenMinusIdx m) r) =
      Matrix.scalar (LargeEvenMinusIdx m)
        (((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂) r) := by
    ext i j
    by_cases h : i = j
    · subst h
      simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply]
    · simp [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.scalar_apply, h]
  rw [hmap]
  have hcomm : Commute (LargeEvenFrobBlock m b c k)
      (Matrix.scalar (LargeEvenMinusIdx m)
        (((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂) r)) :=
    (Matrix.scalar_commute _ (fun _ => Commute.all _ _) _).symm
  rw [hcomm.eq, Matrix.mul_assoc, kgLangCOmMAux_frobBlock_mul_Ainv (𝕂 := 𝕂) hb k, Matrix.mul_one]

private theorem kgLangCOmMAux_isometry_of_mem_orth {ι : Type} [Fintype ι] [DecidableEq ι]
    {𝕂 : Type} [Field 𝕂] {Q : (ι → 𝕂) → 𝕂} {g : GL ι 𝕂}
    (hg : g ∈ LargeEvenOrthGroup Q) :
    ∀ v, Q (((g : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v) = Q v := by
  let T : Subgroup (GL ι 𝕂) :=
    { carrier := {A | ∀ v, Q (((A : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v) = Q v}
      one_mem' := by intro v; simp
      mul_mem' := by
        intro a b ha hb v
        rw [Matrix.GeneralLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
        exact (ha _).trans (hb v)
      inv_mem' := by
        intro a ha v
        rw [Matrix.GeneralLinearGroup.coe_inv]
        have h := ha (((a⁻¹ : GL ι 𝕂) : Matrix ι ι 𝕂).mulVec v)
        rw [Matrix.GeneralLinearGroup.coe_inv] at h
        rw [Matrix.mulVec_mulVec,
          Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp ⟨a, rfl⟩),
          Matrix.one_mulVec] at h
        exact h.symm }
  have hle : LargeEvenOrthGroup Q ≤ T := by
    rw [largeEvenOrthGroup_def]
    exact (Subgroup.closure_le T).mpr fun a ha => ha
  exact hle hg

private theorem kgLangCOmMAux_adjoin_le_span {ι : Type} [Fintype ι] [DecidableEq ι]
    {𝕂 : Type} [Field 𝕂] (P : Subgroup (GL ι 𝕂)) :
    (Algebra.adjoin 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)) : Set (Matrix ι ι 𝕂)) ⊆
      (Submodule.span 𝕂 ((fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _)) :
        Set (Matrix ι ι 𝕂)) := by
  set S : Set (Matrix ι ι 𝕂) := (fun g : GL ι 𝕂 => (g : Matrix ι ι 𝕂)) '' (P : Set _) with hS
  have h1 : (1 : Matrix ι ι 𝕂) ∈ S := ⟨1, P.one_mem, rfl⟩
  have hmul : ∀ a ∈ S, ∀ b ∈ S, a * b ∈ S := by
    rintro _ ⟨g, hg, rfl⟩ _ ⟨h, hh, rfl⟩
    exact ⟨g * h, P.mul_mem hg hh, by
      show ((g * h : GL ι 𝕂) : Matrix ι ι 𝕂) = ((g : Matrix ι ι 𝕂)) * ((h : Matrix ι ι 𝕂))
      rw [Matrix.GeneralLinearGroup.coe_mul]⟩
  have hcl : Submonoid.closure S = S := by
    apply le_antisymm
    · intro x hx
      induction hx using Submonoid.closure_induction with
      | mem y hy => exact hy
      | one => exact h1
      | mul x y hx hy ihx ihy => exact hmul x ihx y ihy
    · exact Submonoid.subset_closure
  intro x hx
  have h := Algebra.adjoin_eq_span (R := 𝕂) (s := S)
  rw [hcl] at h
  have hx' : x ∈ Subalgebra.toSubmodule (Algebra.adjoin 𝕂 S) := hx
  rw [h] at hx'
  exact hx'

private theorem kgLangCOmMAux_odd_card_of_isElemAbelian {p : ℕ} {G : Type*} [Group G] [Finite G]
    (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} (hE : IsElemAbelian p E) :
    Odd (Nat.card E) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2 : 2 ∣ Nat.card E := even_iff_two_dvd.mp heven
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hgp : g ^ p = 1 := Subtype.ext (hE.2 (g : G) g.2)
  have hdivp : orderOf g ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hgp
  have hdiv2 : orderOf g ∣ 2 := by rw [hg]
  have hcop : Nat.Coprime 2 p := by
    have hnotdvd : ¬ p ∣ 2 := by
      intro h
      have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) h
      have hpge : 2 ≤ p := hp.two_le
      omega
    exact (hp.coprime_iff_not_dvd.mpr hnotdvd).symm
  have h1 : orderOf g = 1 := by
    have hgcd := Nat.dvd_gcd hdiv2 hdivp
    rw [Nat.coprime_iff_gcd_eq_one.mp hcop] at hgcd
    exact Nat.dvd_one.mp hgcd
  rw [h1] at hg
  omega

private lemma kgLangCOmMAux_polar_comp {ι 𝕂 : Type} [Fintype ι] [Field 𝕂]
    (Q : QuadraticForm 𝕂 (ι → 𝕂)) (x : Matrix ι ι 𝕂) (u v : ι → 𝕂) :
    QuadraticMap.polar (Q.comp (Matrix.mulVecLin x)) u v =
      QuadraticMap.polar Q (x.mulVec u) (x.mulVec v) := by
  simp only [QuadraticMap.polar, QuadraticMap.comp_apply, Matrix.mulVecLin_apply, Matrix.mulVec_add]

private lemma kgLangCOmMAux_polar_preserved {ι 𝕂 : Type} [Fintype ι] [DecidableEq ι] [Field 𝕂]
    [CharP 𝕂 2] (Q : QuadraticForm 𝕂 (ι → 𝕂)) {g : GL ι 𝕂}
    (hg : ∀ v, Q ((g : Matrix ι ι 𝕂).mulVec v) = Q v) (a b : ι → 𝕂) :
    QuadraticMap.polar Q ((g : Matrix ι ι 𝕂).mulVec a) ((g : Matrix ι ι 𝕂).mulVec b)
      = QuadraticMap.polar Q a b := by
  have hcomp : Q.comp (Matrix.mulVecLin g) = Q := by
    ext v
    simpa only [QuadraticMap.comp_apply, Matrix.mulVecLin_apply] using hg v
  rw [← kgLangCOmMAux_polar_comp Q (g : Matrix ι ι 𝕂) a b, hcomp]

private theorem kgLangCOmMAux_polar_of_tau {𝕂 : Type} [Field 𝕂] {m : ℕ} [CharP 𝕂 2]
    (b c : 𝕂) (hb : b ≠ 0) (x : GL (LargeEvenMinusIdx m) 𝕂)
    (hx : (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
      kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b
        (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) = 1) :
    ∀ u v : LargeEvenMinusIdx m → 𝕂,
      QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c)
        ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec u)
        ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec v) =
      QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) u v := by
  have hτeq : kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b
        (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
      ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))⁻¹ :=
    (Matrix.inv_eq_right_inv hx).symm
  have hleft : kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b
        (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
      (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) = 1 := by
    rw [hτeq]
    exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp ⟨x, rfl⟩)
  intro u v
  rw [kgLangCOmMAux_tau_adjoint b c hb
      (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) u
      ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec v)]
  rw [Matrix.mulVec_mulVec, hleft, Matrix.one_mulVec]

end Plumbing

private theorem kgLangCOmMAux_hfk {m : ℕ} (hm : 3 ≤ m) {𝕂 : Type} [Field 𝕂] [Finite 𝕂]
    [CharP 𝕂 2] {b c : 𝕂} (hbc : ∀ s : 𝕂, s ^ 2 + b * s + c ≠ 0) (k : ℕ)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hk : LargeEvenGraphAut (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))
      (fun h h' : LargeEvenOmega (LargeEvenQMinus m b c) =>
        ((h' : GL (LargeEvenMinusIdx m) 𝕂) : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
          LargeEvenFrobBlock m b c k =
        LargeEvenFrobBlock m b c k *
          (((h : GL (LargeEvenMinusIdx m) 𝕂) : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).map
            (· ^ 2 ^ k)))
      f) :
    MulAut.congr (RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c) (by omega)) f =
      (AutOm.frobAut (n := m + 1) (b := b) (c := c) (by omega) hbc) ^ k := by
  have h1 : (MulAut.congr (RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c) (by omega))).symm
      ((AutOm.frobAut (n := m + 1) (b := b) (c := c) (by omega) hbc) ^ k) = f := by
    refine eq_of_graphAut (RecipeFieldOmega.proj_surjective_minus (n := m + 1) (b := b) (c := c))
      ?_ hk ?_
    · exact RecipeFieldOmega.graphAut_frobAut_pow (n := m + 1) (b := b) (c := c) (by omega) hbc k
    · intro h
      exact RecipeFieldOmega.exists_frob_mem_minus (n := m + 1) (b := b) (c := c) (by omega) hbc k h
  rw [← h1, MulEquiv.apply_symm_apply]

private theorem kgLangCOmMAux_beta_facts {m : ℕ} (hm : 3 ≤ m) {𝕂 : Type} [Field 𝕂] [Finite 𝕂]
    [CharP 𝕂 2] {b c : 𝕂} (hbc : ∀ s : 𝕂, s ^ 2 + b * s + c ≠ 0) (hb : b ≠ 0) (k : ℕ)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (S : MulAut (LargeEvenOmega (LargeEvenQMinus m b c)))
    (hSe : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) (S u) =
        f (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) u))
    (Θ : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) ≃*
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived
        (CFSG.RankThree.PartOne.AUTSL.Qm (m + 1) (by omega) b c))
    (frob : MulAut
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived
        (CFSG.RankThree.PartOne.AUTSL.Qm (m + 1) (by omega) b c)))
    (hΘ : Θ = RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c) (by omega))
    (hfrob : frob = AutOm.frobAut (n := m + 1) (b := b) (c := c) (by omega) hbc)
    (hfk : MulAut.congr Θ f = frob ^ k)
    (σ : 𝕂 ≃+* 𝕂) (hσ : σ = (frobeniusEquiv 𝕂 2) ^ k)
    (β : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 →+*
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
    (hβ : β = kgLangCOmMAux_beta b c hb k) :
    (∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      β ((u : GL (LargeEvenMinusIdx m) 𝕂) : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
        ((S u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) ∧
    (∀ r : 𝕂, β (Matrix.scalar (LargeEvenMinusIdx m) r) =
      Matrix.scalar (LargeEvenMinusIdx m) (σ r)) ∧
    (∀ (i : ℕ) (u : LargeEvenOmega (LargeEvenQMinus m b c)),
      (⇑β)^[i] (((u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
        (((S ^ i) u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) ∧
    (∀ (i : ℕ) (r : 𝕂),
      (⇑β)^[i] (Matrix.scalar (LargeEvenMinusIdx m) r) =
        Matrix.scalar (LargeEvenMinusIdx m) ((σ ^ i) r)) ∧
    (∀ (j : ℕ) (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂),
      (⇑β)^[j] (x + y) = (⇑β)^[j] x + (⇑β)^[j] y) ∧
    (∀ (j : ℕ) (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂),
      (⇑β)^[j] (x * y) = (⇑β)^[j] x * (⇑β)^[j] y) := by
  have hβmat : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      β ((u : GL (LargeEvenMinusIdx m) 𝕂) : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
        ((S u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
    intro u
    have hgraph : ((S u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) * LargeEvenFrobBlock m b c k =
        LargeEvenFrobBlock m b c k *
          (((u : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).map (fun t => t ^ 2 ^ k)) := by
      refine (RecipeFieldOmega.frobAut_pow_mk_eq_iff
        (n := m + 1) (b := b) (c := c) (by omega) hbc k u (S u)).1 ?_
      have h1 : (frob ^ k) (Θ (LargeEvenProjMk _ u)) = Θ (LargeEvenProjMk _ (S u)) := by
        rw [← hfk, MulAut.congr_apply]
        simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, Equiv.symm_apply_apply]
        exact congrArg Θ (hSe u).symm
      rw [← hfrob, ← hΘ]
      exact h1
    calc β ((u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
        = kgLangCOmMAux_beta b c hb k
            ((u : GL (LargeEvenMinusIdx m) 𝕂) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by rw [hβ]
      _ = LargeEvenFrobBlock m b c k *
            RingHom.mapMatrix ((frobeniusEquiv 𝕂 2 ^ k : 𝕂 ≃+* 𝕂) : 𝕂 →+* 𝕂)
              ((u : GL (LargeEvenMinusIdx m) 𝕂) :
                Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
            kgLangCOmMAux_Ainv b c k :=
          kgLangCOmMAux_beta_apply b c hb k _
      _ = LargeEvenFrobBlock m b c k *
            (((u : GL (LargeEvenMinusIdx m) 𝕂) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).map (fun t => t ^ 2 ^ k)) *
            kgLangCOmMAux_Ainv b c k := by rw [kgLangCOmMAux_beta_map_eq b c hb k]
      _ = ((S u : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
          have h := congrArg (fun M => M * kgLangCOmMAux_Ainv b c k) hgraph
          simp only [Matrix.mul_assoc, kgLangCOmMAux_frobBlock_mul_Ainv (𝕂 := 𝕂) hb k,
            Matrix.mul_one] at h
          rw [Matrix.mul_assoc]
          exact h.symm
  have hβsc : ∀ r : 𝕂, β (Matrix.scalar (LargeEvenMinusIdx m) r) =
      Matrix.scalar (LargeEvenMinusIdx m) (σ r) := by
    intro r
    rw [hβ, hσ, kgLangCOmMAux_beta_scalar]
    rfl
  have hβiter_mat : ∀ (i : ℕ) (u : LargeEvenOmega (LargeEvenQMinus m b c)),
      (⇑β)^[i] (((u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
        (((S ^ i) u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
    intro i
    induction i with
    | zero => intro u; simp
    | succ i ih =>
        intro u
        rw [Function.iterate_succ_apply, hβmat, ih]
        rfl
  have hβiter_scalar : ∀ (i : ℕ) (r : 𝕂),
      (⇑β)^[i] (Matrix.scalar (LargeEvenMinusIdx m) r) =
        Matrix.scalar (LargeEvenMinusIdx m) ((σ ^ i) r) := by
    intro i
    induction i with
    | zero => intro r; simp
    | succ i ih =>
        intro r
        rw [Function.iterate_succ_apply, hβsc, ih]
        rfl
  have hβadd : ∀ (n : ℕ) (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂),
      (⇑β)^[n] (x + y) = (⇑β)^[n] x + (⇑β)^[n] y := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
        intro x y
        rw [Function.iterate_succ_apply, map_add, ih,
          Function.iterate_succ_apply, Function.iterate_succ_apply]
  have hβmul : ∀ (n : ℕ) (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂),
      (⇑β)^[n] (x * y) = (⇑β)^[n] x * (⇑β)^[n] y := by
    intro n
    induction n with
    | zero => intro x y; simp
    | succ n ih =>
        intro x y
        rw [Function.iterate_succ_apply, map_mul, ih,
          Function.iterate_succ_apply, Function.iterate_succ_apply]
  exact ⟨hβmat, hβsc, hβiter_mat, hβiter_scalar, hβadd, hβmul⟩

private theorem kgLangCOmMAux_postE {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m n : ℕ} (hm : 3 ≤ m)
    (𝕂 : Type) [Field 𝕂] [Finite 𝕂] [CharP 𝕂 2] (h𝕂 : Nat.card 𝕂 = 2 ^ n) (b c : 𝕂)
    (hbc : ∀ s : 𝕂, s ^ 2 + b * s + c ≠ 0) (hb : b ≠ 0)
    (J : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))))
    (hJ : (J : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) =
      LargeEvenInnSet _)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hfp : orderOf f = p)
    (e : LargeEvenOmega (LargeEvenQMinus m b c) ≃*
      LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
    (cA : LargeEvenOmega (LargeEvenQMinus m b c) →*
      MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))
    (hcA_apply : ∀ A, cA A = MulAut.conj (e A))
    (hcAinj : Function.Injective cA)
    (S : MulAut (LargeEvenOmega (LargeEvenQMinus m b c)))
    (hSe : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c), e (S u) = f (e u))
    (hSp : S ^ p = 1)
    (k : ℕ)
    (Θ : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) ≃*
      CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived
        (CFSG.RankThree.PartOne.AUTSL.Qm (m + 1) (by omega) b c))
    (frob : MulAut
      (CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear.matrixDerived
        (CFSG.RankThree.PartOne.AUTSL.Qm (m + 1) (by omega) b c)))
    (hfrob : frob = AutOm.frobAut (n := m + 1) (b := b) (c := c) (by omega) hbc)
    (hfk : MulAut.congr Θ f = frob ^ k)
    (σ : 𝕂 ≃+* 𝕂)
    (hσ : σ = (frobeniusEquiv 𝕂 2) ^ k)
    (hσp : σ ^ p = 1)
    (hn1 : 1 ≤ n)
    (β : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 →+*
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
    (hβmat : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      β ((u : GL (LargeEvenMinusIdx m) 𝕂) : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
        ((S u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))
    (hβsc : ∀ r : 𝕂, β (Matrix.scalar (LargeEvenMinusIdx m) r) =
      Matrix.scalar (LargeEvenMinusIdx m) (σ r))
    (hβiter_mat : ∀ (i : ℕ) (u : LargeEvenOmega (LargeEvenQMinus m b c)),
      (⇑β)^[i] (((u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
        (((S ^ i) u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))
    (hβiter_scalar : ∀ (i : ℕ) (r : 𝕂),
      (⇑β)^[i] (Matrix.scalar (LargeEvenMinusIdx m) r) =
        Matrix.scalar (LargeEvenMinusIdx m) ((σ ^ i) r))
    (hβadd : ∀ (j : ℕ) (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂),
      (⇑β)^[j] (x + y) = (⇑β)^[j] x + (⇑β)^[j] y)
    (hβmul : ∀ (j : ℕ) (x y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂),
      (⇑β)^[j] (x * y) = (⇑β)^[j] x * (⇑β)^[j] y)
    (tau : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 →
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
    (htau : tau = kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b)
    (E : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))))
    (hEelem : IsElemAbelian p E)
    (hEfix : ∀ x ∈ E, x ∈ J ∧ (MulAut.conj f).toMonoidHom x = x) :
    ∃ N : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))),
      N ≤ J ∧ (∀ a ∈ N, ∀ b ∈ N, a * b = b * a) ∧
      (∀ x ∈ N, (MulAut.conj f).toMonoidHom x ∈ N) ∧
      (∀ c ∈ N, ((List.range p).map fun i => endPow (MulAut.conj f).toMonoidHom i c).prod = 1 →
        ∃ s ∈ N, c = s⁻¹ * (MulAut.conj f).toMonoidHom s) ∧
      E ≤ N := by
  have hEinn : (E : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) ⊆
      Set.range (MulAut.conj :
        LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) →* _) := by
    intro x hx
    have hxJ : x ∈ (J : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) :=
      (hEfix x hx).1
    rw [hJ] at hxJ
    exact hxJ
  set Phat : Subgroup (LargeEvenOmega (LargeEvenQMinus m b c)) := E.comap cA with hPhat
  have hErange : E ≤ cA.range := by
    intro x hx
    obtain ⟨a, ha⟩ := hEinn hx
    obtain ⟨A, hA⟩ := e.surjective a
    refine ⟨A, ?_⟩
    change cA A = x
    rw [hcA_apply A, hA, ha]
  have hcP : Phat.map cA = E := by
    rw [hPhat, Subgroup.map_comap_eq, inf_eq_right.mpr hErange]
  have hPhat_ab : ∀ a ∈ Phat, ∀ b ∈ Phat, a * b = b * a := by
    intro a ha b hb
    rw [hPhat] at ha hb
    apply hcAinj
    rw [map_mul, map_mul]
    have hcomm : cA a * cA b = cA b * cA a := by
      letI : IsMulCommutative E := hEelem.1
      exact congrArg Subtype.val (mul_comm' (⟨cA a, ha⟩ : E) (⟨cA b, hb⟩ : E))
    exact hcomm
  have hcardPhat : Nat.card Phat = Nat.card E := by
    rw [← hcP]
    exact Nat.card_congr (Subgroup.equivMapOfInjective Phat cA hcAinj).toEquiv
  have hEodd : Odd (Nat.card E) := kgLangCOmMAux_odd_card_of_isElemAbelian hp hp2 hEelem
  set P : Subgroup (GL (LargeEvenMinusIdx m) 𝕂) :=
    Phat.map (LargeEvenOmega (LargeEvenQMinus m b c)).subtype with hP
  have hPab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
    intro a ha b hb
    rw [hP] at ha hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    exact congrArg (fun x : LargeEvenOmega (LargeEvenQMinus m b c) =>
      (x : GL (LargeEvenMinusIdx m) 𝕂)) (hPhat_ab a' ha' b' hb')
  have hcardP : Nat.card P = Nat.card E := by
    rw [hP, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hcardPhat]
  have hPodd : Odd (Nat.card P) := by rw [hcardP]; exact hEodd
  set B : Subalgebra 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) :=
    Algebra.adjoin 𝕂 ((fun g : GL (LargeEvenMinusIdx m) 𝕂 =>
      (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) '' (P : Set _)) with hB
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x :=
    (kgLangCOmMAux_adjoin_comm_reduced P hPab hPodd).1
  haveI : IsReduced B :=
    ⟨fun x hx => Subtype.ext
      ((kgLangCOmMAux_adjoin_comm_reduced P hPab hPodd).2 x x.2 (hx.map B.val))⟩
  have hcompat : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      cA (S u) = (MulAut.conj f).toMonoidHom (cA u) := by
    intro u
    rw [hcA_apply, hcA_apply, hSe u]
    ext r
    simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  have hS_mem : ∀ u ∈ Phat, S u ∈ Phat := by
    intro u hu
    rw [hPhat, Subgroup.mem_comap] at hu ⊢
    have hfix : (MulAut.conj f).toMonoidHom (cA u) = cA u := (hEfix (cA u) hu).2
    rw [hcompat u, hfix]
    exact hu
  have hβP : ∀ g ∈ P, β ((g : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) ∈
      (fun g : GL (LargeEvenMinusIdx m) 𝕂 =>
        (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) '' (P : Set _) := by
    intro g hg
    rw [hP] at hg
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
    refine ⟨(S u : GL (LargeEvenMinusIdx m) 𝕂), ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨S u, hS_mem u hu, rfl⟩
    · show ((S u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
        β ((u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
      exact (hβmat u).symm
  have hβB : ∀ a ∈ B, β a ∈ B := by
    intro a ha
    rw [hB] at ha ⊢
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      exact Algebra.subset_adjoin (hβP g₀ hg₀)
    · intro r
      change β (algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r) ∈ _
      rw [show algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r =
          Matrix.scalar (LargeEvenMinusIdx m) r from rfl, hβsc]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y hx hy hx' hy'
      rw [map_add]; exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      rw [map_mul]; exact mul_mem hx' hy'
  have hβp : ∀ a ∈ B, (⇑β)^[p] a = a := by
    intro a ha
    rw [hB] at ha
    refine Algebra.adjoin_induction (p := fun a _ => (⇑β)^[p] a = a) ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      rw [hP] at hg₀
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg₀
      change (⇑β)^[p] (((u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
        ((u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)
      rw [hβiter_mat p u, hSp]
      simp
    · intro r
      change (⇑β)^[p] (algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r) =
        algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r
      rw [show algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r =
          Matrix.scalar (LargeEvenMinusIdx m) r from rfl, hβiter_scalar p r, hσp]
      simp
    · intro x y hx hy hx' hy'
      rw [hβadd p, hx', hy']
    · intro x y hx hy hx' hy'
      rw [hβmul p, hx', hy']
  have hΩ_polar : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      ∀ p q : LargeEvenMinusIdx m → 𝕂,
        QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c)
          (((u : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec p)
          (((u : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec q) =
        QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) p q := by
    intro u p q
    apply kgLangCOmMAux_polar_preserved (TableBOrth.qMinusForm 𝕂 m b c)
    intro v
    rw [TableBOrth.coe_qMinusForm]
    exact kgLangCOmMAux_isometry_of_mem_orth
      (TableBOrth.omega_le_orth (LargeEvenQMinus m b c) u.2) v
  have hτB : ∀ a ∈ B, tau a ∈ B := by
    intro a ha
    rw [hB] at ha ⊢
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      rw [hP] at hg₀
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg₀
      change tau (((u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) ∈ _
      rw [htau, kgLangCOmMAux_tau_isometry b c hb
        ((u : GL (LargeEvenMinusIdx m) 𝕂)) (hΩ_polar u)]
      exact Algebra.subset_adjoin
        ⟨(((u⁻¹ : LargeEvenOmega (LargeEvenQMinus m b c)) :
            GL (LargeEvenMinusIdx m) 𝕂)),
          Subgroup.mem_map.mpr ⟨u⁻¹, Phat.inv_mem hu, rfl⟩, rfl⟩
    · intro r
      change tau (algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r) ∈ _
      rw [show algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r =
          Matrix.scalar (LargeEvenMinusIdx m) r from rfl, htau,
        kgLangCOmMAux_tau_scalar (𝕂 := 𝕂) (m := m) hb r]
      exact Subalgebra.algebraMap_mem _ _
    · intro x y hx hy hx' hy'
      change tau (x + y) ∈ _
      rw [htau] at hx' hy' ⊢
      rw [kgLangCOmMAux_tau_add]
      exact add_mem hx' hy'
    · intro x y hx hy hx' hy'
      change tau (x * y) ∈ _
      rw [htau] at hx' hy' ⊢
      rw [kgLangCOmMAux_tau_mul_anti (hb := hb)]
      exact mul_mem hy' hx'
  have hτadd : ∀ a ∈ B, ∀ b ∈ B, tau (a + b) = tau a + tau b :=
    fun a _ b _ => by rw [htau, kgLangCOmMAux_tau_add]
  have hτone : tau 1 = 1 := by rw [htau, kgLangCOmMAux_tau_one (𝕂 := 𝕂) hb]
  have hττ : ∀ a ∈ B, tau (tau a) = a :=
    fun a _ => by rw [htau, kgLangCOmMAux_tau_tau (𝕂 := 𝕂) hb]
  have hτmul : ∀ a ∈ B, ∀ c₀ ∈ B, tau (a * c₀) = tau a * tau c₀ := by
    intro a ha c₀ hc₀
    rw [show tau (a * c₀) = tau c₀ * tau a from by
      rw [htau, kgLangCOmMAux_tau_mul_anti (hb := hb)]]
    exact hBcomm (tau c₀) (hτB c₀ hc₀) (tau a) (hτB a ha)
  have hcoe_inv : ∀ x : LargeEvenOmega (LargeEvenQMinus m b c),
      ((((x⁻¹ : LargeEvenOmega (LargeEvenQMinus m b c)) : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
      (((x : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))⁻¹ := by
    intro x
    rw [Subgroup.coe_inv, Matrix.GeneralLinearGroup.coe_inv]
  have hτβ_gen : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      tau (β (((u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))) =
      β (tau (((u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))) := by
    intro u
    rw [hβmat u]
    have hL : tau (((S u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
        ((((S u)⁻¹ : LargeEvenOmega (LargeEvenQMinus m b c)) :
          GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
      rw [htau, hcoe_inv (S u)]
      exact (kgLangCOmMAux_tau_isometry b c hb ((S u : GL (LargeEvenMinusIdx m) 𝕂))
        (hΩ_polar (S u))).trans (Matrix.GeneralLinearGroup.coe_inv _)
    have hR : β (tau (((u : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))) =
        ((((S u)⁻¹ : LargeEvenOmega (LargeEvenQMinus m b c)) :
          GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
      rw [htau, kgLangCOmMAux_tau_isometry b c hb ((u : GL (LargeEvenMinusIdx m) 𝕂))
        (hΩ_polar u)]
      rw [Matrix.GeneralLinearGroup.coe_inv, ← hcoe_inv u, hβmat (u⁻¹)]
      rw [show ((S u⁻¹ : LargeEvenOmega (LargeEvenQMinus m b c)) : GL (LargeEvenMinusIdx m) 𝕂) =
          (((S u)⁻¹ : LargeEvenOmega (LargeEvenQMinus m b c)) : GL (LargeEvenMinusIdx m) 𝕂) from
        congrArg (fun x : LargeEvenOmega (LargeEvenQMinus m b c) =>
          (x : GL (LargeEvenMinusIdx m) 𝕂)) (map_inv S u)]
    rw [hL, hR]
  have hτβ : ∀ a ∈ B, tau (β a) = β (tau a) := by
    intro a ha
    rw [hB] at ha
    refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ ha
    · intro g hg
      obtain ⟨g₀, hg₀, rfl⟩ := hg
      rw [hP] at hg₀
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg₀
      exact hτβ_gen u
    · intro r
      change tau (β (algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r)) =
        β (tau (algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r))
      rw [show algebraMap 𝕂 (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) r =
          Matrix.scalar (LargeEvenMinusIdx m) r from rfl]
      have hL : tau (β (Matrix.scalar (LargeEvenMinusIdx m) r)) =
          Matrix.scalar (LargeEvenMinusIdx m) (σ r) := by
        rw [hβsc, htau, kgLangCOmMAux_tau_scalar (𝕂 := 𝕂) (m := m) hb]
      have hR : β (tau (Matrix.scalar (LargeEvenMinusIdx m) r)) =
          Matrix.scalar (LargeEvenMinusIdx m) (σ r) := by
        rw [htau, kgLangCOmMAux_tau_scalar (𝕂 := 𝕂) (m := m) hb, hβsc]
      rw [hL, hR]
    · intro x y hx hy hx' hy'
      have h1 : tau (β (x + y)) = tau (β x) + tau (β y) := by
        rw [map_add, hτadd (β x) (hβB x hx) (β y) (hβB y hy)]
      have h2 : β (tau (x + y)) = β (tau x) + β (tau y) := by
        rw [hτadd x hx y hy, map_add]
      rw [h1, h2, hx', hy']
    · intro x y hx hy hx' hy'
      have h1 : tau (β (x * y)) = tau (β x) * tau (β y) := by
        rw [map_mul, hτmul (β x) (hβB x hx) (β y) (hβB y hy)]
      have h2 : β (tau (x * y)) = β (tau x) * β (tau y) := by
        rw [hτmul x hx y hy, map_mul]
      rw [h1, h2, hx', hy']
  have hσord : orderOf σ = p := by
    haveI : Fact p.Prime := ⟨hp⟩
    refine orderOf_eq_prime hσp ?_
    intro hσ1
    obtain ⟨σ₀, hσ₀_apply, hσ₀_ord, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
        Nat.prime_two hn1 h𝕂
    have hσ_eq : σ = σ₀ ^ k := by
      rw [hσ]
      congr 1
      exact RingEquiv.ext fun a => by
        simp only [hσ₀_apply, frobeniusEquiv_apply, frobenius_def]
    have hσ₀k : σ₀ ^ k = 1 := hσ_eq.symm.trans hσ1
    have hnk : n ∣ k := by
      rw [← hσ₀_ord]
      exact orderOf_dvd_iff_pow_eq_one.mpr hσ₀k
    obtain ⟨j, hj⟩ := hnk
    have hfrob2 : (frob ^ k) ^ 2 = 1 := by
      rw [hfrob, hj, pow_mul, ← pow_mul, mul_comm j 2, pow_mul,
        AutOm.frobAut_pow_f_sq (n := m + 1) (b := b) (c := c) (by omega) hbc h𝕂, one_pow]
    have hf2 : f ^ 2 = 1 := by
      apply (MulAut.congr Θ).injective
      rw [map_pow, hfk, hfrob2, map_one]
    have hpdvd : p ∣ 2 := by
      rw [← hfp]
      exact orderOf_dvd_iff_pow_eq_one.mpr hf2
    have hple : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpdvd
    exact hp2 (le_antisymm hple hp.two_le)
  have hH90 := kgLangC_span_h90_unitary (p := p) (hp := hp) (σ := σ) (hσ := hσord)
    P hPab hPodd B rfl β hβP hβsc hβp
    tau hτB hτadd hτmul hτone hττ hτβ
  let Ugl : Subgroup (GL (LargeEvenMinusIdx m) 𝕂) :=
    { carrier := {x | (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) ∈ B ∧
        (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
          tau (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) = 1}
      mul_mem' := by
        intro x y hx hy
        refine ⟨?_, ?_⟩
        · rw [Units.val_mul]
          exact mul_mem hx.1 hy.1
        · rw [Units.val_mul,
            show tau ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
                (y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
              tau (y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
                tau (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) from by
              rw [htau, kgLangCOmMAux_tau_mul_anti (hb := hb)]]
          calc (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
                (y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
                (tau (y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
                  tau (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))
              = (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
                  ((y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
                    tau (y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) *
                  tau (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
                  simp only [Matrix.mul_assoc]
            _ = 1 := by rw [hy.2, Matrix.mul_one, hx.2]
      one_mem' := by
        refine ⟨B.one_mem, ?_⟩
        rw [Units.val_one, hτone, Matrix.mul_one]
      inv_mem' := by
        intro x hx
        have hinv : ((x⁻¹ : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
            tau ((x : GL (LargeEvenMinusIdx m) 𝕂) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
          rw [Matrix.GeneralLinearGroup.coe_inv]
          exact Matrix.inv_eq_right_inv hx.2
        refine ⟨?_, ?_⟩
        · rw [hinv]
          exact hτB _ hx.1
        · rw [hinv, hττ ((x : GL (LargeEvenMinusIdx m) 𝕂) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) hx.1]
          rw [show tau ((x : GL (LargeEvenMinusIdx m) 𝕂) :
                Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
              ((x : GL (LargeEvenMinusIdx m) 𝕂) :
                Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)⁻¹ from
            (Matrix.inv_eq_right_inv hx.2).symm]
          exact Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp ⟨x, rfl⟩) }
  have hUodd : Odd (Nat.card Ugl) := by
    rw [← Nat.not_even_iff_odd]
    intro heven
    have hdvd : 2 ∣ Nat.card Ugl := even_iff_two_dvd.mp heven
    letI : Fintype Ugl := Fintype.ofFinite Ugl
    rw [Nat.card_eq_fintype_card] at hdvd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card 2 hdvd
    have hx2U : (x : Ugl) ^ 2 = 1 := by simpa [hx] using pow_orderOf_eq_one x
    have hx2 : (x : GL (LargeEvenMinusIdx m) 𝕂) ^ 2 = 1 := by
      have := congrArg (fun y : Ugl => (y : GL (LargeEvenMinusIdx m) 𝕂)) hx2U
      simpa using this
    have hxne : x ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hx
      omega
    apply hxne
    set M : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
      ((x : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) with hM
    have hval2 : M * M = 1 := by
      have := congrArg (fun y : GL (LargeEvenMinusIdx m) 𝕂 =>
        (y : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) hx2
      simpa [hM, pow_two] using this
    have hnil : IsNilpotent (M + 1) := by
      refine ⟨2, ?_⟩
      rw [pow_two]
      rw [show (M + 1) * (M + 1) = M * M + (M + M) + 1 from by noncomm_ring]
      rw [hval2, CharTwo.add_self_eq_zero, add_zero]
      exact CharTwo.add_self_eq_zero 1
    have hmem : M + 1 ∈ B := by
      rw [hM]
      exact add_mem (x.2).1 (Subalgebra.one_mem B)
    have hzero := (kgLangCOmMAux_adjoin_comm_reduced P hPab hPodd).2 _ hmem hnil
    have hx1mat : ((x : GL (LargeEvenMinusIdx m) 𝕂) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) = 1 := by
      have h : M = -1 := eq_neg_of_add_eq_zero_left hzero
      rw [CharTwo.neg_eq] at h
      rwa [hM] at h
    apply Subtype.ext
    apply Units.ext
    exact hx1mat
  have hUΩ : Ugl ≤ LargeEvenOmega (LargeEvenQMinus m b c) := by
    intro x hx
    have hxB : (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) ∈ B := hx.1
    have hxτ : (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
        tau (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) = 1 := hx.2
    have hpolar : ∀ u v : LargeEvenMinusIdx m → 𝕂,
        QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c)
          ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec u)
          ((x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec v) =
        QuadraticMap.polar (TableBOrth.qMinusForm 𝕂 m b c) u v :=
      kgLangCOmMAux_polar_of_tau b c hb x (by
        rw [← htau]
        exact hxτ)
    have hPQ : ∀ g ∈ P, ∀ v : LargeEvenMinusIdx m → 𝕂,
        TableBOrth.qMinusForm 𝕂 m b c
          (((g : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂).mulVec v) =
        TableBOrth.qMinusForm 𝕂 m b c v := by
      intro g hg v
      rw [hP] at hg
      obtain ⟨A, hA, rfl⟩ := Subgroup.mem_map.mp hg
      rw [TableBOrth.coe_qMinusForm]
      exact kgLangCOmMAux_isometry_of_mem_orth
        (TableBOrth.omega_le_orth (LargeEvenQMinus m b c) A.2) v
    have hxspan : (x : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) ∈
        Submodule.span 𝕂 ((fun g : GL (LargeEvenMinusIdx m) 𝕂 =>
          (g : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) '' (P : Set _)) :=
      kgLangCOmMAux_adjoin_le_span P hxB
    have hQpres := kgLangC_quadratic_preserved (TableBOrth.qMinusForm 𝕂 m b c)
      (TableBOrth.nondegenerate_qMinusForm m hbc) P hPab hPodd hPQ hxspan hpolar
    have hT : ∃ T : Submodule 𝕂 (LargeEvenMinusIdx m → 𝕂),
        Module.finrank 𝕂 T = 3 ∧ ∀ y ∈ T, TableBOrth.qMinusForm 𝕂 m b c y = 0 := by
      let e : Fin 3 → LargeEvenMinusIdx m := fun i => Sum.inl (Sum.inl ⟨i, by omega⟩)
      have he : Function.Injective e := by
        intro i j h
        have h' : (⟨i, by omega⟩ : Fin m) = ⟨j, by omega⟩ :=
          Sum.inl_injective (Sum.inl_injective h)
        exact Fin.ext (by simpa using congrArg Fin.val h')
      have hli : LinearIndependent 𝕂 (fun i : Fin 3 =>
          (Pi.single (e i) (1 : 𝕂) : LargeEvenMinusIdx m → 𝕂)) := by
        rw [Fintype.linearIndependent_iff]
        intro g hg i
        have h := congrFun hg (e i)
        simp only [Finset.sum_apply, Pi.smul_apply] at h
        rw [Finset.sum_eq_single i] at h
        · simpa [Pi.single_apply] using h
        · intro j _ hji
          have hne : e i ≠ e j := fun hc => hji (he hc.symm)
          simp [Pi.single_apply, hne]
        · intro hi
          exact absurd (Finset.mem_univ i) hi
      refine ⟨Submodule.span 𝕂 (Set.range (fun i : Fin 3 =>
        (Pi.single (e i) (1 : 𝕂) : LargeEvenMinusIdx m → 𝕂))), ?_, ?_⟩
      · rw [finrank_span_eq_card hli, Fintype.card_fin]
      · intro y hy
        have hyy : ∀ i : Fin m, y (Sum.inl (Sum.inr i)) = 0 := by
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
          · intro z hz
            obtain ⟨k, rfl⟩ := hz
            exact fun i => by
              change Pi.single (e k) 1 (Sum.inl (Sum.inr i)) = 0
              rw [Pi.single_apply]
              exact if_neg (fun h => Sum.inr_ne_inl (Sum.inl_injective h))
          · intro i; simp
          · intro a b _ _ ha hb i
            simp [Pi.add_apply, ha i, hb i]
          · intro cc a _ ha i
            simp [Pi.smul_apply, ha i]
        have huv : ∀ j : Fin 2, y (Sum.inr j) = 0 := by
          refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
          · intro z hz
            obtain ⟨k, rfl⟩ := hz
            exact fun j => by simp
          · intro j; simp
          · intro a b _ _ ha hb j
            simp [Pi.add_apply, ha j, hb j]
          · intro cc a _ ha j
            simp [Pi.smul_apply, ha j]
        rw [TableBOrth.coe_qMinusForm]
        simp [LargeEvenQMinus, hyy, huv]
    have hgm : x ^ Nat.card Ugl = 1 := by
      have h' := congrArg Subtype.val (pow_card_eq_one' (G := Ugl) (x := ⟨x, hx⟩))
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at h'
    have hQmem := kgLangC_mem_omega_of_odd (TableBOrth.qMinusForm 𝕂 m b c)
      (TableBOrth.nondegenerate_qMinusForm m hbc) hT (by
        intro v
        exact hQpres v) hUodd hgm
    rwa [TableBOrth.coe_qMinusForm] at hQmem
  let U : Subgroup (LargeEvenOmega (LargeEvenQMinus m b c)) :=
    Ugl.comap (LargeEvenOmega (LargeEvenQMinus m b c)).subtype
  have hUm : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c),
      u ∈ U ↔ ((u : GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) ∈ B ∧
        ((u : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) *
          tau ((u : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) = 1 :=
    fun u => Iff.rfl
  let N : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) :=
    U.map cA
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  · rintro n ⟨u, -, rfl⟩
    change cA u ∈ (J : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))))
    rw [hJ, hcA_apply u]
    exact ⟨e u, rfl⟩
  · rintro a ⟨x, hx, rfl⟩ b ⟨y, hy, rfl⟩
    have hxy : x * y = y * x := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
      exact hBcomm _ ((hUm x).mp hx).1 _ ((hUm y).mp hy).1
    rw [← map_mul, hxy, map_mul]
  · rintro n ⟨u, hu, rfl⟩
    refine ⟨S u, ?_, hcompat u⟩
    refine (hUm (S u)).mpr ⟨?_, ?_⟩
    · rw [← hβmat u]
      exact hβB _ ((hUm u).mp hu).1
    · rw [htau, kgLangCOmMAux_tau_isometry b c hb (S u : GL (LargeEvenMinusIdx m) 𝕂)
        (hΩ_polar (S u)), Matrix.GeneralLinearGroup.coe_inv]
      exact Matrix.mul_nonsing_inv _
        ((Matrix.isUnit_iff_isUnit_det _).mp ⟨(S u : GL (LargeEvenMinusIdx m) 𝕂), rfl⟩)
  · rintro n ⟨u, hu, rfl⟩ hnorm
    have hgen : ∀ (i : ℕ) (w : LargeEvenOmega (LargeEvenQMinus m b c)),
        endPow (MulAut.conj f).toMonoidHom i (cA w) = cA ((S ^ i) w) := by
      intro i
      induction i with
      | zero => intro w; rw [endPow_apply]; rfl
      | succ i ih =>
          intro w
          rw [endPow_apply, Function.iterate_succ_apply', ← endPow_apply, ih w,
            ← hcompat ((S ^ i) w), pow_succ']
          rfl
    have hnormU : ((List.range p).map fun i => (S ^ i) u).prod = 1 := by
      apply hcAinj
      rw [map_one, MonoidHom.map_list_prod, List.map_map, ← hnorm]
      apply congrArg List.prod
      apply List.map_congr_left
      intro i _
      exact (hgen i u).symm
    set Mu : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
      (((u : GL (LargeEvenMinusIdx m) 𝕂)) :
        Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) with hMu
    have hnormMat : ((List.range p).map fun i => (⇑β)^[i] Mu).prod = 1 := by
      have hlist : (List.range p).map (fun i => (⇑β)^[i] Mu) =
          (List.range p).map (fun i =>
            ((((S ^ i) u : LargeEvenOmega (LargeEvenQMinus m b c)) :
              GL (LargeEvenMinusIdx m) 𝕂) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) :=
        List.map_congr_left (fun i _ => by rw [hMu, hβiter_mat i u])
      rw [hlist]
      have hcoe : (List.range p).map (fun i =>
            ((((S ^ i) u : LargeEvenOmega (LargeEvenQMinus m b c)) :
              GL (LargeEvenMinusIdx m) 𝕂) :
              Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)) =
          ((List.range p).map (fun i =>
            (S ^ i) u)).map
            ((Units.coeHom (Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂)).comp
              (LargeEvenOmega (LargeEvenQMinus m b c)).subtype) := by
        rw [List.map_map]; rfl
      rw [hcoe, ← MonoidHom.map_list_prod, hnormU, map_one]
    obtain ⟨s, hsB, hsτ, hsu⟩ := hH90 ((u : LargeEvenOmega (LargeEvenQMinus m b c)) :
      GL (LargeEvenMinusIdx m) 𝕂) ((hUm u).mp hu).1 ((hUm u).mp hu).2 hnormMat
    let sΩ : LargeEvenOmega (LargeEvenQMinus m b c) := ⟨s, hUΩ ⟨hsB, hsτ⟩⟩
    have hsU : sΩ ∈ U := (hUm sΩ).mpr ⟨hsB, hsτ⟩
    have hsu' : (((u : LargeEvenOmega (LargeEvenQMinus m b c)) :
          GL (LargeEvenMinusIdx m) 𝕂) :
          Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) =
        (((s : GL (LargeEvenMinusIdx m) 𝕂) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂))⁻¹ *
          ((((S sΩ : LargeEvenOmega (LargeEvenQMinus m b c)) :
              GL (LargeEvenMinusIdx m) 𝕂)) :
            Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂) := by
      rw [hsu, Matrix.GeneralLinearGroup.coe_inv, hβmat sΩ]
    have hsuΩ : u = sΩ⁻¹ * (S sΩ) := by
      apply Subtype.ext
      apply Units.ext
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul,
        Matrix.GeneralLinearGroup.coe_inv]
      exact hsu'
    refine ⟨cA sΩ, Subgroup.mem_map.mpr ⟨sΩ, hsU, rfl⟩, ?_⟩
    rw [hsuΩ, map_mul, map_inv, hcompat sΩ]
  · intro n hn
    rw [← hcP] at hn
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hn
    have huU : u ∈ U := by
      refine (hUm u).mpr ⟨?_, ?_⟩
      · rw [hB]
        exact Algebra.subset_adjoin
          ⟨(u : GL (LargeEvenMinusIdx m) 𝕂), Subgroup.mem_map.mpr ⟨u, hu, rfl⟩, rfl⟩
      · rw [htau, kgLangCOmMAux_tau_isometry b c hb (u : GL (LargeEvenMinusIdx m) 𝕂)
          (hΩ_polar u), Matrix.GeneralLinearGroup.coe_inv]
        exact Matrix.mul_nonsing_inv _
          ((Matrix.isUnit_iff_isUnit_det _).mp ⟨(u : GL (LargeEvenMinusIdx m) 𝕂), rfl⟩)
    exact Subgroup.mem_map.mpr ⟨u, huU, rfl⟩

theorem kgLangC_torusInput_omegaMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m n : ℕ} (hm : 3 ≤ m)
    (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n) (b c : 𝕂)
    (hbc : ∀ s : 𝕂, s ^ 2 + b * s + c ≠ 0)
    (J : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))))
    (hJ : (J : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) = LargeEvenInnSet _)
    {f : MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))}
    (hf : f ∈ LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c))))
    (hfp : orderOf f = p) :
    KGLangTorusInput p J (MulAut.conj f).toMonoidHom := by
  classical
  haveI : CharP 𝕂 2 := charP_two_of_card h𝕂
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos (by omega)
    have h1 : 1 < Nat.card 𝕂 := Finite.one_lt_card
    rw [h𝕂, hn0, pow_zero] at h1
    omega
  have hb : b ≠ 0 := CFSG.RankThree.PartOne.AUTSL.ne_zero_of_irreducible_tail b c hbc
  haveI hsS : IsSimpleGroup
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) 𝕂 b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
      (n := m + 1) (K := 𝕂) (by omega) hbc
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    (omegaMinusProjEquiv (m + 1) b c).isSimpleGroup
  haveI : Group.IsPerfect (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) 𝕂 b c)) :=
    CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus
      (n := m + 1) (K := 𝕂) (b := b) (c := c) (by omega) hbc
  haveI : Group.IsPerfect
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) 𝕂 b c))) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : Group.IsPerfect (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    Group.IsPerfect.ofSurjective
      (f := (omegaMinusProjEquiv (m + 1) b c).symm.toMonoidHom)
      (omegaMinusProjEquiv (m + 1) b c).symm.surjective
  have hnc : ¬ IsMulCommutative (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    Group.IsPerfect.not_isMulCommutative _
  have hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)), a * b ≠ b * a := by
    simpa only [isMulCommutative_iff, not_forall] using hnc
  have hZ : Subgroup.center (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) = ⊥ := by
    obtain ⟨a, b, hab⟩ := hna
    exact TableBOrth.center_eq_bot_of_simple hab
  set e := TableBOrth.projMkEquiv
    (TableBOrth.scalars_subgroupOf_omegaMinus_eq_bot (K := 𝕂) (m := m) b c) with he
  have he_apply : ∀ x, e x =
      LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)) x :=
    fun x => TableBOrth.projMkEquiv_apply _ x
  set cA : LargeEvenOmega (LargeEvenQMinus m b c) →*
      MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    (MulAut.conj : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)) →* _).comp
      e.toMonoidHom with hcAdef
  have hcA_apply : ∀ A, cA A = MulAut.conj (e A) := fun A => rfl
  have hcAinj : Function.Injective cA := by
    intro A B hAB
    exact e.injective (mulAut_conj_injective hZ hAB)
  obtain ⟨k, hk⟩ := hf
  set Θ := RecipeFieldOmega.minusEquiv (n := m + 1) (b := b) (c := c) (by omega) with hΘ
  set frob := AutOm.frobAut (n := m + 1) (b := b) (c := c) (by omega) hbc with hfrob
  have hfk : MulAut.congr Θ f = frob ^ k :=
    kgLangCOmMAux_hfk hm hbc k hk
  have hkpow : frob ^ (k * p) = 1 := by
    rw [pow_mul, ← hfk, ← map_pow]
    rw [show f ^ p = 1 by rw [← hfp]; exact pow_orderOf_eq_one f, map_one]
  have hdvd : n ∣ k * p :=
    CFSG.StandardType.AutOm.dvd_of_frobAut_pow_mem_inner
      (n := m + 1) (b := b) (c := c) (by omega) hbc h𝕂 hn1
      (by rw [hkpow]; exact Subgroup.one_mem _)
  set σ : 𝕂 ≃+* 𝕂 := (frobeniusEquiv 𝕂 2) ^ k with hσ
  have hσp : σ ^ p = 1 := by
    rw [hσ, ← pow_mul]
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, pow_mul]
    have hfn : (frobeniusEquiv 𝕂 2) ^ n = 1 :=
      CFSG.StandardType.RootDetectExc.frobeniusEquiv_pow_card (K := 𝕂) h𝕂
    rw [hfn, one_pow]
  set β : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 →+*
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
    kgLangCOmMAux_beta b c hb k with hβ
  set tau : Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 →
      Matrix (LargeEvenMinusIdx m) (LargeEvenMinusIdx m) 𝕂 :=
    kgLangCOmMAux_tau (𝕂 := 𝕂) (m := m) b with htau
  set S : MulAut (LargeEvenOmega (LargeEvenQMinus m b c)) :=
    MulAut.congr e.symm f with hS
  have hSe : ∀ u : LargeEvenOmega (LargeEvenQMinus m b c), e (S u) = f (e u) := by
    intro u
    rw [hS, MulAut.congr_apply]
    simp
  have hSp : S ^ p = 1 := by
    rw [hS, ← map_pow]
    rw [show f ^ p = 1 by rw [← hfp]; exact pow_orderOf_eq_one f, map_one]
  obtain ⟨hβmat, hβsc, hβiter_mat, hβiter_scalar, hβadd, hβmul⟩ :=
    kgLangCOmMAux_beta_facts hm hbc hb k S hSe Θ frob hΘ hfrob hfk σ hσ β hβ
  intro E hEelem hEfix
  exact kgLangCOmMAux_postE hp hp2 hm 𝕂 h𝕂 b c hbc hb J hJ hfp e cA hcA_apply hcAinj
    S hSe hSp k Θ frob hfrob hfk σ hσ hσp hn1 β hβmat hβsc hβiter_mat hβiter_scalar hβadd
    hβmul tau htau E hEelem hEfix

theorem kgLangTorusDatumCont_omegaMinus {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {m n : ℕ} (hm : 3 ≤ m)
    (hpn : p ∣ n) (𝕂 : Type) [Field 𝕂] [Finite 𝕂] (h𝕂 : Nat.card 𝕂 = 2 ^ n) (b c : 𝕂)
    (hbc : ∀ s : 𝕂, s ^ 2 + b * s + c ≠ 0)
    (hcyc : GGRawFieldCycW p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))))
    (hZ : ∀ [Finite (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))]
      (θ : HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) ⧸
        Subgroup.center (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) ≃*
          LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))),
      commutator (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) = ⊤ →
      Nat.Coprime
        (Nat.card (Subgroup.center (HopfCover (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))))) p) :
    KGLangTorusDatumCont p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) (LargeEvenInnSet _)
      (LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))) := by
  haveI : CharP 𝕂 2 := charP_two_of_card h𝕂
  have hn1 : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos (by omega)
    have h1 : 1 < Nat.card 𝕂 := Finite.one_lt_card
    rw [h𝕂, hn0, pow_zero] at h1
    omega
  haveI hsS : IsSimpleGroup
      (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) 𝕂 b c))) :=
    CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus
      (n := m + 1) (K := 𝕂) (by omega) hbc
  have hs : IsSimpleGroup (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
    (omegaMinusProjEquiv (m + 1) b c).isSimpleGroup
  have hna : ∃ a b : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)),
      a * b ≠ b * a := by
    haveI : Group.IsPerfect (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) 𝕂 b c)) :=
      CFSG.LieType.Universal.Spin.isPerfect_statedOmega_quadMinus
        (n := m + 1) (K := 𝕂) (b := b) (c := c) (by omega) hbc
    haveI hperfS : Group.IsPerfect
        (CFSG.Open.StatedProj (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus (m + 1) 𝕂 b c))) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
    haveI hperfR : Group.IsPerfect
        (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
      Group.IsPerfect.ofSurjective
        (f := (omegaMinusProjEquiv (m + 1) b c).symm.toMonoidHom)
        (omegaMinusProjEquiv (m + 1) b c).symm.surjective
    have hnc : ¬ IsMulCommutative (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))) :=
      Group.IsPerfect.not_isMulCommutative _
    simpa only [isMulCommutative_iff, not_forall] using hnc
  have hinn : ∀ r : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)),
      MulAut.conj r ∈ LargeEvenInnSet _ := fun r => ⟨r, rfl⟩
  have hG1 : ∀ u ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))),
      GGL45IsPElt p u → ∃ r : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)),
        u = MulAut.conj r := by
    rintro u ⟨r, rfl⟩ _
    exact ⟨r, rfl⟩
  have hconj : GGRawFieldConj p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))) :=
    RecipeFieldOmega.ggRawFieldConj_omegaMinus (n := m + 1) (b := b) (c := c) (by omega) hbc
      (f₀ := n) h𝕂 hn1 hp hp2
  have hT : ∀ J' : Subgroup (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))),
      (J' : Set (MulAut (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c))))) =
        LargeEvenInnSet _ →
      ∀ f ∈ LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c))),
        orderOf f = p →
        KGLangTorusInput p J' (MulAut.conj f).toMonoidHom := by
    intro J' hJ' f hf hfo
    exact kgLangC_torusInput_omegaMinus hp hp2 hm 𝕂 h𝕂 b c hbc J' hJ' hf hfo
  have hM : KGLangTorusMPart p (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))
      (LargeEvenInnSet _)
      (LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c)))) :=
    kgLangTorusMPart_of_inner hp hs hna hcyc hconj hinn hG1 hT (by
      intro hfin θ hcomm
      letI := hfin
      exact hZ θ hcomm)
  intro hfin θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  letI := hfin
  have hcyc' := hcyc hs hna
  obtain ⟨J, S, hJI, hJS, hN, hcycS, hpS⟩ := hcyc'
  have hα₀J : kgInducedAut θ α₀ ∉ J := by
    intro h
    exact hα₀I (hJI ▸ h)
  have hAS : ∀ α ∈ A, kgInducedAut θ α ∈ S := by
    intro α hα
    obtain ⟨u, huI, f, hfF, huf⟩ := hAI α hα
    apply hpS (kgInducedAut θ α)
    · rw [huf]
      exact Subgroup.mul_mem _
        (Subgroup.subset_closure (Set.mem_union_left
          (LargeEvenPhiQ m b c (LargeEvenProjMk (LargeEvenOmega (LargeEvenQMinus m b c))) : Set _)
          huI))
        (Subgroup.closure_mono (fun _ hx => Set.mem_union_right
          (LargeEvenInnSet (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus m b c)))) hx) hfF)
    · exact ⟨1, by rw [pow_one, ← map_pow, hA.2 α hα, map_one]⟩
  refine ⟨?_, hM θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I⟩
  intro α hα
  obtain ⟨k, hk⟩ := kgLangLT1_decomp hp θ hJS hN hcycS hA hAS hα₀ hα₀J α hα
  exact ⟨k, hJI ▸ hk⟩

end CFSG.StandardType
