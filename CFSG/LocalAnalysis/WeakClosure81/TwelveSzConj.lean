module

public import CFSG.LocalAnalysis.WeakClosure81.TwelveSetting
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
public import CFSG.LieType.BorelTits.Suzuki
import all CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import all TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.GraphAutomorphism
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.WeakClosure81.TenFive
public import CFSG.LocalAnalysis.WeakClosure81.Twelve
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure38Facts
public import CFSG.Quasithin.Background.B2Thompson
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open scoped Matrix
open CFSG.Blueprint

theorem transpose_mul_suzukiW_mul {K : Type} [Field K] [CharP K 2] (a : ℕ) {m : GL (Fin 4) K}
    (hm : m ∈ CFSG.Blueprint.suzukiGroup a K) :
    (m : Matrix (Fin 4) (Fin 4) K)ᵀ * CFSG.Blueprint.suzukiW K * (m : Matrix (Fin 4) (Fin 4) K) =
      CFSG.Blueprint.suzukiW K := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h4 : (4 : K) = 0 := by rw [show (4 : K) = 2 * 2 by norm_num, h2, zero_mul]
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨u, v, h⟩ | ⟨l, h⟩ | h
    · rw [h]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suzukiS, suzukiN, suzukiW, Matrix.mul_apply, Fin.sum_univ_four] <;>
        (ring_nf; simp [h2, h4])
    · have hl : (l : K) ≠ 0 := l.ne_zero
      rw [h]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suzukiD, suzukiW, Matrix.mul_apply, Fin.sum_univ_four, Matrix.diagonal_apply]
      · rw [← zpow_add₀ hl]
        have : (1 + (2 : ℤ) ^ a + (-1 - 2 ^ a)) = 0 := by ring
        rw [this, zpow_zero]
      · exact mul_inv_cancel₀ (zpow_ne_zero _ hl)
      · exact inv_mul_cancel₀ (zpow_ne_zero _ hl)
      · rw [← zpow_add₀ hl]
        have : (-1 - (2 : ℤ) ^ a + (1 + 2 ^ a)) = 0 := by ring
        rw [this, zpow_zero]
    · rw [h]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [suzukiW, Matrix.mul_apply, Fin.sum_univ_four]
  | one => simp
  | mul x y hx hy ihx ihy =>
    rw [Units.val_mul, Matrix.transpose_mul]
    calc (y : Matrix (Fin 4) (Fin 4) K)ᵀ * (x : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K *
          ((x : Matrix (Fin 4) (Fin 4) K) * (y : Matrix (Fin 4) (Fin 4) K))
        = (y : Matrix (Fin 4) (Fin 4) K)ᵀ * ((x : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K *
            (x : Matrix (Fin 4) (Fin 4) K)) * (y : Matrix (Fin 4) (Fin 4) K) := by
          simp only [Matrix.mul_assoc]
      _ = suzukiW K := by rw [ihx, ihy]
  | inv x hx ih =>
    have h1 : ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) *
        (x : Matrix (Fin 4) (Fin 4) K) = 1 := by simp
    have h2' : (x : Matrix (Fin 4) (Fin 4) K) *
        ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 := by simp
    calc ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K *
          ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
            ((x : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K * (x : Matrix (Fin 4) (Fin 4) K)) *
            ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by rw [ih]
      _ = ((x : Matrix (Fin 4) (Fin 4) K) * ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ *
            suzukiW K * ((x : Matrix (Fin 4) (Fin 4) K) *
            ((x⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
          rw [Matrix.transpose_mul]
          simp only [Matrix.mul_assoc]
      _ = suzukiW K := by rw [h2']; simp

theorem inverseTranspose_eq_suzukiW_conj {K : Type} [Field K] [CharP K 2] (a : ℕ)
    {m : GL (Fin 4) K} (hm : m ∈ CFSG.Blueprint.suzukiGroup a K) :
    ((Matrix.GeneralLinearGroup.inverseTranspose m : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      CFSG.Blueprint.suzukiW K * (m : Matrix (Fin 4) (Fin 4) K) * CFSG.Blueprint.suzukiW K := by
  have hJ := transpose_mul_suzukiW_mul a hm
  have hJJ : suzukiW K * suzukiW K = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [suzukiW, Matrix.mul_apply, Fin.sum_univ_four]
  have hJT : (suzukiW K)ᵀ = suzukiW K := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [suzukiW, Matrix.transpose_apply]
  have hMn : (m : Matrix (Fin 4) (Fin 4) K) * ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
      = 1 := by simp
  have h1 : suzukiW K * ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      (m : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K := by
    calc suzukiW K * ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = ((m : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K * (m : Matrix (Fin 4) (Fin 4) K)) *
            ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by rw [hJ]
      _ = (m : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K * ((m : Matrix (Fin 4) (Fin 4) K) *
            ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by rw [Matrix.mul_assoc]
      _ = (m : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K := by rw [hMn, Matrix.mul_one]
  have h2 : ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
      suzukiW K * (m : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K := by
    calc ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
        = (suzukiW K * suzukiW K) * ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by
          rw [hJJ, Matrix.one_mul]
      _ = suzukiW K * (suzukiW K * ((m⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
          rw [Matrix.mul_assoc]
      _ = suzukiW K * ((m : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K) := by rw [h1]
      _ = suzukiW K * (m : Matrix (Fin 4) (Fin 4) K)ᵀ * suzukiW K := by rw [Matrix.mul_assoc]
  rw [Matrix.GeneralLinearGroup.coe_inverseTranspose, h2, Matrix.transpose_mul,
    Matrix.transpose_mul, Matrix.transpose_transpose, hJT]
  simp only [Matrix.mul_assoc]

end CFSG.LocalAnalysis.WeakClosure81
