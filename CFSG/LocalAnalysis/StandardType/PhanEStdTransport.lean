module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LieType.RootSystem.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.RootSystem

theorem coxeterMatrix_cartanE6 {A : Matrix (Fin 6) (Fin 6) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAE : A = CartanMatrix.E 6) : coxeterMatrix hA = CoxeterMatrix.E₆ := by
  subst hAE
  ext i j
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.E, CoxeterMatrix.E₆]

theorem coxeterMatrix_cartanE7 {A : Matrix (Fin 7) (Fin 7) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAE : A = CartanMatrix.E 7) : coxeterMatrix hA = CoxeterMatrix.E₇ := by
  subst hAE
  ext i j
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.E, CoxeterMatrix.E₇]

theorem coxeterMatrix_cartanE8 {A : Matrix (Fin 8) (Fin 8) ℤ} (hA : TauCeti.IsFiniteType A)
    (hAE : A = CartanMatrix.E 8) : coxeterMatrix hA = CoxeterMatrix.E₈ := by
  subst hAE
  ext i j
  simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply]
  fin_cases i <;> fin_cases j <;> simp [CartanMatrix.E, CoxeterMatrix.E₈]

end CFSG.ClassicalInvolution.Phan.PhanE
