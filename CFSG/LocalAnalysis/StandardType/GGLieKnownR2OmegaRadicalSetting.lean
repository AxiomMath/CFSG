module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2OmegaRadicalFrame
public import CFSG.LieType.Universal.SpinOmega.Kernel
public import CFSG.LieType.Universal.SpinOmega.Range
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.StandardType.LieKnownR2.POmega.Radical

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.StandardType CFSG.StandardType.ClassicalPosition

theorem spinOmegaData_quadPlus {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [CharP F 2] :
    SpinOmegaData (Spin.quadPlus n F) := by
  haveI : Algebra.IsCentral F (CliffordAlgebra (Spin.quadPlus n F)) :=
    isCentral_cliffordAlgebra_quadPlus F n
  exact ⟨ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero F 2),
    range_spinAction_quadPlus hn, nondegenerate_polarBilin_quadPlus n F⟩

theorem spinOmegaData_quadMinus {n : ℕ} (hn : 4 ≤ n) {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    SpinOmegaData (Spin.quadMinus n F b c) := by
  haveI : Algebra.IsCentral F (CliffordAlgebra (Spin.quadMinus n F b c)) :=
    isCentral_cliffordAlgebra_quadMinus n b c hirr
  exact ⟨ker_spinAction_eq_bot_of_isCentral _ (CharP.cast_eq_zero F 2),
    range_spinAction_quadMinus hn hirr, nondegenerate_polarBilin_quadMinus_of_finite n F hirr⟩

end CFSG.StandardType.LieKnownR2.POmega.Radical
