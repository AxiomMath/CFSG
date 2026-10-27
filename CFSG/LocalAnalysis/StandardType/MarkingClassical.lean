module

public import CFSG.LocalAnalysis.StandardType.MarkingDict
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.ClassicalModelStatedBridge

variable {K : Type} [Field K]

theorem nonempty_proj_congr {ι : Type} [Fintype ι] [DecidableEq ι] {H H' : Subgroup (GL ι K)}
    (h : H = H') : Nonempty (LargeEvenProj H ≃* StatedProj H') := by
  subst h
  exact ⟨MulEquiv.refl _⟩

@[expose] noncomputable def omegaMinusProjEquiv (l : ℕ) (b c : K) :
    LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus l K b c)) :=
  (mapMkEquivStatedProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c))).symm.trans
    (omegaModelMinusEquiv l b c)

variable [Finite K]

theorem statedClassicalModel_linear (d f : ℕ) (hK : Nat.card K = 2 ^ f)
    (hadm : StatedLieAdmissible .PSL d 2 f) :
    StatedClassicalModel (LargeEvenProj (LargeEvenSLGroup (Fin d) K)) .PSL d 2 f :=
  ⟨hadm, K, inferInstance, inferInstance, hK,
    nonempty_proj_congr (statedSL_eq_ker_det d K).symm⟩

theorem statedClassicalModel_unitary (d n : ℕ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hadm : StatedLieAdmissible .PSU d 2 n) :
    StatedClassicalModel (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n))) .PSU d 2 n :=
  ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩

theorem statedClassicalModel_symplectic (m n : ℕ) (hK : Nat.card K = 2 ^ n)
    (hadm : StatedLieAdmissible .PSp m 2 n) :
    StatedClassicalModel (LargeEvenProj (LargeEvenSpGroup K m)) .PSp m 2 n :=
  ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩

theorem statedClassicalModel_omegaPlus (m n : ℕ) (hK : Nat.card K = 2 ^ n)
    (hadm : StatedLieAdmissible .POmegaPlus m 2 n) :
    StatedClassicalModel (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K m))) .POmegaPlus m 2 n :=
  ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩

theorem statedClassicalModel_omegaMinus (l n : ℕ) (hK : Nat.card K = 2 ^ n) (b c : K)
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hadm : StatedLieAdmissible .POmegaMinus l 2 n) :
    StatedClassicalModel (LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (l - 1) b c)))
      .POmegaMinus l 2 n :=
  ⟨hadm, K, inferInstance, inferInstance, hK, b, c, hbc, ⟨omegaMinusProjEquiv l b c⟩⟩

end CFSG.StandardType
