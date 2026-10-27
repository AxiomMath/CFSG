module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45FinalTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeAFrame
public import CFSG.LieType.SeitzGeneration.OuterLinearLift
public import CFSG.Quasithin.SteinbergBIOddLinearThreeDiagonal
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.RankThree.SteinbergR3ELinearPointwiseAutomorphisms
public import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
public import CFSG.LieType.SeitzGeneration.Inner
public import CFSG.LieType.SeitzGeneration.Lift
public import CFSG.LieType.SeitzGeneration.OuterLinearPlane
public import CFSG.LieType.SeitzGeneration.OuterModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.RankThree.PartOne.CTP.SeitzLinear
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.RankThree.PartOne.KC.LinearDegreeFive
public import CFSG.RankThree.PartOne.KC.LinearEndpointStatements
public import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
public import CFSG.RankThree.PartOne.S11d.OutLinear
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Defs
public import Certificates.Certificate1
public import Certificates.Certificate2

public section

namespace CFSG.StandardType

namespace RawTorusPProof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.ComponentClassification

section Matrices

variable {d : ℕ} {F : Type} [Field F]

theorem isDiag_of_commute_separating {X : Matrix (Fin d) (Fin d) F}
    (h : ∀ i j, i ≠ j → ∃ D : Matrix (Fin d) (Fin d) F, D.IsDiag ∧ D i i ≠ D j j ∧
      X * D = D * X) : X.IsDiag := by
  intro i j hij
  obtain ⟨D, hD, hne, hXD⟩ := h i j hij
  have h1 := congrFun (congrFun hXD i) j
  rw [← (isDiag_iff_diagonal_diag D).mp hD, mul_diagonal, diagonal_mul, diag_apply,
    diag_apply] at h1
  have h2 : (D i i - D j j) * X i j = 0 := by linear_combination -h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact absurd (sub_eq_zero.mp h3) hne
  · exact h3

variable [Finite F]

end Matrices

end RawTorusPProof

end CFSG.StandardType

end
