module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.Data.ZMod.Basic
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotClasses
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6SecondGraphFullCentralizer
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenCanonicalField
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace CFSG.StandardType

namespace GGA3

open Matrix

theorem zmod_two_eq_one_of_mul_eq_one {a b : ZMod 2} (h : a * b = 1) : a = 1 := by
  revert a b
  decide

theorem det_eq_one_of_mul_eq_one {A B : Matrix (Fin 8) (Fin 8) (ZMod 2)} (h : A * B = 1) :
    A.det = 1 := by
  have h' := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at h'
  exact zmod_two_eq_one_of_mul_eq_one h'

@[expose] def omMat (k : ℕ) : Matrix (Fin 8) (Fin 8) (ZMod 2) := fun i j =>
  if i.val / 2 = k ∧ j.val / 2 = k then
    (if i.val % 2 = 0 then (if j.val % 2 = 0 then 0 else 1) else 1)
  else if i = j then 1 else 0

@[expose] def swapMat : Matrix (Fin 8) (Fin 8) (ZMod 2) := fun i j =>
  if j.val = (i.val + 4) % 8 then 1 else 0

theorem omMat_cube {k : ℕ} (hk : k < 4) : omMat k * (omMat k * omMat k) = 1 := by
  interval_cases k <;> decide

theorem swapMat_sq : swapMat * swapMat = 1 := by
  decide

theorem swapMat_mul_omMat_mul {k : ℕ} (hk : k < 4) :
    swapMat * omMat k * swapMat = omMat ((k + 2) % 4) := by
  interval_cases k <;> decide

@[expose] def omSL (k : ℕ) (hk : k < 4 := by decide) : Matrix.SpecialLinearGroup (Fin 8) (ZMod 2) :=
  ⟨omMat k, det_eq_one_of_mul_eq_one (omMat_cube hk)⟩

@[expose] def swapSL : Matrix.SpecialLinearGroup (Fin 8) (ZMod 2) :=
  ⟨swapMat, det_eq_one_of_mul_eq_one swapMat_sq⟩

theorem swapSL_inv : swapSL⁻¹ = swapSL := by
  rw [inv_eq_iff_mul_eq_one]
  exact Subtype.ext swapMat_sq

theorem swapSL_mul_omSL_mul_inv {k : ℕ} (hk : k < 4) :
    swapSL * omSL k hk * swapSL⁻¹ = omSL ((k + 2) % 4) (Nat.mod_lt _ (by norm_num)) := by
  rw [swapSL_inv]
  exact Subtype.ext (swapMat_mul_omMat_mul hk)

@[expose] def slD : Subgroup (Matrix.SpecialLinearGroup (Fin 8) (ZMod 2)) :=
  Subgroup.closure {omSL 0, omSL 1}

@[expose] def slT : Subgroup (Matrix.SpecialLinearGroup (Fin 8) (ZMod 2)) :=
  Subgroup.closure {omSL 2, omSL 3}

theorem map_conj_swapSL_slD : slD.map (MulAut.conj swapSL).toMonoidHom = slT := by
  rw [slD, slT, MonoidHom.map_closure, Set.image_pair]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  rw [swapSL_mul_omSL_mul_inv (k := 0), swapSL_mul_omSL_mul_inv (k := 1)]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.LieType.Steinberg.Adjoint

end GGA3

end CFSG.StandardType
