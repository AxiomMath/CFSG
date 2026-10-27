module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusVectors
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusPlane
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOm.MinusSylow
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.ClassicalGroups.Orthogonal.RootGroupFixedCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

open CFSG.Open Matrix QuadraticMap
open CFSG.ClassicalGroups.Orthogonal (eichler eichler_apply eichler_mem_rootGroup rootGroupGL
  toLinEquiv toLinEquiv_apply)
open CFSG.LieType.Universal.Spin (quadMinus)

local notation "ιM" => Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

variable {K : Type} [Field K]

private def yVec : ιM → K := Pi.single (Sum.inr (Sum.inl 0)) 1

@[simp] private theorem yVec_inl (i : Fin (2 - 1)) : yVec (K := K) (Sum.inl i) = 0 :=
  Pi.single_eq_of_ne (M := fun _ : ιM => K) (by simp) 1

@[simp] private theorem yVec_y : yVec (K := K) (Sum.inr (Sum.inl 0)) = 1 := by
  rw [yVec]
  exact Pi.single_eq_same _ _

@[simp] private theorem yVec_plane (i : Fin 2) : yVec (K := K) (Sum.inr (Sum.inr i)) = 0 :=
  Pi.single_eq_of_ne (M := fun _ : ιM => K) (by simp) 1

private theorem quadMinus_yVec (b c : K) : quadMinus 2 K b c yVec = 0 := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply]
  simp [yVec, Pi.single_apply]

@[simp] private theorem polar_yVec_planeVec (b c : K) (a : Fin 2 → K) :
    polar (quadMinus 2 K b c) yVec (planeVec a) = 0 := by
  rw [polar_comm]
  change polar (quadMinus 2 K b c) (planeVec a) (Pi.single (Sum.inr (Sum.inl 0)) (1 : K)) = 0
  rw [CFSG.LieType.Universal.Spin.polar_quadMinus_single_inr_inl]
  simp only [planeVec_inl]

@[simp] private theorem polar_planeVec_yVec (b c : K) (a : Fin 2 → K) :
    polar (quadMinus 2 K b c) (planeVec a) yVec = 0 := by
  rw [polar_comm, polar_yVec_planeVec]

@[simp] private theorem polar_planeVec_self [CharP K 2] (b c : K) (a : Fin 2 → K) :
    polar (quadMinus 2 K b c) (planeVec a) (planeVec a) = 0 := by
  rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

@[simp] private theorem polar_e1M_yVec (b c : K) :
    polar (quadMinus 2 K b c) (KTabC.e1M K) yVec = 1 := by
  rw [polar_e1M_eq_y, yVec_y]

@[simp] private theorem polar_e1M_planeVec (b c : K) (a : Fin 2 → K) :
    polar (quadMinus 2 K b c) (KTabC.e1M K) (planeVec a) = 0 := by
  rw [polar_e1M_eq_y, planeVec_inr_inl]

theorem exists_mem_statedOmega_fix_planeVec [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {a : Fin 2 → K} (ha0 : a ≠ 0) :
    ∃ h ∈ StatedOmega (StatedQuadMinus 2 K b c),
      (h : Matrix ιM ιM K) *ᵥ planeVec a = planeVec a ∧
        ∀ s : K, (h : Matrix ιM ιM K) *ᵥ KTabC.e1M K ≠ s • KTabC.e1M K := by
  classical
  set h : GL ιM K := (toLinEquiv ιM K).symm (eichler (quadMinus 2 K b c) yVec (planeVec a))
    with hh
  have hhmat : ∀ x : ιM → K, (h : Matrix ιM ιM K) *ᵥ x =
      eichler (quadMinus 2 K b c) yVec (planeVec a) x := by
    intro x
    rw [hh, ← toLinEquiv_apply, MulEquiv.apply_symm_apply]
  refine ⟨h, ?_, ?_, ?_⟩
  · refine rootGroupGL_le_statedOmega_minus hirr yVec ?_
    rw [rootGroupGL, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hh,
      MulEquiv.apply_symm_apply]
    exact eichler_mem_rootGroup (Q := quadMinus 2 K b c) (polar_yVec_planeVec b c a)
  · rw [hhmat, eichler_apply (quadMinus_yVec b c) (polar_yVec_planeVec b c a)]
    simp only [polar_planeVec_yVec, polar_planeVec_self, mul_zero, zero_mul, zero_add, zero_smul,
      add_zero, sub_zero]
  · intro s hs
    have hcoord : ∀ k : Fin 2, a k = 0 := by
      intro k
      have h1 := congrFun hs (Sum.inr (Sum.inr k))
      rw [hhmat, eichler_apply (quadMinus_yVec b c) (polar_yVec_planeVec b c a)] at h1
      simpa only [polar_e1M_yVec, polar_e1M_planeVec, Pi.add_apply, Pi.sub_apply, Pi.smul_apply,
        one_smul, zero_add, mul_one, e1M_apply_plane, yVec_plane, planeVec_inr_inr, smul_eq_mul,
        mul_zero, sub_zero] using h1
    exact ha0 (funext hcoord)

end CFSG.LocalAnalysis.UniquenessCase.UC22.KOm

end
