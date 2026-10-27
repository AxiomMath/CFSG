module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary
public import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.Open.StatedDefs
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

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

variable {K : Type} [Field K]

theorem sec7_polar_quadPlus_iff (x e : Fin 4 ⊕ Fin 4 → K) :
    polar (quadPlus 4 K) e x = 0 ↔
      StatedQuadPlus 4 K (x + e) - StatedQuadPlus 4 K x - StatedQuadPlus 4 K e = 0 := by
  rw [QuadraticMap.polar_comm, ← coe_quadPlus 4 K]
  exact Iff.rfl

theorem sec7_rootGroupGL_eq_LomGLPlus {m : ℕ} (hm : 3 ≤ m) (u : Fin m ⊕ Fin m → K) :
    rootGroupGL (quadPlus m K) u = LomGLPlus hm u :=
  (LomGL_eq_rootGroupGL (coe_quadPlus m K) (commutator_orthogonalGroup_quadPlus hm) u).symm

theorem sec7_siegel_iff_rootGroupGL {e : Fin 4 ⊕ Fin 4 → K}
    (he : StatedQuadPlus 4 K e = 0) (he0 : e ≠ 0) (g : StatedOmega (StatedQuadPlus 4 K)) :
    (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = e ∧
      (∀ x : Fin 4 ⊕ Fin 4 → K, StatedQuadPlus 4 K (x + e) - StatedQuadPlus 4 K x -
          StatedQuadPlus 4 K e = 0 →
        ∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x = c • e) ∧
      (∀ x : Fin 4 ⊕ Fin 4 → K,
        StatedQuadPlus 4 K ((((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) + e) -
          StatedQuadPlus 4 K (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) -
          StatedQuadPlus 4 K e = 0)) ↔
      (g : GL (Fin 4 ⊕ Fin 4) K) ∈ rootGroupGL (quadPlus 4 K) e := by
  have hu : quadPlus 4 K e = 0 := (congrFun (coe_quadPlus 4 K) e).trans he
  rw [sec7_rootGroupGL_eq_LomGLPlus (K := K) (by norm_num : 3 ≤ 4) e,
    mem_LomGLPlus_iff (by norm_num : 3 ≤ 4) hu he0]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨g.2, h1, fun x hx => h2 x ((sec7_polar_quadPlus_iff x e).mp hx),
      fun x => (sec7_polar_quadPlus_iff _ e).mpr (h3 x)⟩
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨h1, fun x hx => h2 x ((sec7_polar_quadPlus_iff x e).mpr hx),
      fun x => (sec7_polar_quadPlus_iff _ e).mp (h3 x)⟩

theorem sec7_card_siegel {e : Fin 4 ⊕ Fin 4 → K}
    (he : StatedQuadPlus 4 K e = 0) (he0 : e ≠ 0) :
    Nat.card {g : StatedOmega (StatedQuadPlus 4 K) //
      (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec e = e ∧
        (∀ x : Fin 4 ⊕ Fin 4 → K, StatedQuadPlus 4 K (x + e) - StatedQuadPlus 4 K x -
            StatedQuadPlus 4 K e = 0 →
          ∃ c : K, ((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x = c • e) ∧
        (∀ x : Fin 4 ⊕ Fin 4 → K,
          StatedQuadPlus 4 K ((((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) + e) -
            StatedQuadPlus 4 K (((g : GL (Fin 4 ⊕ Fin 4) K) : Matrix _ _ K).mulVec x - x) -
            StatedQuadPlus 4 K e = 0))} = Nat.card K ^ 6 := by
  have hu : quadPlus 4 K e = 0 := (congrFun (coe_quadPlus 4 K) e).trans he
  have hm : 3 ≤ 4 := by norm_num
  have hH : rootGroupGL (quadPlus 4 K) e = LomGLPlus hm e := sec7_rootGroupGL_eq_LomGLPlus hm e
  have hle : rootGroupGL (quadPlus 4 K) e ≤ StatedOmega (StatedQuadPlus 4 K) := by
    rw [hH]
    exact Subgroup.map_subtype_le _
  have hfin : Module.finrank K (Fin 4 ⊕ Fin 4 → K) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hLe := CFSG.ClassicalGroups.Orthogonal.rootGroup_le_elementaryGroup (quadPlus 4 K) e
  have hLom : Nat.card ↥(CFSG.ClassicalGroups.Orthogonal.Lom (quadPlus 4 K) e) =
      Nat.card ↥(CFSG.ClassicalGroups.Orthogonal.rootGroup (quadPlus 4 K) e) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLe).toEquiv
  have hcard : Nat.card (rootGroupGL (quadPlus 4 K) e) = Nat.card K ^ (8 - 2) := by
    rw [hH, LomGLPlus,
      Subgroup.card_map_of_injective (f := (StatedOmega (StatedQuadPlus 4 K)).subtype)
        (Subgroup.subtype_injective _),
      Subgroup.card_map_of_injective (f := (statedOmegaPlusEquiv (K := K) hm).symm.toMonoidHom)
        (statedOmegaPlusEquiv (K := K) hm).symm.injective,
      hLom, CFSG.ClassicalGroups.Orthogonal.card_rootGroup
        (nondegenerate_polarBilin_quadPlus 4 K) hu he0, hfin]
  refine (Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    sec7_siegel_iff_rootGroupGL he he0 g)).trans ?_
  refine (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).trans ?_
  exact hcard

end CFSG.RankThree.GF2n.Stroth80
