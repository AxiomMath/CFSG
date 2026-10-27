module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Exc
public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOPSUHolds
public import CFSG.Adapters.LieModelSimple
public import CFSG.Quasithin.Background.RonanF615QTK
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.Sec4.E27.D4TwoLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem mem_calP_subgroupOf {W : Type} [CommGroup W]
    [Module (ZMod 2) (Additive W)] {Y A : Subgroup (MulAut W)} (hA : A ∈ Pset Y) :
    A.subgroupOf Y ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.calP
      ((CFSG.RankThree.FFModules.autRep W).comp Y.subtype) := by
  have hρ : Function.Injective
      ((CFSG.RankThree.FFModules.autRep W).comp Y.subtype) :=
    (CFSG.RankThree.FFModules.autRep_injective (E := W)).comp Y.subtype_injective
  have hrep : CFSG.RankThree.FFModules.repMulAut
      ((CFSG.RankThree.FFModules.autRep W).comp Y.subtype) = Y.subtype := by
    ext y w
    rfl
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.K148.mem_calP_iff]
  have hmap : (A.subgroupOf Y).map
      (CFSG.RankThree.FFModules.repMulAut
        ((CFSG.RankThree.FFModules.autRep W).comp Y.subtype)) = A := by
    rw [hrep]
    exact Subgroup.map_subgroupOf_eq_of_le hA.1
  have hiff := CFSG.RankThree.FFModules.isFFStarOffender_map_iff hρ
    (A := A.subgroupOf Y) (Y := Y) (by rw [hmap]; exact hA.1)
  rw [hmap] at hiff
  exact hiff.1 hA

private theorem noSectionOffender_psu52
    {X : Type} [Group X] {V : Type} [CommGroup V] [Finite V]
    {Lb Eb : Subgroup (MulAut V)}
    (hU : LieModel X .PSU 5 2 2) (hXq : CFSG.IsQuasisimple X)
    (hV : ∀ v : V, v * v = 1)
    (hirr : CFSG.QuasithinUnique.Setup.X1.IsIrrOn Lb)
    (hq : CFSG.IsQuasisimple ↥Lb) (hE : Eb ≠ ⊥) (hEe : IsElemAbelian2 Eb)
    (hEq : IsQuadratic Eb)
    (hEN : Eb ≤ Subgroup.normalizer (Lb : Set (MulAut V)))
    (ψ : X →* ↥Lb) (hψ : Function.Surjective ψ) :
    Nat.card Eb * Nat.card (fixV Eb) < Nat.card V := by
  haveI : IsSimpleGroup X :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hU
  haveI : Nontrivial ↥Lb := CFSG.LocalCores.isQuasisimple_nontrivial hq
  haveI : IsSimpleGroup ↥Lb := IsSimpleGroup.isSimpleGroup_of_surjective ψ hψ
  have hZ : ¬ 5 ∣ Nat.card (Subgroup.center ↥Lb) := by
    rw [CFSG.LocalAnalysis.UniquenessCase.UC22.K148.ExcAux.center_eq_bot hq]
    norm_num
  have hmodel : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSU 5 2 2 :=
    CFSG.Blueprint.LieModel.statedClassicalModel hU (by decide)
  obtain ⟨c⟩ := CFSG.LocalAnalysis.UniquenessCase.UC22.K148.ExcAux.cq_equiv hXq hq ψ hψ
  have hcen : Subgroup.center X = ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K148.ExcAux.center_eq_bot hXq
  let e : (↥Lb ⧸ Subgroup.center ↥Lb) ≃* X :=
    c.trans ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot)
  have hm : CFSG.Assembly.LowTwoRank.StatedClassicalModel
      (↥Lb ⧸ Subgroup.center ↥Lb) .PSU 5 2 2 :=
    CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm hmodel
  exact CFSG.LocalAnalysis.RankThreeUC.S15.GN15.psuNoOffender_holds 5 2 5
    (by norm_num) (by norm_num) (by norm_num) (by decide) V hV Lb Eb hirr hq.1 hZ hm hEN
    hE hEe hEq

theorem k146FFSz_holds : K146FFSz := by
  intro W _ _ hW Y L n hO2 hL hSz A hA
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  let ρ : Representation (ZMod 2) ↥Y (Additive W) :=
    (CFSG.RankThree.FFModules.autRep W).comp Y.subtype
  have hρ : Function.Injective ρ :=
    (CFSG.RankThree.FFModules.autRep_injective (E := W)).comp Y.subtype_injective
  have hcomp : IsComponentOf (L.subgroupOf Y) ⊤ :=
    CFSG.Quasithin.RonanF615.isComponentOf_subgroupOf hL
  have hSz' : IsSz ↥(L.subgroupOf Y) n :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1).symm hSz
  have hAcal : A.subgroupOf Y ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.calP ρ :=
    mem_calP_subgroupOf hA
  have hcomm := CFSG.LocalAnalysis.UniquenessCase.UC22.K148.sz_commute_calP
    (ρ := ρ) hρ hcomp hSz' hAcal
  have hcomm' : ⁅A.subgroupOf Y, L.subgroupOf Y⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm] at hcomm
  have hmap := CFSG.commutator_subgroupOf_map_eq Y L A hL.1 hA.1
  rw [hcomm', Subgroup.map_bot] at hmap
  exact hmap.symm

theorem k146FFU54_holds :
    K146FFU54 := by
  intro W _ _ hW Y L hO2 hL hU A hA
  letI : Module (ZMod 2) (Additive W) := CFSG.RankThree.FFModules.moduleOfSq hW
  let ρ : Representation (ZMod 2) ↥Y (Additive W) :=
    (CFSG.RankThree.FFModules.autRep W).comp Y.subtype
  have hρ : Function.Injective ρ :=
    (CFSG.RankThree.FFModules.autRep_injective (E := W)).comp Y.subtype_injective
  have hcomp : IsComponentOf (L.subgroupOf Y) ⊤ :=
    CFSG.Quasithin.RonanF615.isComponentOf_subgroupOf hL
  have hU' : LieModel ↥(L.subgroupOf Y) .PSU 5 2 2 :=
    LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hL.1).symm hU
  have hAcal : A.subgroupOf Y ∈ CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.calP ρ :=
    mem_calP_subgroupOf hA
  have hXq : CFSG.IsQuasisimple ↥(L.subgroupOf Y) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K148.ExcAux.isQuasisimple_of_isComponentOf hcomp
  have hcomm := CFSG.LocalAnalysis.UniquenessCase.UC22.K148.commute_calP_of_noSectionOffender
    (ρ := ρ) hρ hcomp
    (fun V _ _ Lb Eb hV hirr hq hE0 hEe hEq hEN ⟨ψ, hψ⟩ =>
      noSectionOffender_psu52 hU' hXq hV hirr hq hE0 hEe hEq hEN ψ hψ)
    hAcal
  have hcomm' : ⁅A.subgroupOf Y, L.subgroupOf Y⁆ = ⊥ := by
    rwa [Subgroup.commutator_comm] at hcomm
  have hmap := CFSG.commutator_subgroupOf_map_eq Y L A hL.1 hA.1
  rw [hcomm', Subgroup.map_bot] at hmap
  exact hmap.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
