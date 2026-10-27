module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18FFSzU54
public import CFSG.GroupTheory.IrreducibleAbelianAction
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148IdL2S5
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SecNatRealizes
public import CFSG.Quasithin.Background.FFC7A
public import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit415Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

theorem k146FFL2_holds :
    K146FFL2 := by
  intro W _ _ hW Y L n hO2 hcomp hL2 hn2 hoff
  classical
  letI : Module (ZMod 2) (Additive W) := CFSG.GroupTheory.elemModule 2 hW
  let ρ : Representation (ZMod 2) Y (Additive W) :=
    (CFSG.RankThree.FFModules.autRep W).comp Y.subtype
  have hρinj : Function.Injective ρ :=
    (CFSG.RankThree.FFModules.autRep_injective (E := W)).comp Y.subtype_injective
  let L' : Subgroup Y := L.subgroupOf Y
  have hLmap : L'.map Y.subtype = L := Subgroup.map_subgroupOf_eq_of_le hcomp.1
  have hcomp' : IsComponentOf L' ⊤ := CFSG.Quasithin.RonanF615.isComponentOf_subgroupOf hcomp
  have hL2' : UC22.IsL2 ↥L' n :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hcomp.1).symm hL2
  haveI hsimple' : IsSimpleGroup ↥L' :=
    CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2'
  obtain ⟨A, hA, hAL⟩ := hoff
  let A' : Subgroup Y := A.subgroupOf Y
  have hAmap : A'.map Y.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hAcal : A' ∈ UC22.Ext.calP ρ := mem_calP_subgroupOf hA
  have hAL' : ⁅L', A'⁆ ≠ ⊥ := by
    intro hbot
    apply hAL
    have hmap := Subgroup.map_commutator (H₁ := L') (H₂ := A') Y.subtype
    rw [hLmap, hAmap, hbot, Subgroup.map_bot] at hmap
    simpa [Subgroup.commutator_comm] using hmap.symm
  obtain ⟨B, hinv, hBA, hbest, hquad, hBU, hmov, hT, F, hFfield, hFfin, hFproj, hFdec,
    hFcard, α, hout⟩ :=
    UC22.K148.exists_componentOffenderOutput hρinj hcomp' (by omega) hL2' hAcal hAL'
  have hdich := UC22.K148.dichotomy_of_componentOffenderOutput hρinj hcomp' hL2' hAcal hAL'
    hBA hinv hT hFcard hout
  rcases hdich with ⟨hnat, -⟩ | ⟨hn2', -, -⟩
  · have hbin_aut : CFSG.Quasithin.BinaryNaturalSL
        (CFSG.Quasithin.autSub L (CFSG.Quasithin.commV L)) ⊤
        (CFSG.Quasithin.fixV (CFSG.Quasithin.autSub L (CFSG.Quasithin.commV L))) 2 n := by
      obtain ⟨K, hKfield, hKfin, hKcard, hreal⟩ :=
        CFSG.LocalAnalysis.UniquenessCase.PartTwo.natL2_realizes_autSub_commSub
          (E := W) (Q := Y) Y.subtype hnat
      rw [hLmap] at hreal
      rw [← CFSG.Quasithin.commV_eq_commSub] at hreal
      exact ⟨K, hKfield, hKfin, hKcard, hreal⟩
    have hLV : L ≤ CFSG.Quasithin.stabSub (CFSG.Quasithin.commV L) :=
      CFSG.Quasithin.le_stabSub_commV_self L
    have hLZ : L ≤ CFSG.Quasithin.stabSub
        (CFSG.Quasithin.commV L ⊓ CFSG.Quasithin.fixV L) := by
      have h := CFSG.Quasithin.B5.le_stabSub_fixV_inf_commV (G := L) (L := L)
        (fun g hg l hl => L.mul_mem (L.mul_mem hg hl) (L.inv_mem hg))
        (fun g hg => L.inv_mem hg)
      rwa [inf_comm] at h
    haveI hsimple : IsSimpleGroup ↥L :=
      CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
    have hperf : Group.IsPerfect ↥L :=
      CFSG.Quasithin.F6.isPerfect_of_isSimpleGroup
        (CFSG.ComponentClassification.HarrisLit.L415.simple_nonabelian_of_lieModel hL2).2
    have hVne : CFSG.Quasithin.commV L ≠ ⊥ := by
      intro hbot
      have hLbot : L = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Subgroup.mem_bot]
        have h : CFSG.Quasithin.commSub (⊤ : Subgroup W) L = ⊥ := by
          rwa [CFSG.Quasithin.commV_eq_commSub] at hbot
        have hle : (⊤ : Subgroup W) ≤ CFSG.Quasithin.fixV L :=
          CFSG.Quasithin.commSub_eq_bot_iff.1 h
        ext w
        exact (CFSG.Quasithin.mem_fixV.1 (hle (Subgroup.mem_top w))) x hx
      exact hAL (by simp [hLbot])
    have hfaith : L ⊓ CFSG.Quasithin.centSub (CFSG.Quasithin.commV L) = ⊥ := by
      refine CFSG.Quasithin.inf_centSub_eq_bot_of_isSimpleGroup hsimple hLV ?_
      intro hle
      have hVbot : CFSG.Quasithin.commV L = ⊥ := by
        have hle' : CFSG.Quasithin.commV L ≤ CFSG.Quasithin.fixV L := by
          intro v hv l hl
          exact (CFSG.Quasithin.mem_centSub.mp (hle hl)) v hv
        have hcomm : CFSG.Quasithin.commSub (CFSG.Quasithin.commV L) L =
            CFSG.Quasithin.commV L :=
          CFSG.Quasithin.B15P4.commSub_commV_of_perfect (Subgroup.isPerfect_iff.mp hperf)
        rw [← hcomm, CFSG.Quasithin.commSub_eq_bot_iff]
        exact hle'
      exact hVne hVbot
    have hZeq : (CFSG.Quasithin.commV L ⊓ CFSG.Quasithin.fixV L).subgroupOf
        (CFSG.Quasithin.commV L) =
        CFSG.Quasithin.fixV (CFSG.Quasithin.autSub L (CFSG.Quasithin.commV L)) := by
      apply Subgroup.map_injective (CFSG.Quasithin.commV L).subtype_injective
      rw [Subgroup.subgroupOf_map_subtype, CFSG.Quasithin.map_subtype_fixV_autSub hLV]
      simp
    have hbin : CFSG.Quasithin.BinaryNaturalSL L (CFSG.Quasithin.commV L)
        (CFSG.Quasithin.commV L ⊓ CFSG.Quasithin.fixV L) 2 n := by
      refine CFSG.Quasithin.binaryNaturalSL_of_autSub (V := CFSG.Quasithin.commV L)
        (Z := CFSG.Quasithin.commV L ⊓ CFSG.Quasithin.fixV L)
        hLV hLZ inf_le_left hfaith ?_
      rw [hZeq]
      exact hbin_aut
    have hirr : CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsIrrOn L
        (CFSG.Quasithin.commV L) (CFSG.Quasithin.commV L ⊓ CFSG.Quasithin.fixV L) := by
      refine ⟨?_, ?_, ?_, ?_⟩
      · rw [lt_iff_le_and_ne]
        refine ⟨inf_le_left, ?_⟩
        intro heq
        apply (UC22.K148.commOn_facts_of_mem_calP hρinj hcomp' hAcal hAL').2
        intro x hx
        have hx' : x.toMul ∈ CFSG.Quasithin.commV L := by
          rw [← hLmap, CFSG.Quasithin.commV_eq_commSub]
          exact (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_commOn_autRep_comp
            Y.subtype L' x).1 hx
        have hfix : x.toMul ∈ CFSG.Quasithin.fixV L := by
          have hmem : x.toMul ∈ CFSG.Quasithin.commV L ⊓ CFSG.Quasithin.fixV L := by
            rw [heq]
            exact hx'
          exact hmem.2
        exact (CFSG.RankThree.FFModules.mem_fixSub_autRep_comp Y.subtype L' x).2
          (by rwa [hLmap])
      · intro x hx u hu
        exact (hLV hx u).2 hu
      · intro x hx z hz
        exact (hLZ hx z).2 hz
      · intro J hJ hZJ hJU
        exact CFSG.Quasithin.FFC.irr_of_binaryNatural (by norm_num : 2 ≤ 2) hbin J hJ hZJ hJU
    exact ⟨hirr, hbin⟩
  · omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6
