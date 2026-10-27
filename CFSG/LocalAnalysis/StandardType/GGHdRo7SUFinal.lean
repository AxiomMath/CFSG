module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUAssembly
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallClass
import CFSG.LocalAnalysis.StandardType.GGHdRo7NoTV
import CFSG.LocalAnalysis.StandardType.GGHdRo7XDatum
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUAJ
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUClassLarge
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUGraph
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKStab
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULStab
import CFSG.LocalAnalysis.StandardType.GGHdRo7LNC
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULin
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUPCent
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUPInv
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceU
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUReduceV
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUStabCard
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallAdapt
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallAssembly
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallConj
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsA
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsBD
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsE
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallRules

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem su_labL_of_innerDiag {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L : Subgroup G}
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L) :
    GGHdRo7SULabL p L := by
  obtain ⟨lab, hlab, hhas, _, _, _, _, _, hS, _, _⟩ :=
    largeEvenMarking_exists_hasLabel hM
  obtain ⟨hp3, htag, hn, h6, hndvd⟩ := hS
  exact ⟨lab, hlab, hhas, hp3, htag, hn, h6, hndvd⟩

theorem su_lin_proved
    {p : ℕ} [Fact p.Prime] (hKG : GGReflClassLargeInput') :
    ∀ (m : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin m) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      SULinData p m V b H A → ZS.LinWeyl p H :=
  fun _m _V _ _ _b _H _A hD =>
    su_lin_of_leaves su_normalizer_holds
      (su_reduceU_of_leaves su_pInv_holds su_pCent_holds su_stabCard_holds)
      (su_reduceV_of_leaves su_pInv_holds su_pCent_holds su_stabCard_holds) su_classLarge_holds
      (Small.su_linSmall_of_concrete
        (Small.smLin_of_leaves su_normalizer_holds Small.smRules_holds Small.smClassSet_holds
          Small.smModelsBD_holds Small.smModelsA_holds Small.smModelsE_holds Small.smConj_holds))
      hKG hD

theorem ggResSUCorank2Input_proved
    (hX : GGResXDichotomyInput) (hJ : GGTBJInputR) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hKG : GGReflClassLargeInput') : GGResSUCorank2Input :=
  ggResSUCorank2Input_of_leaves hX hJ hRig hLB hKG su_normalizer_holds
    (su_reduceU_of_leaves su_pInv_holds su_pCent_holds su_stabCard_holds)
    (su_reduceV_of_leaves su_pInv_holds su_pCent_holds su_stabCard_holds) su_classLarge_holds
    (Small.su_linSmall_of_concrete
      (Small.smLin_of_leaves su_normalizer_holds Small.smRules_holds Small.smClassSet_holds
        Small.smModelsBD_holds Small.smModelsA_holds Small.smModelsE_holds Small.smConj_holds))
    su_graph_holds noTV_holds xDatumGraph_holds (su_lmodel_of_coord su_lcoord_holds hRig)
    (su_kmodel_of_coord su_kcoord_holds hRig hLB) su_kstab_holds su_aj_holds


theorem ggResSUCorank2_exact2_originalL
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .twA ∧ lab.n = 1 ∧ 6 ≤ lab.rank ∧
        ¬ 3 ∣ lab.rank + 1) p Bs L)
    (hD2 : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact2 p Bs K J L ggSelAny ggTypAny)
    (hKG : GGReflClassLargeInput') (hRig : GGLabelRigidInput) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨m, hx, τ, hp3, hm7, hm3, hτ, hcm⟩ :=
    hdRo7SULCoordAux_modelCfg (hdRo7SULCoordAux_hyp_of_resHyp hH) hRig
      (su_labL_of_innerDiag hM)
  obtain ⟨V, hV, hVp, ι, b, hxb, hAL⟩ :=
    su_linearModel_of_coord (p := p) hcm hx hτ
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S :=
    CFSG.StandardType.HdRo7LNC.lnc_of_innerDiag_su hM
  exact su_core_of_exact2 hH hp3 hD2 noTV_holds xDatumGraph_holds su_graph_holds
    (su_lin_proved hKG) ι b hx hm7 hm3 hxb hnc hAL

end CFSG.StandardType.HdRo7SU

end
