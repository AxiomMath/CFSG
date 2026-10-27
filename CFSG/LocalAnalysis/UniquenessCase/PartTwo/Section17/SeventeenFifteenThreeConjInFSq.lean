module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenSwap
public import CFSG.LocalAnalysis.WeakClosure81.CFAutAlmostSimple
public import CFSG.LocalAnalysis.WeakClosure81.InFSqComponents
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog7StdOm8Tools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.CentSectionConj
public import CFSG.GroupTheory.PCoreOfSubnormal
public import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BarImageCalC
import CFSG.GroupTheory.PGL2Basic
import CFSG.GroupTheory.PerfectCoreSup
import CFSG.GroupTheory.BarImageConj
import CFSG.Quasithin.Vol2.Ch11SecE42S2e
import CFSG.RankThree.PartTwo.Sec20.Item20Res7ProofL3Orbit
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Bar13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua
public import CFSG.Quasithin.Background.S1567BYE
public import CFSG.Quasithin.Vol2.Ch11SecE3L0
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem328Iso
public import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.WeakClosure81 CFSG.LocalCores
open CFSG.SignalizerFunctorTheorem.McBride
open CFSG.SignalizerFunctorTheorem.McBride.Near (IsChiefFactorOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_15_pCore_top_eq_bot {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (_hC : Ctx17_6 D V₀ V L r q) :
    pCoreOf 2 (⊤ : Subgroup (Bar2 (L ⊔ D.T))) = ⊥ := by
  rw [CFSG.CGT.PushingUpLit.Glue.pCoreOf_top_eq, pCore_two_bar2_eq_bot]

theorem gap17_15_orbitClosure_normal {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) :
    (orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T)).Normal :=
  orbitClosure_normal (orbitClosure_sup_of_calC hC.memL)

theorem gap17_15_centralizer_orbitClosure_le {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) :
    Subgroup.centralizer (orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) : Set (Bar2 (L ⊔ D.T))) ≤
      orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) :=
  centralizer_orbitClosure_le (gap17_15_pCore_top_eq_bot hC)
    (barImage_T_sylow_of_calC hC.memL).isPGroup (orbitClosure_sup_of_calC hC.memL)

theorem gap17_15_orbitClosure_eq_layer {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) :
    orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) =
      CFSG.layer (Bar2 (L ⊔ D.T)) :=
  le_antisymm (orbitClosure_le_layer (barImage_component_of_calC hC.memL))
    (layer_le_orbitClosure (gap17_15_pCore_top_eq_bot hC)
      (barImage_T_sylow_of_calC hC.memL).isPGroup (orbitClosure_sup_of_calC hC.memL))

theorem gap17_15_component_conj {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) {J : Subgroup (Bar2 (L ⊔ D.T))}
    (hJ : CFSG.IsComponent J) :
    ∃ t ∈ UC22.barImage (L ⊔ D.T) D.T,
      J = (UC22.barImage (L ⊔ D.T) L).map (MulAut.conj t).toMonoidHom := by
  classical
  set K : Subgroup (Bar2 (L ⊔ D.T)) := UC22.barImage (L ⊔ D.T) L with hKdef
  have hK : CFSG.IsComponent K := barImage_component_of_calC hC.memL
  have hKT : orbitClosure K (UC22.barImage (L ⊔ D.T) D.T) ⊔
      UC22.barImage (L ⊔ D.T) D.T = ⊤ := orbitClosure_sup_of_calC hC.memL
  let Tb : Subgroup (Bar2 (L ⊔ D.T)) := UC22.barImage (L ⊔ D.T) D.T
  have hTb2 : IsPGroup 2 Tb := (barImage_T_sylow_of_calC hC.memL).isPGroup
  have hO2 : pCoreOf 2 (⊤ : Subgroup (Bar2 (L ⊔ D.T))) = ⊥ :=
    gap17_15_pCore_top_eq_bot hC
  have hJle : J ≤ orbitClosure K Tb :=
    (component_le_layer hJ).trans (layer_le_orbitClosure hO2 hTb2 hKT)
  by_contra hnot
  push Not at hnot
  have hcomm : ∀ t ∈ Tb, ⁅K.map (MulAut.conj t).toMonoidHom, J⁆ = ⊥ := by
    intro t ht
    rcases distinct_components_commute hJ (isComponent_map_conjAut hK t) with h | h
    · exact absurd h (hnot t ht)
    · rwa [Subgroup.commutator_comm]
  have hFleC : orbitClosure K Tb ≤ Subgroup.centralizer (J : Set (Bar2 (L ⊔ D.T))) := by
    refine orbitClosure_le fun t ht => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (hcomm t ht)
  have hJleCF : J ≤ Subgroup.centralizer (orbitClosure K Tb :
      Set (Bar2 (L ⊔ D.T))) := by
    have h1 : ⁅J, orbitClosure K Tb⁆ = ⊥ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hFleC
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hJcenter : J ≤ (Subgroup.center ↥(orbitClosure K Tb)).map
      (orbitClosure K Tb).subtype := fun x hx =>
    (mem_map_center_iff (orbitClosure K Tb)).mpr ⟨hJle hx, hJleCF hx⟩
  have hJcomm : IsMulCommutative ↥J := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hJleCF a.2)
      (b : Bar2 (L ⊔ D.T)) (hJle b.2)).symm
  have : Nontrivial ↥J := isQuasisimple_nontrivial hJ.1
  have : Group.IsPerfect ↥J := hJ.1.1
  exact Group.IsPerfect.not_isMulCommutative J hJcomm


theorem gap17_15_center_barImage_eq_bot {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) :
    Subgroup.center ↥(UC22.barImage (L ⊔ D.T) L) = ⊥ := by
  have hHM : L ⊔ D.T ≤ D.M := sup_le hC.memL.1.le D.sylowM.le
  have hsub : CFSG.Open.IsSubnormal L (L ⊔ D.T) :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hC.memL.1 le_sup_left hHM
  obtain ⟨e, -⟩ := uc22p20d_bar2Equiv le_sup_left hsub
  obtain ⟨r', f', hr', hr2', hq', hf', hm'⟩ := h7
  obtain ⟨hsimple, hnab⟩ :=
    CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hm'
  have : IsSimpleGroup (Bar2 L) := hsimple
  have hbarZ : Subgroup.center (Bar2 L) = ⊥ :=
    CFSG.Quasithin.Vol2.Ch11.SecE3.center_eq_bot_of_simple hnab
  have hmap := Subgroup.map_center_eq e
  rw [hbarZ, Subgroup.map_bot] at hmap
  exact hmap.symm

theorem gap17_15_center_component_eq_bot {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7)
    {J : Subgroup (Bar2 (L ⊔ D.T))} (hJ : CFSG.IsComponent J) :
    Subgroup.center ↥J = ⊥ := by
  obtain ⟨t, -, rfl⟩ := gap17_15_component_conj hC hJ
  let e : ↥(UC22.barImage (L ⊔ D.T) L) ≃*
      ↥((UC22.barImage (L ⊔ D.T) L).map (MulAut.conj t).toMonoidHom) :=
    Subgroup.equivMapOfInjective _ (MulAut.conj t).toMonoidHom (MulAut.conj t).injective
  have hmap := Subgroup.map_center_eq e
  rw [gap17_15_center_barImage_eq_bot hC h7, Subgroup.map_bot] at hmap
  exact hmap.symm

theorem gap17_15_center_orbitClosure_eq_bot {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) :
    Subgroup.center ↥(orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T)) = ⊥ := by
  rw [gap17_15_orbitClosure_eq_layer hC]
  have hcenter := (layer_center (G := Bar2 (L ⊔ D.T))).1
  have hbot : (⨆ K : ComponentIndex (Bar2 (L ⊔ D.T)),
      (Subgroup.center ↥K.1).map K.1.subtype) = ⊥ := by
    refine iSup_eq_bot.mpr fun K => ?_
    rw [gap17_15_center_component_eq_bot hC h7 K.2]
    simp
  rw [hbot] at hcenter
  exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp hcenter


theorem gap17_15_inf_centralizer_orbitClosure_eq_bot {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) :
    orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) ⊓
      Subgroup.centralizer (orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) : Set (Bar2 (L ⊔ D.T))) = ⊥ := by
  refine le_bot_iff.mp ?_
  intro x hx
  have hx' : x ∈ (Subgroup.center ↥(orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T))).map
      (orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T)).subtype :=
    (mem_map_center_iff _).mpr hx
  rw [gap17_15_center_orbitClosure_eq_bot hC h7, Subgroup.map_bot] at hx'
  exact hx'

theorem gap17_15_minimalNormal_orbitClosure {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) {M : Subgroup (Bar2 (L ⊔ D.T))}
    (hM : M.Normal) (hMle : M ≤ orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T)) (hMne : M ≠ ⊥) :
    M = orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T) := by
  have hchief := isChiefFactorOf_orbitClosure (barImage_component_of_calC hC.memL)
    (orbitClosure_sup_of_calC hC.memL)
  have hZ := gap17_15_inf_centralizer_orbitClosure_eq_bot hC h7
  have hMn : CFSG.SignalizerFunctorTheorem.McBride.Near.IsNormalIn M
      (⊤ : Subgroup (Bar2 (L ⊔ D.T))) :=
    ⟨le_top, by rw [Subgroup.normalizer_eq_top_iff.mpr hM]⟩
  rcases hchief.2.2.2 M hMn (by rw [hZ]; exact bot_le) hMle with h | h
  · exact absurd (h.trans hZ) hMne
  · exact h

theorem gap17_15_orbitClosure_le_of_normal {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) {Y : Subgroup (Bar2 (L ⊔ D.T))}
    (hYn : Y.Normal) (hYne : Y ≠ ⊥) :
    orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) ≤ Y := by
  have hFn : (orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T)).Normal :=
    gap17_15_orbitClosure_normal hC
  have : (orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T)).Normal := hFn
  by_cases h : Y ⊓ orbitClosure (UC22.barImage (L ⊔ D.T) L)
      (UC22.barImage (L ⊔ D.T) D.T) = ⊥
  · have hcomm : ⁅Y, orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T)⁆ = ⊥ :=
      le_bot_iff.mp ((Subgroup.commutator_le_inf Y _).trans h.le)
    have hYleC : Y ≤ Subgroup.centralizer (orbitClosure
        (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) : Set (Bar2 (L ⊔ D.T))) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hYleF : Y ≤ orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T) :=
      hYleC.trans (gap17_15_centralizer_orbitClosure_le hC)
    have hYbot : Y ≤ ⊥ := by
      have := le_inf le_rfl hYleF
      rwa [h] at this
    exact absurd (le_bot_iff.mp hYbot) hYne
  · have hmin := gap17_15_minimalNormal_orbitClosure hC h7
      (inferInstance : (Y ⊓ orbitClosure (UC22.barImage (L ⊔ D.T) L)
        (UC22.barImage (L ⊔ D.T) D.T)).Normal)
      inf_le_right h
    calc orbitClosure (UC22.barImage (L ⊔ D.T) L)
          (UC22.barImage (L ⊔ D.T) D.T)
        = Y ⊓ orbitClosure (UC22.barImage (L ⊔ D.T) L)
            (UC22.barImage (L ⊔ D.T) D.T) := hmin.symm
      _ ≤ Y := inf_le_left


theorem gap17_15_centSection_eq_pCoreOf {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7)
    [(L.subgroupOf (L ⊔ NTL17 D L)).Normal]
    (hquot : IsPGroup 2 (↥(L ⊔ NTL17 D L) ⧸
      (L.subgroupOf (L ⊔ NTL17 D L)))) :
    centSection (L ⊔ NTL17 D L) L (pCoreOf 2 L) = pCoreOf 2 (L ⊔ NTL17 D L) := by
  classical
  set N : Subgroup G := L ⊔ NTL17 D L with hN
  have hLN : L ≤ N := le_sup_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hLq : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr hNL
  have hO2eq : pCoreOf 2 L = L ⊓ pCoreOf 2 N :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hLN hNL
  have hZ : Subgroup.center (Bar2 L) = ⊥ := by
    obtain ⟨r', f', hr', hr2', hq', hf', hm'⟩ := h7
    obtain ⟨hsimple, hnab⟩ :=
      CFSG.ComponentClassification.GSThmB.Catalog7Std.Om8.simple_of_lieModel_psl_two hm'
    have : IsSimpleGroup (Bar2 L) := hsimple
    exact CFSG.Quasithin.Vol2.Ch11.SecE3.center_eq_bot_of_simple hnab
  have hO2L_le_C : pCoreOf 2 L ≤ centSection N L (pCoreOf 2 L) := by
    intro x hx
    have hxL : x ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hx
    refine ⟨hLN hxL, Subgroup.le_normalizer hxL, Subgroup.le_normalizer hx, ?_⟩
    intro a ha
    have hmem := CFSG.Quasithin.E1.commutator_mem_pCoreOf (S := L) hx ha
    rwa [commutatorElement_def] at hmem
  have hO2N_le : pCoreOf 2 N ≤ centSection N L (pCoreOf 2 L) := by
    intro x hx
    have hxN : x ∈ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N hx
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := hNL hxN
    have hxP : x ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hxL
    refine ⟨hxN, hxL, hxP, ?_⟩
    intro a ha
    have hxa : x * a * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hxL a).mp ha
    have hmemL : x * a * x⁻¹ * a⁻¹ ∈ L := L.mul_mem hxa (L.inv_mem ha)
    have hmemPN : x * a * x⁻¹ * a⁻¹ ∈ pCoreOf 2 N := by
      have hmem := CFSG.Quasithin.E1.commutator_mem_pCoreOf (S := N) hx (hLN ha)
      rwa [commutatorElement_def] at hmem
    have : x * a * x⁻¹ * a⁻¹ ∈ L ⊓ pCoreOf 2 N := ⟨hmemL, hmemPN⟩
    rwa [← hO2eq] at this
  have hC_le_N : centSection N L (pCoreOf 2 L) ≤ N := centSection_le N L _
  have hN_norm_C : N ≤ Subgroup.normalizer (centSection N L (pCoreOf 2 L) : Set G) :=
    centSection_le_normalizer hNL
  have hC_norm_L : centSection N L (pCoreOf 2 L) ≤ Subgroup.normalizer (L : Set G) :=
    hC_le_N.trans hNL
  have hCinfL : centSection N L (pCoreOf 2 L) ⊓ L = pCoreOf 2 L := by
    refine le_antisymm ?_ (fun x hx => ⟨hO2L_le_C hx, CFSG.LieType.BorelTits.pCoreOf_le 2 L hx⟩)
    rintro x ⟨hxC, hxL⟩
    have hxcenter : (QuotientGroup.mk ⟨x, hxL⟩ : Bar2 L) ∈
        Subgroup.center (Bar2 L) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
      have hcomm : x * (l : G) * x⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L := hxC.2.2.2 l l.2
      have hxl : (x * (l : G)) ∈ L := L.mul_mem hxL l.2
      have hlx : ((l : G) * x) ∈ L := L.mul_mem l.2 hxL
      have hq : (QuotientGroup.mk ⟨x * (l : G), hxl⟩ : Bar2 L) =
          QuotientGroup.mk ⟨(l : G) * x, hlx⟩ := by
        refine QuotientGroup.eq_iff_div_mem.mpr ?_
        have hdiv : ((⟨x * (l : G), hxl⟩ : ↥L) / ⟨(l : G) * x, hlx⟩) =
            (⟨x * (l : G) * x⁻¹ * (l : G)⁻¹,
              L.mul_mem (L.mul_mem (L.mul_mem hxL l.2) (L.inv_mem hxL))
                (L.inv_mem l.2)⟩ : ↥L) := by
          ext
          simp [div_eq_mul_inv, mul_assoc]
        rw [hdiv]
        exact (CFSG.mem_openPCoreOf_iff (⟨x * (l : G) * x⁻¹ * (l : G)⁻¹,
          L.mul_mem (L.mul_mem (L.mul_mem hxL l.2) (L.inv_mem hxL))
            (L.inv_mem l.2)⟩ : ↥L)).mp (by simpa using hcomm)
      have hxl' : (⟨x, hxL⟩ * l : ↥L) = ⟨x * (l : G), hxl⟩ := rfl
      have hlx' : (l * ⟨x, hxL⟩ : ↥L) = ⟨(l : G) * x, hlx⟩ := rfl
      calc (QuotientGroup.mk l : Bar2 L) * (QuotientGroup.mk ⟨x, hxL⟩)
          = (QuotientGroup.mk (l * ⟨x, hxL⟩) : Bar2 L) :=
            (QuotientGroup.mk_mul (pCore 2 ↥L) l ⟨x, hxL⟩).symm
        _ = (QuotientGroup.mk ⟨(l : G) * x, hlx⟩ : Bar2 L) := by rw [hlx']
        _ = (QuotientGroup.mk ⟨x * (l : G), hxl⟩ : Bar2 L) := hq.symm
        _ = (QuotientGroup.mk (⟨x, hxL⟩ * l) : Bar2 L) := by rw [hxl']
        _ = (QuotientGroup.mk ⟨x, hxL⟩) * (QuotientGroup.mk l) :=
            QuotientGroup.mk_mul (pCore 2 ↥L) ⟨x, hxL⟩ l
    rw [hZ] at hxcenter
    have hx1 : (QuotientGroup.mk ⟨x, hxL⟩ : Bar2 L) = 1 := Subgroup.mem_bot.mp hxcenter
    exact (CFSG.mem_openPCoreOf_iff (⟨x, hxL⟩ : ↥L)).mpr
      ((QuotientGroup.eq_one_iff (⟨x, hxL⟩ : ↥L)).mp hx1)
  have hkerNormal : ((centSection N L (pCoreOf 2 L) ⊓ L).subgroupOf
      (centSection N L (pCoreOf 2 L))).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr ?_
    intro x hx
    refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
    · intro hy
      exact ⟨(centSection N L (pCoreOf 2 L)).mul_mem
          ((centSection N L (pCoreOf 2 L)).mul_mem hx hy.1)
          ((centSection N L (pCoreOf 2 L)).inv_mem hx),
        (Subgroup.mem_normalizer_iff.mp (hC_norm_L hx) y).mp hy.2⟩
    · intro hy
      have hxinv : x⁻¹ ∈ centSection N L (pCoreOf 2 L) :=
        (centSection N L (pCoreOf 2 L)).inv_mem hx
      have hC' : x⁻¹ * (x * y * x⁻¹) * x ∈ centSection N L (pCoreOf 2 L) :=
        (centSection N L (pCoreOf 2 L)).mul_mem
          ((centSection N L (pCoreOf 2 L)).mul_mem hxinv hy.1) hx
      have hxinvN : (x⁻¹ : G) ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.inv_mem _ (hC_norm_L hx)
      have hL' : x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp hxinvN (x * y * x⁻¹)).mp hy.2
      have hL'' : x⁻¹ * (x * y * x⁻¹) * x ∈ L := by
        simpa only [inv_inv] using hL'
      exact ⟨by simpa [mul_assoc] using hC', by simpa [mul_assoc] using hL''⟩
  have hNgroup : IsPGroup 2 ↥((centSection N L (pCoreOf 2 L) ⊓ L).subgroupOf
      (centSection N L (pCoreOf 2 L))) := by
    have e : ↥((centSection N L (pCoreOf 2 L) ⊓ L).subgroupOf
        (centSection N L (pCoreOf 2 L))) ≃* ↥(pCoreOf 2 L) :=
      (Subgroup.subgroupOfEquivOfLe inf_le_left).trans (MulEquiv.subgroupCongr hCinfL)
    exact (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 L).of_equiv e.symm
  let ψ : ↥(centSection N L (pCoreOf 2 L)) →*
      (↥N ⧸ (L.subgroupOf N)) :=
    (QuotientGroup.mk' (L.subgroupOf N)).comp
      (Subgroup.inclusion hC_le_N)
  have hkerψ : ψ.ker = (centSection N L (pCoreOf 2 L) ⊓ L).subgroupOf
      (centSection N L (pCoreOf 2 L)) := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      refine Subgroup.mem_subgroupOf.mpr ⟨x.2, ?_⟩
      have hq : (QuotientGroup.mk' (L.subgroupOf N)) (Subgroup.inclusion hC_le_N x) = 1 := hx
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (Subgroup.inclusion hC_le_N x)).mp hq)
    · intro hx
      rw [MonoidHom.mem_ker]
      have hxL : ((x : ↥(centSection N L (pCoreOf 2 L))) : G) ∈ L :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).2
      exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hxL)
  have hQgroup : IsPGroup 2 (↥(centSection N L (pCoreOf 2 L)) ⧸
      (centSection N L (pCoreOf 2 L) ⊓ L).subgroupOf
        (centSection N L (pCoreOf 2 L))) := by
    have htop : IsPGroup 2 (⊤ : Subgroup (↥N ⧸ (L.subgroupOf N))) :=
      hquot.of_equiv (Subgroup.topEquiv (G := ↥N ⧸ (L.subgroupOf N))).symm
    have hrange : IsPGroup 2 ↥ψ.range := htop.to_le le_top
    have h := hrange.of_equiv (QuotientGroup.quotientKerEquivRange ψ).symm
    let e := QuotientGroup.quotientMulEquivOfEq hkerψ.symm
    exact h.of_equiv e.symm
  have hC2 : IsPGroup 2 ↥(centSection N L (pCoreOf 2 L)) :=
    IsPGroup.of_subgroup_of_quotient hNgroup hQgroup
  refine le_antisymm ?_ hO2N_le
  exact CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hC_le_N
    (fun x hx y hy => (Subgroup.mem_normalizer_iff.mp (hN_norm_C hx) y).mp hy) hC2

theorem gap17_15_barImage_NTL {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) :
    UC22.barImage (L ⊔ D.T) (NTL17 D L) =
      UC22.barImage (L ⊔ D.T) D.T ⊓
        Subgroup.normalizer (UC22.barImage (L ⊔ D.T) L :
          Set (Bar2 (L ⊔ D.T))) := by
  classical
  set H : Subgroup G := L ⊔ D.T with hH
  set S : Subgroup G := NTL17 D L with hS
  have hLH : L ≤ H := le_sup_left
  have hSH : S ≤ H := fun x hx => Subgroup.mem_sup_right (hx.1)
  have hHM : H ≤ D.M := sup_le hC.memL.1.le D.sylowM.le
  have hsubL : CFSG.Open.IsSubnormal L H :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hC.memL.1 le_sup_left hHM
  have hperfL : ⁅L, L⁆ = L := hC.memL.2.1
  ext y
  constructor
  · intro hy
    obtain ⟨s, hs, hsy⟩ := Subgroup.mem_map.mp hy
    have hsG : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have hsT : (s : G) ∈ D.T := hsG.1
    have hsN : (s : G) ∈ Subgroup.normalizer (L : Set G) := hsG.2
    have hsH : (s : G) ∈ H := hSH hsG
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [← hsy]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hsT)
    · rw [← hsy]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      have hconj : L.map (MulAut.conj (s : G)).toMonoidHom = L :=
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp hsN
      have hmap : (UC22.barImage H L).map (MulAut.conj
          (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨(s : G), hsH⟩)).toMonoidHom =
          UC22.barImage H (L.map (MulAut.conj (s : G)).toMonoidHom) :=
        (CFSG.GroupTheory.barImage_map_conj H L hLH hsH).symm
      have hsval : (⟨(s : G), hsH⟩ : ↥H) = s := Subtype.ext rfl
      have hmap' : (UC22.barImage H L).map
          (↑(MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) s))) =
          UC22.barImage H (L.map (MulAut.conj (s : G)).toMonoidHom) := by
        simpa [hsval] using hmap
      rw [hmap', hconj]
  · intro hy
    obtain ⟨hyT, hyN⟩ := Subgroup.mem_inf.mp hy
    obtain ⟨t, ht, hty⟩ := Subgroup.mem_map.mp hyT
    have htG : (t : G) ∈ D.T := Subgroup.mem_subgroupOf.mp ht
    have htH : (t : G) ∈ H := Subgroup.mem_sup_right htG
    have hqnorm : QuotientGroup.mk' (CFSG.pCore 2 ↥H) t ∈
        Subgroup.normalizer (UC22.barImage H L : Set (Bar2 H)) := hty ▸ hyN
    have hmap : (UC22.barImage H L).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H) t)).toMonoidHom =
        UC22.barImage H L :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp hqnorm
    have hmap' : (UC22.barImage H L).map
        (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥H)
          (⟨(t : G), htH⟩ : ↥H))).toMonoidHom =
        UC22.barImage H (L.map (MulAut.conj (t : G)).toMonoidHom) :=
      (CFSG.GroupTheory.barImage_map_conj H L hLH htH).symm
    have hImg : UC22.barImage H (L.map (MulAut.conj (t : G)).toMonoidHom) =
        UC22.barImage H L := by
      rw [← hmap']
      simpa using hmap
    let P : Subgroup G := L.map (MulAut.conj (t : G)).toMonoidHom
    have hPH : P ≤ H := by
      intro x hx
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
      exact H.mul_mem (H.mul_mem htH (hLH hl)) (H.inv_mem htH)
    have hHmap : H.map (MulAut.conj (t : G)).toMonoidHom = H :=
      (Subgroup.mem_normalizer_iff_map_conj_eq).mp
        (Subgroup.le_normalizer (H := H) htH)
    have hsubP : CFSG.Open.IsSubnormal P H := by
      have h := hsubL.map (MulAut.conj (t : G)).toMonoidHom
      rwa [hHmap] at h
    have hperfP : ⁅P, P⁆ = P := by
      have h := congrArg (Subgroup.map (MulAut.conj (t : G)).toMonoidHom) hperfL
      rwa [Subgroup.map_commutator] at h
    have hsup : P ⊔ pCoreOf 2 H = L ⊔ pCoreOf 2 H := by
      refine CFSG.RankThree.PartTwo.Sec20.Res7.eq_of_img_eq le_sup_right
        (sup_le hPH (CFSG.LieType.BorelTits.pCoreOf_le 2 H)) le_sup_right
        (sup_le hLH (CFSG.LieType.BorelTits.pCoreOf_le 2 H)) ?_
      change UC22.barImage H (P ⊔ pCoreOf 2 H) = UC22.barImage H (L ⊔ pCoreOf 2 H)
      rw [s13_barImage_sup hPH (CFSG.LieType.BorelTits.pCoreOf_le 2 H),
        s13_barImage_sup hLH (CFSG.LieType.BorelTits.pCoreOf_le 2 H),
        uc22p22u_barImage_pCore]
      simpa only [P, sup_bot_eq] using hImg
    have hPL : P = L := by
      calc P = CFSG.Quasithin.perfectCore (P ⊔ pCoreOf 2 H) :=
            (CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq hPH hsubP hperfP).symm
        _ = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 H) := by rw [hsup]
        _ = L := CFSG.GroupTheory.perfectCore_sup_pCoreOf_eq hLH hsubL hperfL
    have htS : (t : G) ∈ S :=
      ⟨htG, (Subgroup.mem_normalizer_iff_map_conj_eq).mpr hPL⟩
    exact Subgroup.mem_map.mpr ⟨t, Subgroup.mem_subgroupOf.mpr htS, hty⟩

theorem gap17_15_hquot {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) [(L.subgroupOf (L ⊔ NTL17 D L)).Normal] :
    IsPGroup 2 (↥(L ⊔ NTL17 D L) ⧸
      (L.subgroupOf (L ⊔ NTL17 D L))) := by
  classical
  set N : Subgroup G := L ⊔ NTL17 D L with hN
  set S : Subgroup G := NTL17 D L with hS
  have hLN : L ≤ N := le_sup_left
  have hSN : S ≤ N := le_sup_right
  have hLq : (L.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLN).mpr
      (sup_le Subgroup.le_normalizer inf_le_right)
  let Sq : Subgroup ↥N := S.subgroupOf N
  have hSq2 : IsPGroup 2 ↥Sq :=
    (D.sylowM.isPGroup.to_le inf_le_left).of_equiv
      (Subgroup.subgroupOfEquivOfLe hSN).symm
  have hsup : L.subgroupOf N ⊔ Sq = ⊤ := by
    change L.subgroupOf N ⊔ S.subgroupOf N = ⊤
    rw [← Subgroup.subgroupOf_sup hLN hSN, hN.symm,
      Subgroup.subgroupOf_self]
  let f : ↥Sq →* (↥N ⧸ (L.subgroupOf N)) :=
    (QuotientGroup.mk' (L.subgroupOf N)).comp Sq.subtype
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx : x ∈ L.subgroupOf N ⊔ Sq := by rw [hsup]; exact Subgroup.mem_top x
    obtain ⟨l, hl, s, hs, hls⟩ := Subgroup.mem_sup_of_normal_left.mp hx
    refine ⟨⟨s, hs⟩, ?_⟩
    show (QuotientGroup.mk' (L.subgroupOf N)) s =
      (QuotientGroup.mk' (L.subgroupOf N)) x
    rw [← hls, map_mul]
    have hl1 : (QuotientGroup.mk' (L.subgroupOf N)) l = 1 :=
      (QuotientGroup.eq_one_iff l).mpr hl
    rw [hl1, one_mul]
  exact IsPGroup.of_surjective hSq2 f hf

theorem gap17_15_barImage_pCoreOf_le_autC {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) :
    UC22.barImage (L ⊔ D.T) (pCoreOf 2 (L ⊔ NTL17 D L)) ≤
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L) := by
  classical
  set H : Subgroup G := L ⊔ D.T with hH
  set S : Subgroup G := NTL17 D L with hS
  set N : Subgroup G := L ⊔ S with hN
  set K : Subgroup (Bar2 H) := UC22.barImage H L with hK
  set Tb : Subgroup (Bar2 H) := UC22.barImage H D.T with hTb
  set A : Subgroup (Bar2 H) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL Tb K with hAdef
  have hNH : N ≤ H := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hLN : L ≤ N := le_sup_left
  have hSN : S ≤ N := le_sup_right
  have hNL : N ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hLM : L ≤ D.M := hC.memL.1.le
  have hHM : H ≤ D.M := sup_le hLM D.sylowM.le
  have hsub : CFSG.Open.IsSubnormal L H :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hC.memL.1 le_sup_left hHM
  have hO2LH : pCoreOf 2 L ≤ pCoreOf 2 H := by
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsub]
    exact inf_le_right
  have hO2eq : pCoreOf 2 L = L ⊓ pCoreOf 2 N :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hLN hNL
  have hA' : UC22.barImage (L ⊔ D.T) (L ⊔ NTL17 D L) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L) := by
    rw [s13_barImage_sup (M := L ⊔ D.T) (A := L) (B := NTL17 D L)
      (le_sup_left : L ≤ L ⊔ D.T)
      (inf_le_left.trans le_sup_right : NTL17 D L ≤ L ⊔ D.T),
      gap17_15_barImage_NTL hC]
    exact sup_comm ..
  have hA : UC22.barImage H N = A := by
    change UC22.barImage (L ⊔ D.T) (L ⊔ NTL17 D L) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L)
    exact hA'
  intro x hx
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hx
  have hnO : (n : G) ∈ pCoreOf 2 N := Subgroup.mem_subgroupOf.mp hn
  have hnN : (n : G) ∈ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N hnO
  have hxA : x ∈ A := by
    rw [← hA]
    exact Subgroup.mem_map.mpr ⟨n, Subgroup.mem_subgroupOf.mpr hnN, hnx⟩
  refine Subgroup.mem_inf.mpr ⟨hxA, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.mp hk
  have hlG : (l : G) ∈ L := Subgroup.mem_subgroupOf.mp hl
  have hcommL : (n : G) * (l : G) * (n : G)⁻¹ * (l : G)⁻¹ ∈ pCoreOf 2 L := by
    have hmem := CFSG.Quasithin.E1.commutator_mem_pCoreOf (S := N) hnO (hLN hlG)
    rw [commutatorElement_def] at hmem
    have hmemL : (n : G) * (l : G) * (n : G)⁻¹ * (l : G)⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNL hnN) (l : G)).mp hlG)
        (L.inv_mem hlG)
    rw [hO2eq]
    exact ⟨hmemL, hmem⟩
  have hnl : ((n : G) * (l : G)) ∈ H := H.mul_mem (hNH hnN) ((le_sup_left : L ≤ H) hlG)
  have hln : ((l : G) * (n : G)) ∈ H := H.mul_mem ((le_sup_left : L ≤ H) hlG) (hNH hnN)
  have hq : (QuotientGroup.mk (⟨(n : G) * (l : G), hnl⟩ : ↥H) : Bar2 H) =
      QuotientGroup.mk ⟨(l : G) * (n : G), hln⟩ := by
    refine QuotientGroup.eq_iff_div_mem.mpr ?_
    have hdiv : ((⟨(n : G) * (l : G), hnl⟩ : ↥H) /
        ⟨(l : G) * (n : G), hln⟩) =
        (⟨(n : G) * (l : G) * (n : G)⁻¹ * (l : G)⁻¹, H.mul_mem (H.mul_mem
          (H.mul_mem (hNH hnN) ((le_sup_left : L ≤ H) hlG)) (H.inv_mem (hNH hnN)))
          (H.inv_mem ((le_sup_left : L ≤ H) hlG))⟩ : ↥H) := by
      ext
      simp [div_eq_mul_inv, mul_assoc]
    rw [hdiv]
    exact (CFSG.mem_openPCoreOf_iff _).mp (hO2LH hcommL)
  rw [← hlk, ← hnx]
  calc (QuotientGroup.mk l : Bar2 H) * (QuotientGroup.mk n)
      = (QuotientGroup.mk (l * n) : Bar2 H) :=
        (QuotientGroup.mk_mul (CFSG.pCore 2 ↥H) l n).symm
    _ = (QuotientGroup.mk (⟨(l : G) * (n : G), hln⟩ : ↥H) : Bar2 H) := rfl
    _ = (QuotientGroup.mk ⟨(n : G) * (l : G), hnl⟩ : Bar2 H) := hq.symm
    _ = (QuotientGroup.mk (n * l) : Bar2 H) := rfl
    _ = (QuotientGroup.mk n) * (QuotientGroup.mk l) :=
        QuotientGroup.mk_mul (CFSG.pCore 2 ↥H) n l

theorem gap17_15_autC_le_barImage_pCoreOf {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L) ≤
      UC22.barImage (L ⊔ D.T) (pCoreOf 2 (L ⊔ NTL17 D L)) := by
  classical
  set H : Subgroup G := L ⊔ D.T with hH
  set S : Subgroup G := NTL17 D L with hS
  set N : Subgroup G := L ⊔ S with hN
  set K : Subgroup (Bar2 H) := UC22.barImage H L with hK
  set Tb : Subgroup (Bar2 H) := UC22.barImage H D.T with hTb
  set A : Subgroup (Bar2 H) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL Tb K with hAdef
  have hNH : N ≤ H := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hLN : L ≤ N := le_sup_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hLM : L ≤ D.M := hC.memL.1.le
  have hHM : H ≤ D.M := sup_le hLM D.sylowM.le
  have hsub : CFSG.Open.IsSubnormal L H :=
    CFSG.Quasithin.A3.subnormal_of_le_of_le hC.memL.1 le_sup_left hHM
  have hO2LH : pCoreOf 2 L ≤ pCoreOf 2 H := by
    rw [CFSG.pCoreOf_eq_inf_pCoreOf_of_isSubnormal hsub]
    exact inf_le_right
  have hO2eq : pCoreOf 2 L = L ⊓ pCoreOf 2 N :=
    CFSG.Quasithin.S1567.pCoreOf_eq_inf_pCoreOf_of_normal hLN hNL
  have hA' : UC22.barImage (L ⊔ D.T) (L ⊔ NTL17 D L) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L) := by
    rw [s13_barImage_sup (M := L ⊔ D.T) (A := L) (B := NTL17 D L)
      (le_sup_left : L ≤ L ⊔ D.T)
      (inf_le_left.trans le_sup_right : NTL17 D L ≤ L ⊔ D.T),
      gap17_15_barImage_NTL hC]
    exact sup_comm ..
  have hA : UC22.barImage H N = A := by
    change UC22.barImage (L ⊔ D.T) (L ⊔ NTL17 D L) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L)
    exact hA'
  have hLq' : (L.subgroupOf (L ⊔ NTL17 D L)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_left : L ≤ L ⊔ NTL17 D L)).mpr
      (sup_le Subgroup.le_normalizer inf_le_right)
  have hquot := gap17_15_hquot (D := D) (V₀ := V₀) (V := V) (L := L) (r := r) (q := q) hC
  have hcent := gap17_15_centSection_eq_pCoreOf (D := D) (V₀ := V₀) (V := V) (L := L)
    (r := r) (q := q) hC h7 hquot
  intro x hx
  have hxA : x ∈ A := hx.1
  have hxC : x ∈ Subgroup.centralizer (K : Set (Bar2 H)) := hx.2
  rw [← hA] at hxA
  obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxA
  have hnN : (n : G) ∈ N := Subgroup.mem_subgroupOf.mp hn
  have hnCent : (n : G) ∈ centSection N L (pCoreOf 2 L) := by
    refine ⟨hnN, hNL hnN,
      CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L (hNL hnN), ?_⟩
    intro l hl
    have hlH : (l : G) ∈ H := hNH (hLN hl)
    have hmemK : (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : Bar2 H) ∈ K := by
      rw [hK]
      exact Subgroup.mem_map.mpr ⟨⟨l, hlH⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
    have hcommq : (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : Bar2 H) * x =
        x * (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : Bar2 H) :=
      Subgroup.mem_centralizer_iff.mp hxC _ hmemK
    have hnl : ((n : G) * l) ∈ H := H.mul_mem (hNH hnN) hlH
    have hln : (l * (n : G)) ∈ H := H.mul_mem hlH (hNH hnN)
    have hsame : (QuotientGroup.mk (⟨l * (n : G), hln⟩ : ↥H) : Bar2 H) =
        QuotientGroup.mk ⟨(n : G) * l, hnl⟩ := by
      calc (QuotientGroup.mk (⟨l * (n : G), hln⟩ : ↥H) : Bar2 H)
          = (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : Bar2 H) *
              (QuotientGroup.mk n : Bar2 H) :=
            (QuotientGroup.mk_mul (CFSG.pCore 2 ↥H) ⟨l, hlH⟩
              ⟨(n : G), hNH hnN⟩).symm.trans rfl
        _ = (QuotientGroup.mk n : Bar2 H) *
              (QuotientGroup.mk (⟨l, hlH⟩ : ↥H) : Bar2 H) := by
            rw [← hnx] at hcommq
            exact hcommq
        _ = (QuotientGroup.mk ⟨(n : G) * l, hnl⟩ : Bar2 H) :=
            (QuotientGroup.mk_mul (CFSG.pCore 2 ↥H) ⟨(n : G), hNH hnN⟩
              ⟨l, hlH⟩).symm.trans rfl
    have hmemH : l * (n : G) * l⁻¹ * (n : G)⁻¹ ∈ pCoreOf 2 H := by
      have hqdiv := QuotientGroup.eq_iff_div_mem.mp hsame
      have hdiv : ((⟨l * (n : G), hln⟩ : ↥H) / ⟨(n : G) * l, hnl⟩) =
          (⟨l * (n : G) * l⁻¹ * (n : G)⁻¹, H.mul_mem (H.mul_mem
            (H.mul_mem hlH (hNH hnN)) (H.inv_mem hlH)) (H.inv_mem (hNH hnN))⟩ : ↥H) := by
        ext
        simp [div_eq_mul_inv, mul_assoc]
      rw [hdiv] at hqdiv
      exact (CFSG.mem_openPCoreOf_iff (⟨l * (n : G) * l⁻¹ * (n : G)⁻¹,
        H.mul_mem (H.mul_mem (H.mul_mem hlH (hNH hnN)) (H.inv_mem hlH))
          (H.inv_mem (hNH hnN))⟩ : ↥H)).mpr (by simpa using hqdiv)
    have hmemH' : (n : G) * l * (n : G)⁻¹ * l⁻¹ ∈ pCoreOf 2 H := by
      have heq : (n : G) * l * (n : G)⁻¹ * l⁻¹ =
          (l * (n : G) * l⁻¹ * (n : G)⁻¹)⁻¹ := by group
      rw [heq]
      exact (pCoreOf 2 H).inv_mem hmemH
    have hmemL : (n : G) * l * (n : G)⁻¹ * l⁻¹ ∈ L :=
      L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNL hnN) l).mp hl) (L.inv_mem hl)
    have hmemN : (n : G) * l * (n : G)⁻¹ * l⁻¹ ∈ N :=
      N.mul_mem (N.mul_mem (N.mul_mem hnN (hLN hl)) (N.inv_mem hnN))
        (N.inv_mem (hLN hl))
    have hmemPN : (n : G) * l * (n : G)⁻¹ * l⁻¹ ∈ pCoreOf 2 N :=
      CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hNH ⟨hmemN, hmemH'⟩
    rw [hO2eq]
    exact ⟨hmemL, hmemPN⟩
  have hnO : (n : G) ∈ pCoreOf 2 N := by
    rw [← hcent]
    exact hnCent
  exact Subgroup.mem_map.mpr ⟨⟨(n : G), hNH hnN⟩,
    Subgroup.mem_subgroupOf.mpr hnO, hnx⟩

theorem gap17_15_barImage_pCoreOf_eq_autC {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) :
    UC22.barImage (L ⊔ D.T) (pCoreOf 2 (L ⊔ NTL17 D L)) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L) :=
  le_antisymm (gap17_15_barImage_pCoreOf_le_autC hC h7)
    (gap17_15_autC_le_barImage_pCoreOf hC h7)

theorem gap17_15_autQuot_mulEquiv {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7) :
    Nonempty (↥(CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L)) ⧸
      (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L)).subgroupOf
        (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
          (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L)) ≃*
      Bar2 (L ⊔ NTL17 D L)) := by
  classical
  set H : Subgroup G := L ⊔ D.T with hH
  set S : Subgroup G := NTL17 D L with hS
  set N : Subgroup G := L ⊔ S with hN
  set K : Subgroup (Bar2 H) := UC22.barImage H L with hK
  set Tb : Subgroup (Bar2 H) := UC22.barImage H D.T with hTb
  set A : Subgroup (Bar2 H) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL Tb K with hAdef
  set C : Subgroup (Bar2 H) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC Tb K with hCdef
  have hNH : N ≤ H := sup_le le_sup_left (inf_le_left.trans le_sup_right)
  have hLN : L ≤ N := le_sup_left
  have hNL : N ≤ Subgroup.normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer inf_le_right
  have hA' : UC22.barImage (L ⊔ D.T) (L ⊔ NTL17 D L) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L) := by
    rw [s13_barImage_sup (M := L ⊔ D.T) (A := L) (B := NTL17 D L)
      (le_sup_left : L ≤ L ⊔ D.T)
      (inf_le_left.trans le_sup_right : NTL17 D L ≤ L ⊔ D.T),
      gap17_15_barImage_NTL hC]
    exact sup_comm ..
  have hA : UC22.barImage H N = A := by
    change UC22.barImage (L ⊔ D.T) (L ⊔ NTL17 D L) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L)
    exact hA'
  have hCeq : UC22.barImage H (pCoreOf 2 N) = C := by
    change UC22.barImage (L ⊔ D.T) (pCoreOf 2 (L ⊔ NTL17 D L)) =
      CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC
        (UC22.barImage (L ⊔ D.T) D.T) (UC22.barImage (L ⊔ D.T) L)
    exact gap17_15_barImage_pCoreOf_eq_autC hC h7
  let π : ↥N →* Bar2 H :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hNH)
  have hπrange : π.range = A := by
    change ((QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp
      (Subgroup.inclusion hNH)).range = A
    rw [MonoidHom.range_comp, Subgroup.inclusion_range, ← hA]
    rfl
  let πA : ↥N →* ↥A := π.codRestrict A (fun x => by
    have hx : π x ∈ UC22.barImage H N :=
      Subgroup.mem_map.mpr ⟨⟨x, hNH x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩
    rwa [hA] at hx)
  have hπAsurj : Function.Surjective πA := by
    intro a
    have ha : (a : Bar2 H) ∈ π.range := by rw [hπrange]; exact a.2
    obtain ⟨x, hx⟩ := ha
    exact ⟨x, Subtype.ext hx⟩
  let φ : ↥N →* (↥A ⧸ C.subgroupOf A) :=
    (QuotientGroup.mk' (C.subgroupOf A)).comp πA
  have hφsurj : Function.Surjective φ := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective (C.subgroupOf A) y
    obtain ⟨x, rfl⟩ := hπAsurj a
    exact ⟨x, rfl⟩
  have hπker : π.ker = (pCoreOf 2 H).subgroupOf N := by
    ext x
    exact (CFSG.Quasithin.Vol2.Ch11.SecE.mem_ker_modO2_iff hNH x).trans
      Subgroup.mem_subgroupOf.symm
  have hNcap : N ⊓ pCoreOf 2 H ≤ pCoreOf 2 N :=
    CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hNH
  have hφker : φ.ker = (pCoreOf 2 N).subgroupOf N := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hxsub : ((πA x : ↥A) : Bar2 H) ∈ C :=
        Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff (πA x)).mp hx)
      have hxC : π x ∈ C := hxsub
      rw [← hCeq] at hxC
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.mp hxC
      have hnO : (n : G) ∈ pCoreOf 2 N := Subgroup.mem_subgroupOf.mp hn
      let nN : ↥N := ⟨(n : G), CFSG.LieType.BorelTits.pCoreOf_le 2 N hnO⟩
      have hxn : x * nN⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have hnx' : π nN = π x := by
          have hnn : (Subgroup.inclusion hNH nN : ↥H) = n := Subtype.ext rfl
          rw [show π nN = QuotientGroup.mk (Subgroup.inclusion hNH nN) from rfl, hnn]
          exact hnx
        rw [hnx', mul_inv_cancel]
      rw [hπker] at hxn
      have hxnH : ((x : G) * (n : G)⁻¹) ∈ N ⊓ pCoreOf 2 H :=
        ⟨N.mul_mem x.2 (N.inv_mem (CFSG.LieType.BorelTits.pCoreOf_le 2 N hnO)),
          Subgroup.mem_subgroupOf.mp hxn⟩
      have hxnO : ((x : G) * (n : G)⁻¹) ∈ pCoreOf 2 N := hNcap hxnH
      have hxO : (x : G) ∈ pCoreOf 2 N := by
        have heq : (x : G) = ((x : G) * (n : G)⁻¹) * (n : G) := by group
        rw [heq]
        exact (pCoreOf 2 N).mul_mem hxnO hnO
      exact Subgroup.mem_subgroupOf.mpr hxO
    · intro hx
      rw [MonoidHom.mem_ker]
      have hxO : (x : G) ∈ pCoreOf 2 N := Subgroup.mem_subgroupOf.mp hx
      have hxC : π x ∈ C := by
        rw [← hCeq]
        exact Subgroup.mem_map.mpr ⟨⟨x, hNH x.2⟩, Subgroup.mem_subgroupOf.mpr hxO, rfl⟩
      have hxC' : ((πA x : ↥A) : Bar2 H) ∈ C := hxC
      exact (QuotientGroup.eq_one_iff (πA x)).mpr
        (Subgroup.mem_subgroupOf.mpr hxC')
  let e1 : (↥N ⧸ φ.ker) ≃* (↥A ⧸ C.subgroupOf A) :=
    QuotientGroup.quotientKerEquivOfSurjective φ hφsurj
  let e2 : (↥N ⧸ φ.ker) ≃* Bar2 N :=
    QuotientGroup.quotientMulEquivOfEq (by
      rw [hφker, CFSG.openPCoreOf_subgroupOf])
  exact ⟨e1.symm.trans e2⟩

theorem gap17_15_cfAutPGL2_Tbar {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7)
    (hPGL : CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L))) :
    WeakClosure81.CFAutInFGroupPGL2 (Bar2 (L ⊔ D.T))
      (UC22.barImage (L ⊔ D.T) D.T) := by
  classical
  set H : Subgroup G := L ⊔ D.T with hH
  set K : Subgroup (Bar2 H) := UC22.barImage H L with hK
  set Tb : Subgroup (Bar2 H) := UC22.barImage H D.T with hTb
  set F : Subgroup (Bar2 H) := orbitClosure K Tb with hF
  have hFnormal : F.Normal := gap17_15_orbitClosure_normal hC
  have hFne : F ≠ ⊥ := by
    have hKle : K ≤ F := le_orbitClosure K Tb
    have hKne : K ≠ ⊥ := by
      intro hbot
      have : Nontrivial ↥K := isQuasisimple_nontrivial (barImage_component_of_calC hC.memL).1
      exact (Subgroup.nontrivial_iff_ne_bot K).mp inferInstance hbot
    intro hbot
    exact hKne (le_bot_iff.mp (hKle.trans (le_of_eq hbot)))
  have hbase : CFSG.Quasithin.F6.IsPGL2 7
      (↥(CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL Tb K) ⧸
        (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC Tb K).subgroupOf
          (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL Tb K)) := by
    obtain ⟨e⟩ := gap17_15_autQuot_mulEquiv (D := D) (V₀ := V₀) (V := V) (L := L)
      (r := r) (q := q) hC h7
    exact (by simpa [hH, hK, hTb] using CFSG.GroupTheory.isPGL2_of_mulEquiv e hPGL)
  intro X hXn hXne hXmin hXnc L' hL'
  have hFleX : F ≤ X := gap17_15_orbitClosure_le_of_normal hC h7 hXn hXne
  have hXleF : X ≤ F := by
    by_contra hnot
    have hbot : X ⊓ F = ⊥ := by
      rcases hXmin (X ⊓ F) (inferInstance : (X ⊓ F).Normal) inf_le_left with h | h
      · exact h
      · exact absurd (h ▸ inf_le_right : X ≤ F) hnot
    have hFX : F ≤ X ⊓ F := le_inf hFleX le_rfl
    exact hFne (le_bot_iff.mp (hbot ▸ hFX))
  have hXeq : X = F := le_antisymm hXleF hFleX
  have hL'F : CFSG.Open.IsComponentOf L' F := hXeq ▸ hL'
  have hL'subOpen : CFSG.Open.IsSubnormal L' (⊤ : Subgroup (Bar2 H)) :=
    CFSG.Open.IsSubnormal.trans hL'F.2.1
      (CFSG.Open.IsSubnormal.of_mathlib (Subgroup.Normal.isSubnormal hFnormal))
  have hL'compQ : CFSG.IsComponent L' :=
    ⟨CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr hL'F.2.2,
      CFSG.Quasithin.A3.subnormal_top_iff.mp hL'subOpen⟩
  obtain ⟨t, ht, hL't⟩ := gap17_15_component_conj hC hL'compQ
  have hTbmap : Tb.map (MulAut.conj t).toMonoidHom = Tb :=
    (Subgroup.mem_normalizer_iff_map_conj_eq).mp (Subgroup.le_normalizer ht)
  have hPGL' : CFSG.Quasithin.F6.IsPGL2 7
      (↥(CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL Tb L') ⧸
        (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC Tb L').subgroupOf
          (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL Tb L')) := by
    classical
    let econj := Classical.choice
      (CFSG.LocalAnalysis.WeakClosure81.fourFive_autQuot_equiv (MulAut.conj t) Tb K)
    have h := CFSG.GroupTheory.isPGL2_of_mulEquiv econj.symm hbase
    rw [hTbmap] at h
    rw [← hL't] at h
    exact h
  exact ⟨CFSG.LocalAnalysis.WeakClosure81.fourFive_normal_autC Tb L', hPGL'⟩

theorem gap17_15_cfAutPGL2_sylow {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ}
    (hC : Ctx17_6 D V₀ V L r q) (h7 : IsL2Over17 (Bar2 L) 7)
    (hPGL : CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L)))
    {T' : Subgroup (Bar2 (L ⊔ D.T))} (hT' : IsSylowIn 2 T' ⊤) :
    WeakClosure81.CFAutInFGroupPGL2 (Bar2 (L ⊔ D.T)) T' := by
  classical
  have hTb : IsSylowIn 2 (UC22.barImage (L ⊔ D.T) D.T) ⊤ :=
    barImage_T_sylow_of_calC hC.memL
  obtain ⟨g, -, hg⟩ := CFSG.Quasithin.Ch1Sec3.exists_conj_of_isSylowIn hTb hT'
  have hmap : (UC22.barImage (L ⊔ D.T) D.T).map (MulAut.conj g).toMonoidHom = T' := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hg (g * y * g⁻¹)).mpr (by
        have h : g⁻¹ * (g * y * g⁻¹) * g = y := by group
        rwa [h])
    · intro hx
      have hy : g⁻¹ * x * g ∈ UC22.barImage (L ⊔ D.T) D.T := (hg x).mp hx
      refine ⟨g⁻¹ * x * g, hy, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  have hbase := gap17_15_cfAutPGL2_Tbar hC h7 hPGL
  have hconj := hbase.map_mulEquiv (MulAut.conj g)
  rwa [hmap] at hconj

theorem gap17_15_cfAutInFGroup_of_pgl2 (h410 : W4Lem4_10) {Q : Type} [Group Q] [Finite Q]
    {S : Subgroup Q} (h : WeakClosure81.CFAutInFGroupPGL2 Q S) :
    CFAutInFGroup 1 Q S := by
  intro X hXn hXne hXmin hXnc L hL
  obtain ⟨h, hPGL⟩ := h X hXn hXne hXmin hXnc L hL
  exact ⟨h, inFGroup_of_isPGL2_seven h410
    (↥(CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL S L) ⧸
      (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autC S L).subgroupOf
        (CFSG.LocalAnalysis.UniquenessCase.UC22.F12.autNL S L)) hPGL⟩

theorem gap17_15_compFactorAutInF_holds (h410 : W4Lem4_10) {D : Data G}
    {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h7 : IsL2Over17 (Bar2 L) 7)
    (hPGL : CFSG.Quasithin.F6.IsPGL2 7 (Bar2 (L ⊔ NTL17 D L))) :
    ∀ T' : Subgroup (Bar2 (L ⊔ D.T)), CFSG.ABGLocalTools.IsSylowOf 2 T' ⊤ →
      CompFactorAutInF 1 (⊤ : Subgroup (Bar2 (L ⊔ D.T))) T' := by
  classical
  intro T' hT'
  have hT'in : IsSylowIn 2 T' ⊤ := by
    obtain ⟨hle, hP, hdvd⟩ :=
      (CFSG.ABGLocalTools.isSylowOf_iff (p := 2) (P := T') (K := ⊤)).mp hT'
    exact ⟨hle, hP, hdvd⟩
  have hPGLsyl : WeakClosure81.CFAutInFGroupPGL2 (Bar2 (L ⊔ D.T)) T' :=
    gap17_15_cfAutPGL2_sylow hC h7 hPGL hT'in
  intro Y hY hYn
  obtain rfl | hYne := eq_or_ne Y ⊥
  ·
    let e := (CFSG.Quasithin.H13.topBotEquiv (Bar2 (L ⊔ D.T))).symm
    have hS : Subgroup.map e.toMonoidHom T' =
        (T'.subgroupOf ⊤).map
          (QuotientGroup.mk' ((⊥ : Subgroup (Bar2 (L ⊔ D.T))).subgroupOf ⊤)) := by
      ext x
      constructor
      · rintro ⟨s, hs, rfl⟩
        exact Subgroup.mem_map.mpr
          ⟨⟨s, Subgroup.mem_top s⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      · rintro ⟨s, hs, rfl⟩
        exact ⟨(s : Bar2 (L ⊔ D.T)), Subgroup.mem_subgroupOf.mp hs, rfl⟩
    exact gap17_15_cfAutInFGroup_of_pgl2 h410
      (WeakClosure81.CFAutInFGroupPGL2.map_mulEquiv_eq e hS hPGLsyl)
  ·
    set F : Subgroup (Bar2 (L ⊔ D.T)) :=
      orbitClosure (UC22.barImage (L ⊔ D.T) L) (UC22.barImage (L ⊔ D.T) D.T) with hF
    set Tb : Subgroup (Bar2 (L ⊔ D.T)) := UC22.barImage (L ⊔ D.T) D.T with hTb
    have hYnQ : Y.Normal := by
      have h := (Subgroup.normal_subgroupOf_iff_le_normalizer (le_top : Y ≤ ⊤)).mp hYn
      exact Subgroup.normalizer_eq_top_iff.mp (le_antisymm le_top h)
    have hFY : F ≤ Y := by
      simpa [hF] using gap17_15_orbitClosure_le_of_normal hC h7 hYnQ hYne
    have hFT : F ⊔ Tb = ⊤ := by
      simpa [hF, hTb] using orbitClosure_sup_of_calC hC.memL
    have hFn : F.Normal := by
      simpa [hF] using gap17_15_orbitClosure_normal hC
    let f : ↥Tb →* (↥(⊤ : Subgroup (Bar2 (L ⊔ D.T))) ⧸ (Y.subgroupOf ⊤)) :=
      (QuotientGroup.mk' (Y.subgroupOf ⊤)).comp
        (Subgroup.inclusion (le_top : Tb ≤ ⊤))
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Y.subgroupOf ⊤) y
      have hxsup : (x : Bar2 (L ⊔ D.T)) ∈ F ⊔ Tb := by
        rw [hFT]
        exact Subgroup.mem_top _
      obtain ⟨a, ha, t, ht, hat⟩ := Subgroup.mem_sup_of_normal_left.mp hxsup
      refine ⟨⟨t, ht⟩, ?_⟩
      show (QuotientGroup.mk' (Y.subgroupOf ⊤))
          (Subgroup.inclusion (le_top : Tb ≤ ⊤) ⟨t, ht⟩) =
        (QuotientGroup.mk' (Y.subgroupOf ⊤)) x
      have hx_eq : x = Subgroup.inclusion (le_top : F ≤ ⊤) ⟨a, ha⟩ *
          Subgroup.inclusion (le_top : Tb ≤ ⊤) ⟨t, ht⟩ :=
        Subtype.ext hat.symm
      rw [hx_eq, map_mul]
      have haY : (QuotientGroup.mk' (Y.subgroupOf ⊤))
          (Subgroup.inclusion (le_top : F ≤ ⊤) ⟨a, ha⟩) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr
          (Subgroup.mem_subgroupOf.mpr (hFY ha))
      rw [haY, one_mul]
    have hQY : IsPGroup 2 (↥(⊤ : Subgroup (Bar2 (L ⊔ D.T))) ⧸ (Y.subgroupOf ⊤)) :=
      IsPGroup.of_surjective (barImage_T_sylow_of_calC hC.memL).isPGroup f hf
    exact WeakClosure81.cfAutInFGroup_of_isPGroup Nat.prime_two hQY 1 _

theorem gap17_15_threeConjInFSq_holds (h410 : W4Lem4_10) (h43c : W3Lem45_2Chief)
    (D : Data G) {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q) :
    Gap17_15_threeConjInFSq D V₀ V L r q hC := by
  intro h7 hPGL
  exact inFSq_of_components h43c (m := 1) (by norm_num)
    (barImage_component_of_calC hC.memL) (barImage_T_sylow_of_calC hC.memL)
    (orbitClosure_sup_of_calC hC.memL) (gap17_15_compFactorAutInF_holds h410 hC h7 hPGL)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

end
