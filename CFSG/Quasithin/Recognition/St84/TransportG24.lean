module

public import CFSG.Quasithin.Recognition.St84.TransferG24
public import CFSG.Quasithin.Recognition.St84.Sec4TreeTransfer
public import CFSG.Quasithin.Recognition.St84.Sec4TreeData
public import CFSG.Quasithin.Recognition.St84.Sec4Setup
public import CFSG.Quasithin.Recognition.St84.Sec6BaumannS3
public import CFSG.Quasithin.Background.SpecialPGroupMulEquiv
import CFSG.Quasithin.Background.SimsD1Transport
import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalLargeReeBZero

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ CFSG.GH74.QTGen4.DSGen4
open CFSG.SignalizerFunctorTheorem.CatalogBridge (isoOfMapEq)
open scoped Pointwise commutatorElement

variable {H : Type} [Group H] [Finite H]

private theorem pCoreOf_map_subgroupOf {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    (hφ : Function.Injective φ) {Y : Subgroup H} (hY : Y ≤ P) :
    pCoreOf 2 ((Y.subgroupOf P).map φ) = ((pCoreOf 2 Y).subgroupOf P).map φ := by
  rw [pCoreOf_map_injective φ hφ, CFSG.Quasithin.H13.U3.GC137.pCoreOf_subgroupOf_eq hY]

private theorem oTwoPrime_map_subgroupOf {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    (hφ : Function.Injective φ) {Y : Subgroup H} (hY : Y ≤ P) :
    oTwoPrime ((Y.subgroupOf P).map φ) = ((oTwoPrime Y).subgroupOf P).map φ := by
  have hside : oTwoPrime (Y.subgroupOf P) = (oTwoPrime Y).subgroupOf P := by
    refine Subgroup.map_injective (f := P.subtype) P.subtype_injective ?_
    rw [← oTwoPrime_map (f := P.subtype) P.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hY,
      Subgroup.map_subgroupOf_eq_of_le ((oTwoPrime_le Y).trans hY)]
  rw [oTwoPrime_map (f := φ) hφ, hside]

private theorem relCent_map_subgroupOf {U : Type} [Group U] {P : Subgroup H} {φ : ↥P →* U}
    (hφ : Function.Injective φ) {E Z C : Subgroup H} (hE : E ≤ P) (hZ : Z ≤ P)
    (hC : C ≤ P) (hEZ : E ≤ Subgroup.normalizer (Z : Set H)) :
    relCent ((E.subgroupOf P).map φ) ((Z.subgroupOf P).map φ) ((C.subgroupOf P).map φ) =
      ((relCent E Z C).subgroupOf P).map φ := by
  have hEZ' : E.subgroupOf P ≤
      Subgroup.normalizer ((Z.subgroupOf P : Subgroup ↥P) : Set ↥P) := by
    rw [Subgroup.le_normalizer_iff]
    intro e he z hz
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hEZ he) z).mp hz)
  rw [CFSG.Quasithin.St84.relCent_subgroupOf hE hZ hC hEZ hEZ',
    CFSG.Quasithin.St84.relCent_map_of_injective φ hφ hEZ']

private theorem g24EdgeData_dictionary {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    {Pa Pb Ea Eb : Subgroup H} {φa : ↥Pa →* (f112Gold L1 L2 S).Universal}
    {φb : ↥Pb →* (f112Gold L1 L2 S).Universal}
    (hφa : Function.Injective φa) (hφb : Function.Injective φb)
    (hEa : Ea ≤ Pa) (hEb : Eb ≤ Pb) (hKa : f112saK L1 L2 S ≤ Pa)
    (ha : (X.Gi 0).map (f112E5 L1 L2 S).subtype = (Ea.subgroupOf Pa).map φa)
    (hb : (X.Gi 1).map (f112E5 L1 L2 S).subtype = (Eb.subgroupOf Pb).map φb)
    (hK : (X.Gi 0 ⊓ X.Gi 1).map (f112E5 L1 L2 S).subtype =
      ((f112saK L1 L2 S).subgroupOf Pa).map φa) :
    ((X.L 0).map (f112E5 L1 L2 S).subtype = ((oTwoPrime Ea).subgroupOf Pa).map φa) ∧
    ((X.L 1).map (f112E5 L1 L2 S).subtype = ((oTwoPrime Eb).subgroupOf Pb).map φb) ∧
    ((pCoreOf 2 (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Ea).subgroupOf Pa).map φa) ∧
    ((pCoreOf 2 (X.L 1)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Eb).subgroupOf Pb).map φb) ∧
    ((centerOf (pCoreOf 2 (X.L 0))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Ea)).subgroupOf Pa).map φa) ∧
    ((centerOf (pCoreOf 2 (X.L 1))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Eb)).subgroupOf Pb).map φb) ∧
    ((centerOf (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((centerOf (oTwoPrime Ea)).subgroupOf Pa).map φa) ∧
    (X.S.map (f112E5 L1 L2 S).subtype =
      ((S ⊓ f112saK L1 L2 S).subgroupOf Pa).map φa) := by
  have hj : Function.Injective (f112E5 L1 L2 S).subtype :=
    (f112E5 L1 L2 S).subtype_injective
  have hLa : oTwoPrime Ea ≤ Pa := (oTwoPrime_le Ea).trans hEa
  have hLb : oTwoPrime Eb ≤ Pb := (oTwoPrime_le Eb).trans hEb
  have hQaP : pCoreOf 2 Ea ≤ Pa :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Ea).trans hEa
  have hQbP : pCoreOf 2 Eb ≤ Pb :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Eb).trans hEb
  have hZaP : centerOf (pCoreOf 2 Ea) ≤ Pa := inf_le_left.trans hQaP
  have hZbP : centerOf (pCoreOf 2 Eb) ≤ Pb := inf_le_left.trans hQbP
  have hCLa : centerOf (oTwoPrime Ea) ≤ Pa := inf_le_left.trans hLa
  have dL0 : (X.L 0).map (f112E5 L1 L2 S).subtype =
      ((oTwoPrime Ea).subgroupOf Pa).map φa := by
    rw [← oTwoPrime_map (f := (f112E5 L1 L2 S).subtype) hj, ha]
    exact oTwoPrime_map_subgroupOf hφa hEa
  have dL1 : (X.L 1).map (f112E5 L1 L2 S).subtype =
      ((oTwoPrime Eb).subgroupOf Pb).map φb := by
    rw [← oTwoPrime_map (f := (f112E5 L1 L2 S).subtype) hj, hb]
    exact oTwoPrime_map_subgroupOf hφb hEb
  have dQ0 : (pCoreOf 2 (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Ea).subgroupOf Pa).map φa := by
    rw [← pCoreOf_map_injective _ hj, dL0, pCoreOf_map_subgroupOf hφa hLa,
      pCoreOf_oTwoPrime Ea]
  have dQ1 : (pCoreOf 2 (X.L 1)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Eb).subgroupOf Pb).map φb := by
    rw [← pCoreOf_map_injective _ hj, dL1, pCoreOf_map_subgroupOf hφb hLb,
      pCoreOf_oTwoPrime Eb]
  have dZ0 : (centerOf (pCoreOf 2 (X.L 0))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Ea)).subgroupOf Pa).map φa := by
    rw [← SimsD1.TransGrp.centerOf_map_eq _ hj, dQ0,
      centerOf_map_eq_of_le hφa hQaP]
  have dZ1 : (centerOf (pCoreOf 2 (X.L 1))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Eb)).subgroupOf Pb).map φb := by
    rw [← SimsD1.TransGrp.centerOf_map_eq _ hj, dQ1,
      centerOf_map_eq_of_le hφb hQbP]
  have dCL0 : (centerOf (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((centerOf (oTwoPrime Ea)).subgroupOf Pa).map φa := by
    rw [← SimsD1.TransGrp.centerOf_map_eq _ hj, dL0,
      centerOf_map_eq_of_le hφa hLa]
  have dS : X.S.map (f112E5 L1 L2 S).subtype =
      ((S ⊓ f112saK L1 L2 S).subgroupOf Pa).map φa := by
    rw [← pCoreOf_map_injective _ hj, hK, pCoreOf_map_subgroupOf hφa hKa,
      f112_pCoreOf_K_eq hF h1 h2]
  exact ⟨dL0, dL1, dQ0, dQ1, dZ0, dZ1, dCL0, dS⟩

private theorem g24EdgeData_irr_left {L1 L2 S : Subgroup H}
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    {Pa Ea : Subgroup H} {φa : ↥Pa →* (f112Gold L1 L2 S).Universal}
    (hφa : Function.Injective φa) (hEa : Ea ≤ Pa)
    (ha : (X.Gi 0).map (f112E5 L1 L2 S).subtype = (Ea.subgroupOf Pa).map φa)
    (he : X.TreeG24Extra)
    (dQ0 : (pCoreOf 2 (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Ea).subgroupOf Pa).map φa)
    (dZ0 : (centerOf (pCoreOf 2 (X.L 0))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Ea)).subgroupOf Pa).map φa) :
    ∀ Y : Subgroup H, centerOf (pCoreOf 2 Ea) ≤ Y → Y ≤ pCoreOf 2 Ea →
      Ea ≤ Subgroup.normalizer (Y : Set H) →
      Y = centerOf (pCoreOf 2 Ea) ∨ Y = pCoreOf 2 Ea := by
  have hj : Function.Injective (f112E5 L1 L2 S).subtype :=
    (f112E5 L1 L2 S).subtype_injective
  have hQaP : pCoreOf 2 Ea ≤ Pa :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Ea).trans hEa
  have hZaP : centerOf (pCoreOf 2 Ea) ≤ Pa := inf_le_left.trans hQaP
  intro Y hZY hYQ hEY
  have hYP : Y ≤ Pa := hYQ.trans hQaP
  have hYEa : Y ≤ Ea := hYQ.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 Ea)
  obtain ⟨Y', hY'⟩ :=
    SimsD1.TransGrp.exists_map_eq_of_le_map (f112E5 L1 L2 S).subtype
      ((Subgroup.map_mono (Subgroup.subgroupOf_mono Pa hYEa)).trans ha.ge)
  have hZY' : centerOf (pCoreOf 2 (X.L 0)) ≤ Y' := by
    rw [← Subgroup.map_le_map_iff_of_injective hj, dZ0, hY']
    exact (SimsD1.Transport.img_le_img_iff hφa hZaP).mpr hZY
  have hY'Q : Y' ≤ pCoreOf 2 (X.L 0) := by
    rw [← Subgroup.map_le_map_iff_of_injective hj, dQ0, hY']
    exact (SimsD1.Transport.img_le_img_iff hφa hYP).mpr hYQ
  have hGY' : X.Gi 0 ≤ Subgroup.normalizer (Y' : Set ↥(f112E5 L1 L2 S)) :=
    (SimsD1.TransGrp.le_normalizer_map_iff _ hj _ _).mp (by
      rw [ha, hY']
      exact (SimsD1.Transport.le_normalizer_img_iff hφa hEa hYP).mpr hEY)
  rcases he.irr_left Y' hZY' hY'Q hGY' with h | h
  · left
    refine (SimsD1.Transport.img_inj hφa hYP hZaP).mp ?_
    rw [SimsD1.Transport.img, SimsD1.Transport.img,
      ← hY', ← dZ0, h]
  · right
    refine (SimsD1.Transport.img_inj hφa hYP hQaP).mp ?_
    rw [SimsD1.Transport.img, SimsD1.Transport.img,
      ← hY', ← dQ0, h]

private theorem g24EdgeData_orth_left {L1 L2 S : Subgroup H}
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    {Pa Ea : Subgroup H} {φa : ↥Pa →* (f112Gold L1 L2 S).Universal}
    (hφa : Function.Injective φa) (hEa : Ea ≤ Pa)
    (ha : (X.Gi 0).map (f112E5 L1 L2 S).subtype = (Ea.subgroupOf Pa).map φa)
    (he : X.TreeG24Extra)
    (dL0 : (X.L 0).map (f112E5 L1 L2 S).subtype = ((oTwoPrime Ea).subgroupOf Pa).map φa)
    (dQ0 : (pCoreOf 2 (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Ea).subgroupOf Pa).map φa)
    (dZ0 : (centerOf (pCoreOf 2 (X.L 0))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Ea)).subgroupOf Pa).map φa) :
    ∃ E : Subgroup H, centerOf (pCoreOf 2 Ea) ≤ E ∧ E ≤ pCoreOf 2 Ea ∧
      (centerOf (pCoreOf 2 Ea)).relIndex E = 16 ∧
      oTwoPrime Ea ≤ Subgroup.normalizer (E : Set H) ∧
      (∃ l ∈ oTwoPrime Ea, ∃ e ∈ E, ⁅l, e⁆ ∉ centerOf (pCoreOf 2 Ea)) ∧
      ¬ NatSec (oTwoPrime Ea) (centerOf (pCoreOf 2 Ea)) E := by
  have hj : Function.Injective (f112E5 L1 L2 S).subtype :=
    (f112E5 L1 L2 S).subtype_injective
  have hLa : oTwoPrime Ea ≤ Pa := (oTwoPrime_le Ea).trans hEa
  have hQaP : pCoreOf 2 Ea ≤ Pa :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Ea).trans hEa
  have hZaP : centerOf (pCoreOf 2 Ea) ≤ Pa := inf_le_left.trans hQaP
  obtain ⟨E', hZE', hE'Q, hidx, hLE', ⟨l', hl', e', he', hle'⟩, hnat⟩ := he.orth_left
  have hE'G : E' ≤ X.Gi 0 :=
    hE'Q.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (oTwoPrime_le _))
  obtain ⟨E, hEEa, hE'⟩ :=
    SimsD1.Embed.exists_of_le_map hφa hEa
      ((Subgroup.map_mono hE'G).trans ha.le)
  have hEP : E ≤ Pa := hEEa.trans hEa
  refine ⟨E, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← SimsD1.Transport.img_le_img_iff hφa hZaP,
      SimsD1.Transport.img, SimsD1.Transport.img,
      ← dZ0, ← hE']
    exact Subgroup.map_mono hZE'
  · rw [← SimsD1.Transport.img_le_img_iff hφa hEP,
      SimsD1.Transport.img, SimsD1.Transport.img,
      ← dQ0, ← hE']
    exact Subgroup.map_mono hE'Q
  · rw [← Subgroup.relIndex_subgroupOf hEP,
      ← Subgroup.relIndex_map_map_of_injective _ _ hφa, ← dZ0, ← hE',
      Subgroup.relIndex_map_map_of_injective _ _ hj]
    exact hidx
  · exact (SimsD1.Transport.le_normalizer_img_iff hφa hLa hEP).mp (by
      rw [SimsD1.Transport.img, SimsD1.Transport.img,
        ← dL0, ← hE']
      exact (SimsD1.TransGrp.le_normalizer_map_iff _ hj _ _).mpr hLE')
  · obtain ⟨p, hp, hpl⟩ : (f112E5 L1 L2 S).subtype l' ∈
        ((oTwoPrime Ea).subgroupOf Pa).map φa := by
      rw [← dL0]
      exact ⟨l', hl', rfl⟩
    obtain ⟨q, hq, hqe⟩ : (f112E5 L1 L2 S).subtype e' ∈ (E.subgroupOf Pa).map φa := by
      rw [← hE']
      exact ⟨e', he', rfl⟩
    refine ⟨p, hp, q, hq, fun hmem => hle' ?_⟩
    have h1 : φa ⁅p, q⁆ ∈ ((centerOf (pCoreOf 2 Ea)).subgroupOf Pa).map φa := by
      refine ⟨⁅p, q⁆, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf,
        show ((⁅p, q⁆ : ↥Pa) : H) = ⁅(p : H), (q : H)⁆ from map_commutatorElement Pa.subtype p q]
      exact hmem
    rw [map_commutatorElement, hpl, hqe, ← map_commutatorElement, ← dZ0] at h1
    exact (Subgroup.mem_map_iff_mem hj).mp h1
  · rwa [← natSec_map_iff_of_le hφa hLa hZaP hEP dL0 dZ0 hE']

private theorem g24EdgeData_relCent_S {L1 L2 S : Subgroup H}
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    {Pa Pb Ea Eb : Subgroup H} {φa : ↥Pa →* (f112Gold L1 L2 S).Universal}
    {φb : ↥Pb →* (f112Gold L1 L2 S).Universal}
    (hφa : Function.Injective φa) (hEa : Ea ≤ Pa) (hEb : Eb ≤ Pb)
    (hKa : f112saK L1 L2 S ≤ Pa) (hKb : f112saK L1 L2 S ≤ Pb)
    (hab : ∀ (y : H) (hya : y ∈ Pa) (hyb : y ∈ Pb), φa ⟨y, hya⟩ = φb ⟨y, hyb⟩)
    (hQb : pCoreOf 2 Eb ≤ S ⊓ f112saK L1 L2 S)
    (dQ0 : (pCoreOf 2 (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Ea).subgroupOf Pa).map φa)
    (dZ0 : (centerOf (pCoreOf 2 (X.L 0))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Ea)).subgroupOf Pa).map φa)
    (dS : X.S.map (f112E5 L1 L2 S).subtype =
      ((S ⊓ f112saK L1 L2 S).subgroupOf Pa).map φa)
    (dZ1 : (centerOf (pCoreOf 2 (X.L 1))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Eb)).subgroupOf Pb).map φb)
    (ht : X.TreeG24Transfer) :
    relCent (pCoreOf 2 Ea) (centerOf (pCoreOf 2 Ea)) (S ⊓ f112saK L1 L2 S) =
      centerOf (pCoreOf 2 Eb) := by
  have hj : Function.Injective (f112E5 L1 L2 S).subtype :=
    (f112E5 L1 L2 S).subtype_injective
  have hQaP : pCoreOf 2 Ea ≤ Pa :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Ea).trans hEa
  have hQbP : pCoreOf 2 Eb ≤ Pb :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Eb).trans hEb
  have hZaP : centerOf (pCoreOf 2 Ea) ≤ Pa := inf_le_left.trans hQaP
  have hZbP : centerOf (pCoreOf 2 Eb) ≤ Pb := inf_le_left.trans hQbP
  have hZbQ : centerOf (pCoreOf 2 Eb) ≤ pCoreOf 2 Eb := inf_le_left
  have hTa : S ⊓ f112saK L1 L2 S ≤ Pa := inf_le_right.trans hKa
  have hTb : S ⊓ f112saK L1 L2 S ≤ Pb := inf_le_right.trans hKb
  have hQaN : pCoreOf 2 Ea ≤ Subgroup.normalizer (centerOf (pCoreOf 2 Ea) : Set H) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf _)
  have hQ'N : pCoreOf 2 (X.L 0) ≤
      Subgroup.normalizer (centerOf (pCoreOf 2 (X.L 0)) : Set ↥(f112E5 L1 L2 S)) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_centerOf _)
  have hZbT : centerOf (pCoreOf 2 Eb) ≤ S ⊓ f112saK L1 L2 S := hZbQ.trans hQb
  have hRP : relCent (pCoreOf 2 Ea) (centerOf (pCoreOf 2 Ea))
      (S ⊓ f112saK L1 L2 S) ≤ Pa := (relCent_le _ _ _).trans hQaP
  refine (SimsD1.Transport.img_inj hφa hRP (hZbT.trans hTa)).mp ?_
  rw [SimsD1.Transport.img, SimsD1.Transport.img]
  calc ((relCent (pCoreOf 2 Ea) (centerOf (pCoreOf 2 Ea))
        (S ⊓ f112saK L1 L2 S)).subgroupOf Pa).map φa
      = relCent (((pCoreOf 2 Ea).subgroupOf Pa).map φa)
          (((centerOf (pCoreOf 2 Ea)).subgroupOf Pa).map φa)
          (((S ⊓ f112saK L1 L2 S).subgroupOf Pa).map φa) :=
        (relCent_map_subgroupOf hφa hQaP hZaP hTa hQaN).symm
    _ = (relCent (pCoreOf 2 (X.L 0)) (centerOf (pCoreOf 2 (X.L 0))) X.S).map
          (f112E5 L1 L2 S).subtype := by
        rw [CFSG.Quasithin.St84.relCent_map_of_injective _ hj hQ'N, dQ0, dZ0, dS]
    _ = (centerOf (pCoreOf 2 (X.L 1))).map (f112E5 L1 L2 S).subtype := by
        rw [ht.relCent_S]
    _ = ((centerOf (pCoreOf 2 Eb)).subgroupOf Pb).map φb := dZ1
    _ = ((centerOf (pCoreOf 2 Eb)).subgroupOf Pa).map φa :=
        (H13.F431.subImg_eq_of_agree hab (hZbT.trans hTa)
          (hZbT.trans hTb)).symm

private theorem g24EdgeData_mid_right {L1 L2 S : Subgroup H}
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    {Pb Eb : Subgroup H} {φb : ↥Pb →* (f112Gold L1 L2 S).Universal}
    (hφb : Function.Injective φb) (hEb : Eb ≤ Pb)
    (hb : (X.Gi 1).map (f112E5 L1 L2 S).subtype = (Eb.subgroupOf Pb).map φb)
    (hd : X.TreeG24Data)
    (dL1 : (X.L 1).map (f112E5 L1 L2 S).subtype = ((oTwoPrime Eb).subgroupOf Pb).map φb)
    (dQ1 : (pCoreOf 2 (X.L 1)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Eb).subgroupOf Pb).map φb)
    (dZ1 : (centerOf (pCoreOf 2 (X.L 1))).map (f112E5 L1 L2 S).subtype =
      ((centerOf (pCoreOf 2 Eb)).subgroupOf Pb).map φb) :
    ∃ W : Subgroup H, centerOf (pCoreOf 2 Eb) ≤ W ∧ W ≤ pCoreOf 2 Eb ∧
      Nat.card ↥W = 2 ^ 6 ∧ ⁅W, oTwoPrime Eb⁆ ≤ centerOf (pCoreOf 2 Eb) ∧
      NatSec (oTwoPrime Eb) W (pCoreOf 2 Eb) := by
  have hLb : oTwoPrime Eb ≤ Pb := (oTwoPrime_le Eb).trans hEb
  have hQbP : pCoreOf 2 Eb ≤ Pb :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Eb).trans hEb
  have hZbP : centerOf (pCoreOf 2 Eb) ≤ Pb := inf_le_left.trans hQbP
  obtain ⟨W', hZW', hW'Q, hW'card, hW'comm, hW'nat⟩ := hd.mid_right
  have hW'G : W' ≤ X.Gi 1 :=
    hW'Q.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (oTwoPrime_le _))
  obtain ⟨W, hWEb, hW'⟩ :=
    SimsD1.Embed.exists_of_le_map hφb hEb
      ((Subgroup.map_mono hW'G).trans hb.le)
  have hWP : W ≤ Pb := hWEb.trans hEb
  refine ⟨W, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← SimsD1.Transport.img_le_img_iff hφb hZbP,
      SimsD1.Transport.img, SimsD1.Transport.img,
      ← dZ1, ← hW']
    exact Subgroup.map_mono hZW'
  · rw [← SimsD1.Transport.img_le_img_iff hφb hWP,
      SimsD1.Transport.img, SimsD1.Transport.img,
      ← dQ1, ← hW']
    exact Subgroup.map_mono hW'Q
  · rw [← card_of_map_eq_of_le hφb hWP hW']
    exact hW'card
  · rw [← SimsD1.Transport.img_le_img_iff hφb
      (Subgroup.commutator_le_of_le hWP hLb),
      SimsD1.Transport.img, SimsD1.Transport.img,
      ← commutator_map_eq_of_le hWP hLb, ← hW', ← dL1, ← Subgroup.map_commutator, ← dZ1]
    exact Subgroup.map_mono hW'comm
  · exact (natSec_map_iff_of_le hφb hLb hWP hQbP dL1 hW' dQ1).mp hW'nat

private theorem g24EdgeData_cent_right {L1 L2 S : Subgroup H}
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    {Pa Pb Ea Eb : Subgroup H} {φa : ↥Pa →* (f112Gold L1 L2 S).Universal}
    {φb : ↥Pb →* (f112Gold L1 L2 S).Universal}
    (hφa : Function.Injective φa) (hφb : Function.Injective φb) (hEb : Eb ≤ Pb)
    (hKa : f112saK L1 L2 S ≤ Pa) (hKb : f112saK L1 L2 S ≤ Pb)
    (hab : ∀ (y : H) (hya : y ∈ Pa) (hyb : y ∈ Pb), φa ⟨y, hya⟩ = φb ⟨y, hyb⟩)
    (hQb : pCoreOf 2 Eb ≤ S ⊓ f112saK L1 L2 S)
    (dQ0 : (pCoreOf 2 (X.L 0)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Ea).subgroupOf Pa).map φa)
    (dQ1 : (pCoreOf 2 (X.L 1)).map (f112E5 L1 L2 S).subtype =
      ((pCoreOf 2 Eb).subgroupOf Pb).map φb)
    (dL1 : (X.L 1).map (f112E5 L1 L2 S).subtype = ((oTwoPrime Eb).subgroupOf Pb).map φb)
    (ht : X.TreeG24Transfer) :
    ∀ k ∈ oTwoPrime Eb, orderOf k = 3 →
      pCoreOf 2 Eb ⊓ Subgroup.centralizer ({k} : Set H) ≤ pCoreOf 2 Ea := by
  have hj : Function.Injective (f112E5 L1 L2 S).subtype :=
    (f112E5 L1 L2 S).subtype_injective
  have hLb : oTwoPrime Eb ≤ Pb := (oTwoPrime_le Eb).trans hEb
  have hQbP : pCoreOf 2 Eb ≤ Pb :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Eb).trans hEb
  have hTa : S ⊓ f112saK L1 L2 S ≤ Pa := inf_le_right.trans hKa
  have hTb : S ⊓ f112saK L1 L2 S ≤ Pb := inf_le_right.trans hKb
  intro k hk hk3 x hx
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨k', hk', hk'e⟩ : φb ⟨k, hLb hk⟩ ∈
      (X.L 1).map (f112E5 L1 L2 S).subtype := by
    rw [dL1]
    exact ⟨⟨k, hLb hk⟩, hk, rfl⟩
  change (k' : (f112Gold L1 L2 S).Universal) = φb ⟨k, hLb hk⟩ at hk'e
  obtain ⟨x', hx', hx'e⟩ : φb ⟨x, hQbP hxQ⟩ ∈
      (pCoreOf 2 (X.L 1)).map (f112E5 L1 L2 S).subtype := by
    rw [dQ1]
    exact ⟨⟨x, hQbP hxQ⟩, hxQ, rfl⟩
  change (x' : (f112Gold L1 L2 S).Universal) = φb ⟨x, hQbP hxQ⟩ at hx'e
  have hk'3 : orderOf k' = 3 := by
    rw [← orderOf_injective _ hj k']
    show orderOf ((k' : ↥(f112E5 L1 L2 S)) : (f112Gold L1 L2 S).Universal) = 3
    rw [hk'e, orderOf_injective _ hφb, Subgroup.orderOf_mk, hk3]
  have hx'C : x' ∈ Subgroup.centralizer ({k'} : Set ↥(f112E5 L1 L2 S)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hj
    have hxk : x * k = k * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
    simp only [map_mul, Subgroup.coe_subtype]
    rw [hx'e, hk'e, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hxk
  have hx'Q := ht.cent_right k' hk' hk'3 (Subgroup.mem_inf.mpr ⟨hx', hx'C⟩)
  obtain ⟨y, hy, hyx⟩ : φb ⟨x, hQbP hxQ⟩ ∈ ((pCoreOf 2 Ea).subgroupOf Pa).map φa := by
    rw [← dQ0, ← hx'e]
    exact ⟨x', hx'Q, rfl⟩
  have hxT : x ∈ S ⊓ f112saK L1 L2 S := hQb hxQ
  rw [← hab x (hTa hxT) (hTb hxT)] at hyx
  have hy' : y = ⟨x, hTa hxT⟩ := hφa hyx
  subst hy'
  exact hy

private theorem g24EdgeData_of_tree {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    {Pa Pb Ea Eb : Subgroup H} {φa : ↥Pa →* (f112Gold L1 L2 S).Universal}
    {φb : ↥Pb →* (f112Gold L1 L2 S).Universal}
    (hφa : Function.Injective φa) (hφb : Function.Injective φb)
    (hEa : Ea ≤ Pa) (hEb : Eb ≤ Pb)
    (hKa : f112saK L1 L2 S ≤ Pa) (hKb : f112saK L1 L2 S ≤ Pb)
    (hab : ∀ (y : H) (hya : y ∈ Pa) (hyb : y ∈ Pb), φa ⟨y, hya⟩ = φb ⟨y, hyb⟩)
    (hmeet : ∀ {Y Z : Subgroup H}, Y ≤ Pa → Z ≤ Pb →
      (Y.subgroupOf Pa).map φa ⊓ (Z.subgroupOf Pb).map φb = ((Y ⊓ Z).subgroupOf Pa).map φa)
    (ha : (X.Gi 0).map (f112E5 L1 L2 S).subtype = (Ea.subgroupOf Pa).map φa)
    (hb : (X.Gi 1).map (f112E5 L1 L2 S).subtype = (Eb.subgroupOf Pb).map φb)
    (hK : (X.Gi 0 ⊓ X.Gi 1).map (f112E5 L1 L2 S).subtype =
      ((f112saK L1 L2 S).subgroupOf Pa).map φa)
    (hQb : pCoreOf 2 Eb ≤ S ⊓ f112saK L1 L2 S)
    (hd : X.TreeG24Data) (he : X.TreeG24Extra) (ht : X.TreeG24Transfer) :
    G24EdgeData Ea Eb (f112saK L1 L2 S) (S ⊓ f112saK L1 L2 S) := by
  obtain ⟨dL0, dL1, dQ0, dQ1, dZ0, dZ1, dCL0, dS⟩ :=
    g24EdgeData_dictionary (X := X) hF h1 h2 hφa hφb hEa hEb hKa ha hb hK
  have hj : Function.Injective (f112E5 L1 L2 S).subtype :=
    (f112E5 L1 L2 S).subtype_injective
  have hLa : oTwoPrime Ea ≤ Pa := (oTwoPrime_le Ea).trans hEa
  have hLb : oTwoPrime Eb ≤ Pb := (oTwoPrime_le Eb).trans hEb
  have hQaP : pCoreOf 2 Ea ≤ Pa :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Ea).trans hEa
  have hQbP : pCoreOf 2 Eb ≤ Pb :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 Eb).trans hEb
  have hZaP : centerOf (pCoreOf 2 Ea) ≤ Pa := inf_le_left.trans hQaP
  have hZbP : centerOf (pCoreOf 2 Eb) ≤ Pb := inf_le_left.trans hQbP
  have hCLa : centerOf (oTwoPrime Ea) ≤ Pa := inf_le_left.trans hLa
  have hTa : S ⊓ f112saK L1 L2 S ≤ Pa := inf_le_right.trans hKa
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact IsSpecialPow.of_mulEquiv
      ((isoOfMapEq (f112E5 L1 L2 S)
        (pCoreOf 2 (X.L 0)) ((pCoreOf 2 Ea).subgroupOf Pa) φa hφa dQ0).trans
      (Subgroup.subgroupOfEquivOfLe hQaP)) hd.special_left
  · refine (SimsD1.Transport.img_inj hφa hZaP hCLa).mp ?_
    rw [SimsD1.Transport.img, SimsD1.Transport.img,
      ← dZ0, ← dCL0, hd.center_left]
  · refine (SimsD1.Transport.img_inj hφa
      (Subgroup.commutator_le_of_le hQaP hLa) hQaP).mp ?_
    rw [SimsD1.Transport.img, SimsD1.Transport.img,
      ← commutator_map_eq_of_le hQaP hLa, ← dQ0, ← dL0, ← Subgroup.map_commutator,
      hd.indec_left]
  · exact g24EdgeData_irr_left hφa hEa ha he dQ0 dZ0
  · exact g24EdgeData_orth_left hφa hEa ha he dL0 dQ0 dZ0
  · exact g24EdgeData_relCent_S hφa hEa hEb hKa hKb hab hQb dQ0 dZ0 dS dZ1 ht
  · exact (card_of_map_eq_of_le hφb hQbP dQ1).symm.trans hd.card_right
  · exact IsSpecialPGroup.of_mulEquiv
      ((isoOfMapEq (f112E5 L1 L2 S)
        (pCoreOf 2 (X.L 1)) ((pCoreOf 2 Eb).subgroupOf Pb) φb hφb dQ1).trans
      (Subgroup.subgroupOfEquivOfLe hQbP)) hd.special_right
  · exact (card_of_map_eq_of_le hφb hZbP dZ1).symm.trans hd.card_center_right
  · have dbot : (⊥ : Subgroup ↥(f112E5 L1 L2 S)).map (f112E5 L1 L2 S).subtype =
        ((⊥ : Subgroup H).subgroupOf Pb).map φb := by
      rw [Subgroup.map_bot, Subgroup.bot_subgroupOf, Subgroup.map_bot]
    exact (natSec_map_iff_of_le hφb hLb bot_le hZbP dL1 dbot dZ1).mp hd.natZ_right
  · exact g24EdgeData_mid_right hφb hEb hb hd dL1 dQ1 dZ1
  · refine (SimsD1.Transport.img_inj hφb
      (Subgroup.commutator_le_of_le hQbP hLb) hQbP).mp ?_
    rw [SimsD1.Transport.img, SimsD1.Transport.img,
      ← commutator_map_eq_of_le hQbP hLb, ← dQ1, ← dL1, ← Subgroup.map_commutator,
      he.comm_right]
  · exact g24EdgeData_cent_right hφa hφb hEb hKa hKb hab hQb dQ0 dQ1 dL1 ht
  · exact (card_of_map_eq_of_le hφa hTa dS).symm.trans hd.card_S
  · exact (card_of_map_eq_of_le hφa hKa hK).symm.trans hd.card_edge
  · have h : (pCoreOf 2 (X.L 0) ⊓ pCoreOf 2 (X.L 1)).map (f112E5 L1 L2 S).subtype =
        ((pCoreOf 2 Ea ⊓ pCoreOf 2 Eb).subgroupOf Pa).map φa := by
      rw [Subgroup.map_inf _ _ _ hj, dQ0, dQ1]
      exact hmeet hQaP hQbP
    exact (card_of_map_eq_of_le hφa (inf_le_left.trans hQaP) h).symm.trans hd.card_inf

private theorem f112_g24TransferData_of_treeG24Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeG24Data) (he : X.TreeG24Extra) (ht : X.TreeG24Transfer) :
    G24TransferData L1 L2 S := by
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  have hT := f112_pCoreOf_sup_eq hF h1 h2
  exact g24EdgeData_of_tree hF h1 h2 (X := X)
    (Pa := f112P1 L1 L2 S) (Pb := f112P2 L1 L2 S)
    (φa := (f112Gold L1 L2 S).ofA) (φb := (f112Gold L1 L2 S).ofB)
    (f112Gold L1 L2 S).ofA_injective (f112Gold L1 L2 S).ofB_injective
    (f112sa_P1'_le_P1 hF) (f112sa_P2'_le_P2 hF)
    ((f112saK_le_P1' L1 L2 S).trans (f112sa_P1'_le_P1 hF))
    ((f112saK_le_P2' L1 L2 S).trans (f112sa_P2'_le_P2 hF))
    (fun y hya hyb => f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨hya, hyb⟩)
    (fun hY hZ => ofA_map_inf_ofB_map L1 L2 S hY hZ)
    D.gi_zero_map D.gi_one_map D.gi_inf_map (le_sup_right.trans hT.le) hd he ht

private theorem f112_g24TransferData_swap_of_treeG24Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.swap.TreeG24Data) (he : X.swap.TreeG24Extra) (ht : X.swap.TreeG24Transfer) :
    G24TransferData L2 L1 S := by
  let D := f112BaseEdgeData hF h1 h2 X hX0 hX1
  have hT := f112_pCoreOf_sup_eq hF h1 h2
  have hK1 : f112saK L1 L2 S ≤ f112P1 L1 L2 S :=
    (f112saK_le_P1' L1 L2 S).trans (f112sa_P1'_le_P1 hF)
  have hK2 : f112saK L1 L2 S ≤ f112P2 L1 L2 S :=
    (f112saK_le_P2' L1 L2 S).trans (f112sa_P2'_le_P2 hF)
  have ha : (X.swap.Gi 0).map (f112E5 L1 L2 S).subtype =
      ((f112saP2' L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB := by
    rw [Setup.swap_Gi, sub_zero]
    exact D.gi_one_map
  have hb : (X.swap.Gi 1).map (f112E5 L1 L2 S).subtype =
      ((f112saP1' L1 L2 S).subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA := by
    rw [Setup.swap_Gi, sub_self]
    exact D.gi_zero_map
  have hK : (X.swap.Gi 0 ⊓ X.swap.Gi 1).map (f112E5 L1 L2 S).subtype =
      ((f112saK L1 L2 S).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB := by
    rw [Setup.swap_Gi, Setup.swap_Gi, sub_zero, sub_self, inf_comm (X.Gi 1) (X.Gi 0)]
    exact D.gi_inf_map.trans (ofA_subgroupOf_eq_ofB_subgroupOf L1 L2 S (le_inf hK1 hK2))
  have hmeet : ∀ {Y Z : Subgroup H}, Y ≤ f112P2 L1 L2 S → Z ≤ f112P1 L1 L2 S →
      (Y.subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ⊓
          (Z.subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA =
        ((Y ⊓ Z).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB := by
    intro Y Z hY hZ
    calc (Y.subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB ⊓
          (Z.subgroupOf (f112P1 L1 L2 S)).map (f112Gold L1 L2 S).ofA
        = f112OfA L1 L2 S Z ⊓ f112OfB L1 L2 S Y := inf_comm _ _
      _ = f112OfA L1 L2 S (Z ⊓ Y) := ofA_map_inf_ofB_map L1 L2 S hZ hY
      _ = f112OfB L1 L2 S (Z ⊓ Y) :=
          ofA_subgroupOf_eq_ofB_subgroupOf L1 L2 S
            (le_inf (inf_le_left.trans hZ) (inf_le_right.trans hY))
      _ = ((Y ⊓ Z).subgroupOf (f112P2 L1 L2 S)).map (f112Gold L1 L2 S).ofB := by
          rw [inf_comm Z Y]
  rw [g24TransferData_swap_iff]
  exact g24EdgeData_of_tree hF h1 h2 (X := X.swap)
    (Pa := f112P2 L1 L2 S) (Pb := f112P1 L1 L2 S)
    (φa := (f112Gold L1 L2 S).ofB) (φb := (f112Gold L1 L2 S).ofA)
    (f112Gold L1 L2 S).ofB_injective (f112Gold L1 L2 S).ofA_injective
    (f112sa_P2'_le_P2 hF) (f112sa_P1'_le_P1 hF) hK2 hK1
    (fun y hya hyb => (f112sa_ofA_eq_ofB_of_mem_inf L1 L2 S ⟨hyb, hya⟩).symm)
    hmeet ha hb hK (le_sup_left.trans hT.le) hd he ht

theorem f112_g24LocalData_of_treeG24Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.TreeG24Data) (he : X.TreeG24Extra) (ht : X.TreeG24Transfer) :
    G24LocalData L1 L2 S :=
  f112_g24LocalData_of_g24TransferData hF h1 h2
    (f112_g24TransferData_of_treeG24Data hF h1 h2 hX0 hX1 hd he ht)

theorem f112_g24LocalData_swap_of_treeG24Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hd : X.swap.TreeG24Data) (he : X.swap.TreeG24Extra) (ht : X.swap.TreeG24Transfer) :
    G24LocalData L2 L1 S :=
  f112_g24LocalData_of_g24TransferData hF.symm h2 h1
    (f112_g24TransferData_swap_of_treeG24Data hF h1 h2 hX0 hX1 hd he ht)

theorem f112_g24_of_treeG24Data
    {L1 L2 S : Subgroup H} (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2)
    {X : Setup (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)}
    (hX0 : X.vert 0 = baseA (f112Gold L1 L2 S))
    (hX1 : X.vert 1 = baseB (f112Gold L1 L2 S))
    (hident : ∀ {L1 L2 S : Subgroup H}, F112HypW L1 L2 S → VA5 L1 → VA5 L2 →
      G24LocalData L1 L2 S → IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over 2))
    (hd : (X.TreeG24Data ∧ X.TreeG24Extra ∧ X.TreeG24Transfer) ∨
      (X.swap.TreeG24Data ∧ X.swap.TreeG24Extra ∧ X.swap.TreeG24Transfer)) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsG2Over 2) := by
  rcases hd with ⟨hd, he, ht⟩ | ⟨hd, he, ht⟩
  · exact hident hF h1 h2 (f112_g24LocalData_of_treeG24Data hF h1 h2 hX0 hX1 hd he ht)
  · exact isAmalgamOfGroup_f112Amalgam_swap
      (hident hF.symm h2 h1 (f112_g24LocalData_swap_of_treeG24Data hF h1 h2 hX0 hX1 hd he ht))

end CFSG.Quasithin.F112R.St84
