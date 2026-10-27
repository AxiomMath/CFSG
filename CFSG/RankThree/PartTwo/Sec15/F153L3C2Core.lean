module

public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Glue
public import CFSG.RankThree.PartTwo.Sec15.F153Bridge
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Defs

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.Quasithin
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.RankThree.PartTwo.Sec15.SimsBaumann (W315 isTwoReducedIn_W315)
open CFSG.RankThree.PartTwo.Sec15.F153

theorem false_of_noOuterFFOffender_of_pushing_up {X : Type} [Group X] [Finite X] {S : Subgroup X}
    (hK : CFSG.Open.IsKGroup X)
    (hF : generalizedFitting X = CFSG.pCore 2 X)
    (hq : CFSG.IsQuasisimple ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)))
    (hS2 : IsPGroup 2 S) (hS1 : S ≠ ⊥) (hQS : CFSG.pCore 2 X ≤ S)
    (hXS : oResidual 2 X ⊔ S = ⊤)
    (hJ : ¬ CFSG.Quasithin.thompsonJ S ≤ CFSG.pCore 2 X)
    (hno : ¬ ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ S ∧ (C.subgroupOf S).Characteristic ∧ C.Normal)
    (hG : S ⊓ (oResidual 2 X ⊔ Subgroup.centralizer (W315 X : Set X)) ≤
      Subgroup.centralizer (W315 X : Set X))
    {T : Type} [Group T] (hT : NoOuterFFOffender T)
    (e : ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ⧸
      Subgroup.center ↥(oResidual 2 (X ⧸ CFSG.pCore 2 X)) ≃* T) : False := by
  have hWL := comm_W315_ne_bot hF hS2 hS1 hQS hXS hno
  have hred := isTwoReducedIn_W315 hq hWL
  have hV := hred.2.2.1
  have hJC := not_thompsonJ_le_centralizer_W315 hq hS2 hQS hXS hJ hWL
  have hVS : W315 X ≤ S := W315_le_pCore.trans hQS
  have hSN : S ≤ Subgroup.normalizer (W315 X : Set X) := fun s _ => hred.2.1 (Subgroup.mem_top s)
  obtain ⟨A, hAS, hA1, hAe, hAoff⟩ := (B2_7_of_not_le hV hVS hSN hJC).1
  obtain ⟨e'⟩ := nonempty_autOn_centerQuotientEquiv_W315 hS2 hXS hq hWL
  have hAL : A ⊓ autI hV (oResidual 2 X) = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    obtain ⟨hφA, hφL⟩ := Subgroup.mem_inf.mp hφ
    obtain ⟨g, hgS, hgφ⟩ := (mem_autI hV).1 (hAS hφA)
    obtain ⟨g', hg'L, hg'φ⟩ := (mem_autI hV).1 hφL
    have hker : convI hV (g'⁻¹ * g) = 1 := by
      rw [map_mul, map_inv, hg'φ, hgφ, inv_mul_cancel]
    have hcen : ((g'⁻¹ * g : ↥(Subgroup.normalizer (W315 X : Set X))) : X) ∈
        Subgroup.centralizer (W315 X : Set X) := (convI_eq_one_iff hV _).mp hker
    have hgmem : (g : X) ∈ oResidual 2 X ⊔ Subgroup.centralizer (W315 X : Set X) := by
      have h1 : (g : X) = (g' : X) * (((g'⁻¹ * g : ↥(Subgroup.normalizer (W315 X : Set X))) : X)) := by
        simp
      rw [h1]
      exact Subgroup.mul_mem_sup hg'L hcen
    have hgC : (g : X) ∈ Subgroup.centralizer (W315 X : Set X) :=
      hG (Subgroup.mem_inf.mpr ⟨hgS, hgmem⟩)
    have : φ = 1 := by
      rw [← hgφ]
      exact (convI_eq_one_iff hV g).mpr hgC
    rw [this]
    exact Subgroup.one_mem _
  have hlt := hT (IntMod (W315 X) hV) (fun v => IntMod.sq_eq_one v) (autI hV (⊤ : Subgroup X))
    (autI hV (oResidual 2 X)) (ffHyp_W315 hK hS2 hXS hq hWL) ⟨e'.trans e⟩ A
    (hAS.trans (autI_mono hV le_top)) hA1 hAe hAL
  exact absurd hAoff (not_le.mpr hlt)

theorem leaf_false_of_noOuterFFOffender {G : Type} [Group G] [Finite G] {Y S : Subgroup G}
    (hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S))
    (hY : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y)
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y))
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Subgroup.normalizer (Y : Set G))
    (hFF : FF153 Y S) (hno : ¬ CharNormal153 Y S)
    (hInn : ∀ n : ↥(Subgroup.normalizer (Y : Set G)), (n : G) ∈ S → rho Y n ∈ innQ Y →
      rho Y n = 1)
    {T : Type} [Group T] (hT : NoOuterFFOffender T)
    (e : (↥Y ⧸ CFSG.pCore 2 ↥Y) ⧸ Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) ≃* T) : False := by
  obtain ⟨φ⟩ := Push153.nonempty_oResidual_quotient_equiv hS2 hSY hY3
  have hF : generalizedFitting ↥(Y ⊔ S) = CFSG.pCore 2 ↥(Y ⊔ S) :=
    Push153.generalizedFitting_sup_eq hY hS2 hSY
  have hq : CFSG.IsQuasisimple ↥(oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S))) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm hYq
  have hSmap : (S.subgroupOf (Y ⊔ S)).map (Y ⊔ S).subtype = S := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_right]
  have hS2' : IsPGroup 2 ↥(S.subgroupOf (Y ⊔ S)) :=
    hS2.of_injective (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)).injective
  have hS1' : S.subgroupOf (Y ⊔ S) ≠ ⊥ := by
    intro h
    apply hFF.2
    have hSb : S = ⊥ := by
      have h2 := hSmap
      rw [h, Subgroup.map_bot] at h2
      exact h2.symm
    exact (Push153.thompsonJ_le_self S).trans (hSb.le.trans bot_le)
  have hQS' : CFSG.pCore 2 ↥(Y ⊔ S) ≤ S.subgroupOf (Y ⊔ S) := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hFF.1 ((Push153.mem_pCore_iff_mem_pCoreOf x).mp hx)
  have hXS : oResidual 2 ↥(Y ⊔ S) ⊔ S.subgroupOf (Y ⊔ S) = ⊤ := by
    rw [Push153.oResidual_sup_eq hS2 hSY hY3]
    have h := Subgroup.subgroupOf_sup (le_sup_left : Y ≤ Y ⊔ S) (le_sup_right : S ≤ Y ⊔ S)
    rw [Subgroup.subgroupOf_self] at h
    exact h.symm
  have hJ' : ¬ CFSG.Quasithin.thompsonJ (S.subgroupOf (Y ⊔ S)) ≤ CFSG.pCore 2 ↥(Y ⊔ S) := by
    intro h
    apply hFF.2
    have key : CFSG.Quasithin.thompsonJ ((S.subgroupOf (Y ⊔ S)).map (Y ⊔ S).subtype) =
        (CFSG.Quasithin.thompsonJ (S.subgroupOf (Y ⊔ S))).map (Y ⊔ S).subtype :=
      CFSG.Quasithin.thompsonJ_map_of_injective' (Y ⊔ S).subtype_injective _
    rw [hSmap] at key
    rw [key]
    exact Subgroup.map_mono h
  have hno' : ¬ ∃ C : Subgroup ↥(Y ⊔ S), C ≠ ⊥ ∧ C ≤ S.subgroupOf (Y ⊔ S) ∧
      (C.subgroupOf (S.subgroupOf (Y ⊔ S))).Characteristic ∧ C.Normal := by
    rintro ⟨C', hC'b, hC'S, hC'char, hC'n⟩
    apply hno
    unfold CharNormal153
    refine ⟨C'.map (Y ⊔ S).subtype, ?_, ?_, ?_, ?_⟩
    · intro h
      exact hC'b ((Subgroup.map_eq_bot_iff_of_injective C' (Y ⊔ S).subtype_injective).mp h)
    · exact Subgroup.map_le_iff_le_comap.mpr hC'S
    · let ι : ↥(S.subgroupOf (Y ⊔ S)) ≃* ↥S := Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ Y ⊔ S)
      have hc := CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.characteristic_map_equiv' ι hC'char
      have heq : (C'.subgroupOf (S.subgroupOf (Y ⊔ S))).map ι.toMonoidHom =
          (C'.map (Y ⊔ S).subtype).subgroupOf S := by
        ext x
        constructor
        · intro hx
          obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
          rw [← hyx]
          exact Subgroup.mem_subgroupOf.mpr
            (Subgroup.mem_map.mpr ⟨y.1, Subgroup.mem_subgroupOf.mp hy, rfl⟩)
        · intro hx
          obtain ⟨c, hc, hcx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
          have hcS : c ∈ S.subgroupOf (Y ⊔ S) := Subgroup.mem_subgroupOf.mpr (by
            have h' : (c : G) = (x : G) := hcx
            rw [h']
            exact x.2)
          exact Subgroup.mem_map.mpr ⟨⟨c, hcS⟩, Subgroup.mem_subgroupOf.mpr hc, Subtype.ext hcx⟩
      rw [heq] at hc
      exact hc
    · exact le_normalizer_map_subtype_of_normal hC'n
  have e' : ↥(oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S))) ⧸
      Subgroup.center ↥(oResidual 2 (↥(Y ⊔ S) ⧸ CFSG.pCore 2 ↥(Y ⊔ S))) ≃* T :=
    (QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)).trans e
  have hWL := comm_W315_ne_bot hF hS2' hS1' hQS' hXS hno'
  have hred := isTwoReducedIn_W315 hq hWL
  have hWn : (W315 ↥(Y ⊔ S)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hred.2.1)
  haveI hCn : (Subgroup.centralizer (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S))).Normal := inferInstance
  have hUC : Y ⊔ S ≤ Subgroup.normalizer
      (((Subgroup.centralizer (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S))).map (Y ⊔ S).subtype : Subgroup G) :
        Set G) := le_normalizer_map_subtype_of_normal hCn
  have hUY : Y ⊔ S ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hSY
  have hoRes : oResidual 2 ↥(Y ⊔ S) = Y.subgroupOf (Y ⊔ S) :=
    Push153.oResidual_sup_eq hS2 hSY hY3
  have hWC : W315 ↥(Y ⊔ S) ≤ Subgroup.centralizer (CFSG.pCore 2 ↥(Y ⊔ S) : Set ↥(Y ⊔ S)) := by
    unfold W315 CFSG.Quasithin.omegaOneCenterOf CFSG.Quasithin.omegaOneOf
    rw [Subgroup.closure_le]
    intro x hx
    exact hx.1.2
  have hnot : ¬ Y ≤ ((Subgroup.centralizer (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S))).map
      (Y ⊔ S).subtype : Subgroup G) := by
    intro hYCg
    apply hWL
    have hOC : oResidual 2 ↥(Y ⊔ S) ≤ Subgroup.centralizer (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S)) := by
      intro y' hy'
      rw [hoRes] at hy'
      obtain ⟨c, hc, hcy⟩ := Subgroup.mem_map.mp (hYCg (Subgroup.mem_subgroupOf.mp hy'))
      have : c = y' := Subtype.ext hcy
      rw [← this]
      exact hc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mpr fun y' hy' =>
      (Subgroup.mem_centralizer_iff.mp (hOC hy') w hw).symm
  have hO2 : CFSG.Open.pCoreOf 2 Y ≤ ((Subgroup.centralizer
      (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S))).map (Y ⊔ S).subtype : Subgroup G) := by
    intro x hx
    have hx' : x ∈ Y ⊓ CFSG.Open.pCoreOf 2 (Y ⊔ S) := by
      rw [Push153.inf_pCoreOf_sup_eq hSY]
      exact hx
    obtain ⟨hxY, hxU⟩ := Subgroup.mem_inf.mp hx'
    have hxP : (⟨x, Subgroup.mem_sup_left hxY⟩ : ↥(Y ⊔ S)) ∈ CFSG.pCore 2 ↥(Y ⊔ S) :=
      (Push153.mem_pCore_iff_mem_pCoreOf ⟨x, Subgroup.mem_sup_left hxY⟩).mpr hxU
    refine Subgroup.mem_map.mpr ⟨⟨x, Subgroup.mem_sup_left hxY⟩, ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun w hw =>
      (Subgroup.mem_centralizer_iff.mp (hWC hw) _ hxP).symm
  have hglue := glue_G hSY hS2 hY3 hYq
    (fun c hc => by
      obtain ⟨c', -, rfl⟩ := Subgroup.mem_map.mp hc
      exact hUY c'.2)
    (le_sup_left.trans hUC) (le_sup_right.trans hUC) hnot hO2 hInn
  have hG : S.subgroupOf (Y ⊔ S) ⊓ (oResidual 2 ↥(Y ⊔ S) ⊔
      Subgroup.centralizer (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S))) ≤
      Subgroup.centralizer (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S)) := by
    intro s' hs'
    obtain ⟨hs'S, hs'Y⟩ := Subgroup.mem_inf.mp hs'
    obtain ⟨y', hy', c', hc', hyc⟩ := Subgroup.mem_sup_of_normal_right.mp hs'Y
    have hyY : (y' : G) ∈ Y := by
      rw [hoRes] at hy'
      exact Subgroup.mem_subgroupOf.mp hy'
    have hcCg : (c' : G) ∈ ((Subgroup.centralizer (W315 ↥(Y ⊔ S) : Set ↥(Y ⊔ S))).map
        (Y ⊔ S).subtype : Subgroup G) := ⟨c', hc', rfl⟩
    have hsS : (s' : G) ∈ S := Subgroup.mem_subgroupOf.mp hs'S
    have hs_eq : (s' : G) = (y' : G) * (c' : G) := by
      rw [← hyc]
      rfl
    obtain ⟨c'', hc''C, hc''eq⟩ := Subgroup.mem_map.mp (hglue _ hsS _ hyY _ hcCg hs_eq)
    have hcs : c'' = s' := Subtype.ext hc''eq
    rw [← hcs]
    exact hc''C
  exact false_of_noOuterFFOffender_of_pushing_up hKH hF hq hS2' hS1' hQS' hXS hJ' hno' hG hT e'

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
