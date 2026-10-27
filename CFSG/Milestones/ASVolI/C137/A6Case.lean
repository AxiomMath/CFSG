module

public import CFSG.Milestones.ASVolI.C137.A6Out
public import CFSG.Quasithin.H13.GoldschmidtC137SQFinal
public import CFSG.Milestones.ASVolI.C137.A6Ent
public import CFSG.Milestones.ASVolI.C137.Cases
public import CFSG.Milestones.ASVolI.C137.Setup
public import CFSG.Quasithin.Background.C124BlkTop
public import CFSG.Quasithin.H13.GoldschmidtC137KMod4
public import CFSG.Quasithin.H13.GoldschmidtC137S6Main
public import CFSG.Quasithin.H13.GoldschmidtC137ZfRed1
public import CFSG.Quasithin.MS93.Burnside.Sp4HDesc
public import CFSG.Quasithin.MS93.MResOrd
public import CFSG.Quasithin.Vol2.Ch11SecOE2C

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits
open CFSG.Quasithin.B3 CFSG.Quasithin.C124 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

theorem burnsideC137_not_isChiBlock2_of_card {X L : Subgroup G} (h : IsChiBlock2 X L)
    (hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 ∨ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080) :
    False := by
  rcases h.2 with ⟨n, -, hn⟩ | ⟨m, hm, hmA⟩
  · exact not_isLin2Type_of_card hn hc
  · rcases (by obtain ⟨j, rfl⟩ := hm; omega : m = 1 ∨ 3 ≤ m) with rfl | h3
    · obtain ⟨α, hα, hker, -⟩ := hmA
      have h1 := card_quot_of_surj α hα hker
      have h2 : Nat.card (alternatingGroup (Fin 1)) = 1 :=
        Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩, ⟨1⟩⟩
      omega
    · exact not_isAltType_of_card hm h3 hmA hc

section Canonical

set_option linter.unusedSectionVars false


theorem burnsideC137_a6_inner
    [Finite G] {X T L P M V : Subgroup G}
    (hXLT : (X : Set G) = (L : Set G) * (T : Set G)) (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X)
    (hX : CharTwo X) (hA6 : IsAlt 6 (↥L ⧸ CFSG.pCore 2 ↥L)) (hTP : T ≤ P) (hPX : P ≤ X)
    (hred : IsTwoReducedIn X V) (hVL : ⁅V, L⁆ ≠ ⊥) (hin : autOn T V ≤ autOn L V) :
    burnsideC137_Concl G X T L P V M := by
  have hL2 := burnsideC137_charTwo_L hL hX
  have halt : IsAltQuotient L (oTwoZIn L) 6 := isAltQuotient_of_a6 hA6
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  have hQP : pCoreOf 2 X ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans hTP)
      (hPX.trans (le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  have hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
    have h3 := Subgroup.relIndex_mul_relIndex T P X hTP hPX
    have h4 : 2 ∣ T.relIndex X := by
      rw [← h3]
      exact Dvd.dvd.mul_right h2 _
    exact hT.2.2 h4
  have hRT : pCoreOf 2 P ≤ T := pCoreOf_two_le_of_sylowIn hTP hT.2.1 hTodd
  have hRL : autOn (pCoreOf 2 P) V ≤ autOn L V := (autI_mono hred.2.2.1 hRT).trans hin
  have hc := as_C_1_24 G X V T L (pCoreOf 2 P) ⟨hX, hred, hT⟩ hXLT hL hL2 hVL hQP hRT 6 halt
    (Or.inr (Or.inl ⟨rfl, hRL⟩))
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := card_of_a6 hA6
  rcases hc with h1 | hchi | ⟨-, hA7⟩ | ⟨-, hA6b⟩ | ⟨-, hH⟩
  · exact Or.inl h1
  · exact (burnsideC137_not_isChiBlock2_of_card hchi (Or.inl hcard)).elim
  · exact (not_isExcA7Block_of_card hA7 (Or.inl hcard)).elim
  · refine Or.inr (Or.inl ⟨Or.inr (Or.inl hA6b), fun hH => ?_⟩)
    exact (not_hatA6_of_a6 hA6 ⟨hH.2.1.1.1, hH.2.1.2.1, hH.2.1.2.2⟩).elim
  · exact (not_hatA6_of_a6 hA6 ⟨hH.2.1.1.1, hH.2.1.2.1, hH.2.1.2.2⟩).elim

theorem burnsideC137_card_autI_dvd
    [Finite G] {X L U : Subgroup G} (hU : IsElemAbelian 2 U)
    (hred : IsTwoReducedIn X U) (hLX : L ≤ X) (hn : X ≤ normalizer (L : Set G)) :
    Nat.card ↥(autI hU L) ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hLU : L ≤ normalizer (U : Set G) := hLX.trans hred.2.1
  have hOL : pCoreOf 2 L ≤ L ⊓ centralizer (U : Set G) :=
    le_inf (pCoreOf_le 2 L) ((le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)).trans
      (C124.pCoreOf_le_centralizer hred))
  have h2 : (pCoreOf 2 L).relIndex L = Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    have hR : (pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L :=
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective L) _
    rw [Subgroup.relIndex, hR, Subgroup.index_eq_card]
  have h1 : Nat.card ↥(autI hU L) = (L ⊓ centralizer (U : Set G)).relIndex L :=
    card_autOn_eq_relIndex hLU
  rw [h1, ← h2]
  exact Subgroup.relIndex_dvd_of_le_left L hOL

theorem burnsideC137_caseA6
    : burnsideC137_CaseA6 := by
  intro G _ _ X T L P M V hyp hA6
  obtain ⟨hXLT, hT, hL, hX, -, -, hTP, hPM, hM, hPeq, hred, hVL, -⟩ := hyp
  have hPX : P ≤ X := hPM.trans hM.1.le
  by_cases hin : autOn T V ≤ autOn L V
  · exact burnsideC137_a6_inner hXLT hT hL hX hA6 hTP hPX hred hVL hin
  have hprod := burnsideC137_prod hXLT
  have hL2 := burnsideC137_charTwo_L hL hX
  obtain ⟨hMX, hmax⟩ := burnsideC137_max hM
  have hhat : ¬ IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) := fun hH =>
    not_hatA6_of_a6 hA6 ⟨hH.1.1, hH.2.1, hH.2.2⟩
  have hP : P = M := hPeq.resolve_right fun h => hhat h.1
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hL
  have halt : IsAltQuotient L (oTwoZIn L) 6 := isAltQuotient_of_a6 hA6
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_altQuotient hL halt (by norm_num)
  obtain ⟨hredU, hUU, hCeq⟩ := burnsideC137_a6_reduce hred hT hprod hL hLq hVL
  have hU : IsElemAbelian 2 ⁅V, L⁆ := hredU.2.2.1
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hredU.2.1
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hXU
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLX.trans hred.2.1)
  have hUL : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
    rw [hUU]
    exact hVL
  have hTX : T ≤ X := hT.1
  have hninU : ¬ autOn T ⁅V, L⁆ ≤ autOn L ⁅V, L⁆ :=
    zf_not_autOn_le_of_centralizer_eq hred.2.1 hXU hTX hLX hCeq hin
  have hSQ : SQTKGroup ↥X :=
    c137SQTKSupply_holds G X T L hX hT hprod hL hL2 (Or.inr (Or.inl hA6))
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn hT.1 hT.2.1 hT.2.2
  have hQP : pCoreOf 2 X ≤ pCoreOf 2 P :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans hTP)
      (hPX.trans (le_normalizer_pCoreOf 2 X)) (pCoreOf_isPGroup 2 X)
  have hTodd : ¬ 2 ∣ T.relIndex P := fun h2 => by
    have h3 := Subgroup.relIndex_mul_relIndex T P X hTP hPX
    have h4 : 2 ∣ T.relIndex X := by
      rw [← h3]
      exact Dvd.dvd.mul_right h2 _
    exact hT.2.2 h4
  have hRT : pCoreOf 2 P ≤ T := pCoreOf_two_le_of_sylowIn hTP hT.2.1 hTodd
  rcases burnsideC137_a6_entry_or_concl1 hSQ hredU hT hprod hL hUL halt hQP hRT with
    ⟨C, hC0, hCle, hCchar, hCn⟩ | E
  · exact Or.inl ⟨C, hC0, hCle, hCchar, hCn⟩
  have hcomm : commV (autI hU L) = ⊤ := C124.commV_autI_eq_top hU hLU hUU
  rcases burnsideC137_a6_classes E hcomm with ⟨h5, -⟩ | ⟨h5, -⟩ | ⟨-, π, hπ, -⟩ | ⟨h7, -⟩ |
      ⟨-, -, hH⟩ | ⟨h7, -⟩
  · omega
  · omega
  ·
    have hnat := burnsideC137_natural_of_realizes hU hLU hπ
    obtain ⟨k, hk, ⟨N⟩⟩ := model_of_Z hU hU hLU hLU hUU hUU hnat
    have hctx : S6Ctx X T ⁅V, L⁆ L P M :=
      { hX := hX, hSQ := hSQ, hT := hT, hprod := hprod, hL := hL, hL2 := hL2, hA6 := hA6,
        hnin := hninU, hTP := hTP, hPM := hPM, hMX := hMX, hmax := hmax, hPeq := hP,
        hred := hredU, hVL := hUL, hmod := ⟨k, hk, ⟨N⟩⟩ }
    have hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32 :=
      MS93.MRes.asC132_of_descSp4 MS93.S4L.burnsideSp4H_s34RDescSp4
    have hXeq := hctx.autI_X_eq N
    rcases s6_concl (C124.c124StatementSQTK_holds G) hC132 hctx with
      ⟨C, hCle, hC0, hCchar, hCn⟩ | hB | ⟨h12096, -⟩ | ⟨-, hl, -, hA⟩
    · exact Or.inl ⟨C, hC0, hCle, hCchar, hCn⟩
    · refine Or.inr (Or.inl ⟨Or.inr (Or.inl
        (Vol2.Ch11.OE2.isAltBlockType_of_isA6Block (hB.2.1 hA6))), fun hH => ?_⟩)
      exact (hhat hH.2.1).elim
    · exfalso
      have h720 : Nat.card ↥(autI hU X) = 720 := by
        rw [← hXeq, Subgroup.card_map_of_injective N.ρ_inj, Subgroup.card_top, Nat.card_perm,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
      have h720' : Nat.card ↥(autOn X ⁅V, L⁆) = 720 := h720
      omega
    · have hirr := E.case1i.1.2.2.2
      rw [hcomm] at hirr
      have hPl : ∀ l : Subgroup G, P ≤ normalizer (l : Set G) → ¬ X ≤ normalizer (l : Set G) →
          autOn P V = autOn (X ⊓ normalizer (l : Set G)) V := by
        intro l hPl hXl
        have hMl : M ≤ X ⊓ normalizer (l : Set G) := by
          rw [← hP]
          exact le_inf hPX hPl
        rcases hmax (X ⊓ normalizer (l : Set G)) hMl inf_le_left with h1 | h1
        · rw [h1, hP]
        · exact (hXl (h1.symm.le.trans inf_le_right)).elim
      exact Or.inr (Or.inr (Or.inr (Or.inr (burnsideC137_concl5_of hred.2.2.1 hred.2.1 hU hUV
        hXU hn hLX hTX hCeq hk N hXeq hirr hPl ⟨hl, fun hH => (hhat hH).elim, hA⟩))))
  · omega
  ·
    exfalso
    obtain ⟨-, h3, ⟨e⟩⟩ := hH
    have hA360 : Nat.card ↥(alternatingGroup (Fin 6)) = 360 := by
      obtain ⟨eA⟩ := hA6
      rw [← Nat.card_congr eA.toEquiv]
      exact card_of_a6 ⟨eA⟩
    have h1 : Nat.card ↥(autI hU L) = 1080 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(autI hU L)), h3,
        Nat.card_congr e.toEquiv, hA360]
    have h2 := burnsideC137_card_autI_dvd hU hredU hLX hn
    rw [h1, card_of_a6 hA6] at h2
    exact absurd h2 (by norm_num)
  · omega

end Canonical

end CFSG.ASVolI
