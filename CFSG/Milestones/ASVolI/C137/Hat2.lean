module

public import CFSG.Milestones.ASVolI.C137.Hat1
public import CFSG.Milestones.ASVolI.C137.A6Case
public import CFSG.Quasithin.H13.GoldschmidtC137H6CaseI
public import CFSG.Quasithin.H13.GoldschmidtC137H6Two

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits
open CFSG.Quasithin.B3 CFSG.Quasithin.C124 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

section Canonical

set_option linter.unusedSectionVars false

theorem burnsideC137_hatA
    [Finite G] {X T L P M V : Subgroup G}
    (hXLT : (X : Set G) = (L : Set G) * (T : Set G)) (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X)
    (hX : CharTwo X) (hH : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)))
    (hTP : T ≤ P) (hPM : P ≤ M) (hM : IsMaxSubgroupIn X M)
    (hPeq : P = M ∨ (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) ∧
      P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ oTwoZIn L))
    (hred : IsTwoReducedIn X V) (hVL : ⁅V, L⁆ ≠ ⊥) (hSQ : SQTKGroup ↥X)
    (hredU : IsTwoReducedIn X ⁅V, L⁆) (hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆)
    (hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G))
    {π : ↥(alternatingGroup (Fin 6)) →* ↥(autI hredU.2.2.1 L)}
    (hπ : (FFModel.altDn 6).RealizesVia (autI hredU.2.2.1 L) ⊤ (fixV (autI hredU.2.2.1 L)) π)
    (hirr : XMod.IsIrrSec ↥(autI hredU.2.2.1 L)
      (XMod.fixed ↥(autI hredU.2.2.1 L) (⊤ : Subgroup (IntMod ⁅V, L⁆ hredU.2.2.1)))
      (⊤ : Subgroup (IntMod ⁅V, L⁆ hredU.2.2.1))) :
    burnsideC137_Concl G X T L P V M := by
  have hprod := burnsideC137_prod hXLT
  have hL2 := burnsideC137_charTwo_L hL hX
  obtain ⟨hMX, hmax⟩ := burnsideC137_max hM
  have hPX : P ≤ X := hPM.trans hMX.le
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hn : X ≤ normalizer (L : Set G) := le_normalizer_of_prod hT hprod hL
  have hTX : T ≤ X := hT.1
  have hhat := burnsideC137_isHatA6 hH
  have hcard : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 1080 := card_of_hatA6 hhat
  have hU : IsElemAbelian 2 ⁅V, L⁆ := hredU.2.2.1
  have hXU : X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hredU.2.1
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hXU
  have hUV : ⁅V, L⁆ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.mp (hLX.trans hred.2.1)
  have hUL : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
    rw [hUU]
    exact hVL
  have h360 : Nat.card ↥(autI hU L) = 360 := by
    rw [card_eq_of_faithful (FFC.altDn_faithful (by norm_num)) hπ]
    exact burnsideC137_card_alt6
  have hnoB : ¬ IsHatA6Block L := fun hB => by
    have h1 := burnsideC137_card_autI_of_hatBlock hred hLX hn hUU hVL hU hB
    rw [h360, hcard] at h1
    norm_num at h1
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
  have hC124 := C124.c124StatementSQTK_holds G
  by_cases hin : autOn T V ≤ autOn L V
  ·
    have hRL : autOn (pCoreOf 2 P) V ≤ autOn L V := (autI_mono hred.2.2.1 hRT).trans hin
    have hc := as_C_1_24 G X V T L (pCoreOf 2 P) ⟨hX, hred, hT⟩ hXLT hL hL2 hVL hQP hRT 6
      (isAltQuotient_of_hatA6 hhat) (Or.inr (Or.inl ⟨rfl, hRL⟩))
    rcases hc with h1 | hchi | ⟨-, hA7⟩ | ⟨-, hA6b⟩ | ⟨-, hHb⟩
    · exact Or.inl h1
    · exact (burnsideC137_not_isChiBlock2_of_card hchi (Or.inr hcard)).elim
    · exact (not_isExcA7Block_of_card hA7 (Or.inr hcard)).elim
    · have h1 := card_of_isAltBlockType hA6b
      rw [hcard] at h1
      norm_num at h1
    · exact (hnoB hHb).elim
  have hninU : ¬ autOn T ⁅V, L⁆ ≤ autOn L ⁅V, L⁆ :=
    zf_not_autOn_le_of_centralizer_eq hred.2.1 hXU hTX hLX hCeq hin
  have hnat := burnsideC137_natural_of_realizes hU hLU hπ
  obtain ⟨k, hk, ⟨N⟩⟩ := model_of_Z hU hU hLU hLU hUU hUU hnat
  have hctx : H6Ctx X T ⁅V, L⁆ L P :=
    { hX := hX, hSQ := hSQ, hT := hT, hprod := hprod, hL := hL, hL2 := hL2, hhat := hhat,
      hnin := hninU, hTP := hTP, hPX := lt_of_le_of_lt hPM hMX, hred := hredU, hVL := hUL,
      hmod := ⟨k, hk, ⟨N⟩⟩ }
  have hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32 :=
    MS93.MRes.asC132_of_descSp4 MS93.S4L.burnsideSp4H_s34RDescSp4
  have hXeq := hctx.autI_X_eq N
  have h720 : Nat.card ↥(autOn X ⁅V, L⁆) = 720 := by
    change Nat.card ↥(autI hU X) = 720
    rw [← hXeq, Subgroup.card_map_of_injective N.ρ_inj, Subgroup.card_top, Nat.card_perm,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  have hB2 : ¬ BlockPart L := fun hB => hnoB (Vol2.Ch11.OE2.isHatA6Block_of (hB.2.2.1 hhat))
  by_cases hDP : H13.A6.o2Z L ≤ P
  · rcases concl_caseI hC124 hctx hDP with ⟨C, hCle, hC0, hCchar, hCn⟩ | hB | ⟨h12096, -⟩ |
        ⟨-, -, hZ, -⟩
    · exact Or.inl ⟨C, hC0, hCle, hCchar, hCn⟩
    · exact (hB2 hB).elim
    · omega
    · exact ((hZ hhat) ((oTwoUpper_le _).trans hDP)).elim
  have hDM : H13.A6.o2Z L ≤ M := by
    have := hctx.D_le_of_maximal (hTP.trans hPM) hMX hmax
    rwa [hctx.D_eq_o2Z] at this
  have h3 : P.relIndex M = 3 := by
    rcases hPeq with hPM' | ⟨-, h3, -⟩
    · exact absurd (hPM' ▸ hDM) hDP
    · exact h3
  have hsup : P ⊔ H13.A6.o2Z L = M := burnsideC137_sup_eq_of_index_three hPM hDM h3 hDP
  have hDC : H13.A6.o2Z L ≤ centralizer (V : Set G) := by
    intro d hd
    have h1 : d ∈ X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
      ⟨hDM.trans hMX.le hd, (hctx.o2Z_le_D hd).2⟩
    rw [hCeq] at h1
    exact h1.2
  have hDCU : H13.A6.o2Z L ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) := fun d hd =>
    (hctx.o2Z_le_D hd).2
  rcases concl_caseII hC124 hC132 hctx hPM hMX hmax h3 hDP with ⟨C, hCle, hC0, hCchar, hCn⟩ |
      hB | ⟨h12096, -⟩ | ⟨-, hl, hZ, hA⟩
  · exact Or.inl ⟨C, hC0, hCle, hCchar, hCn⟩
  · exact (hB2 hB).elim
  · omega
  · have hPN : P ≤ normalizer (V : Set G) := hPX.trans hred.2.1
    have hDN : H13.A6.o2Z L ≤ normalizer (V : Set G) := hDM.trans (hMX.le.trans hred.2.1)
    have hautM : autOn M V = autOn P V := by
      change autI hred.2.2.1 M = autI hred.2.2.1 P
      rw [← hsup, CFSG.Quasithin.autI_sup hred.2.2.1 hPN hDN,
        autI_eq_bot_of_le_centralizer hred.2.2.1 hDC, sup_bot_eq]
    have hPl : ∀ l : Subgroup G, ⁅V, L⁆ ⊓ centralizer (L : Set G) ≤ l → l ≤ ⁅V, L⁆ →
        P ≤ normalizer (l : Set G) → ¬ X ≤ normalizer (l : Set G) →
        autOn P V = autOn (X ⊓ normalizer (l : Set G)) V := by
      intro l _ hlU hPl hXl
      have hDl : H13.A6.o2Z L ≤ normalizer (l : Set G) := burnsideC137_le_normalizer_of_le hDCU hlU
      have hMl : M ≤ X ⊓ normalizer (l : Set G) := by
        rw [← hsup]
        exact sup_le (le_inf hPX hPl) (le_inf (hDM.trans hMX.le) hDl)
      rcases hmax _ hMl inf_le_left with h1 | h1
      · rw [h1, hautM]
      · exact (hXl (h1.symm.le.trans inf_le_right)).elim
    exact Or.inr (Or.inr (Or.inr (Or.inr (burnsideC137_concl5_of_le hred.2.2.1 hred.2.1 hU hUV
      hXU hn hLX hTX hCeq hk N hXeq hirr hPl
      ⟨hl, fun hH' => hZ (burnsideC137_isHatA6 hH'), hA⟩))))

end Canonical

end CFSG.ASVolI
