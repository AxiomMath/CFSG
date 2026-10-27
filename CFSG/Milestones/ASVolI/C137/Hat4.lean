module

public import CFSG.Milestones.ASVolI.C137.Hat2
public import CFSG.Milestones.ASVolI.C137.Hat3
public import CFSG.Quasithin.MS93.ASC134

public section

namespace CFSG.ASVolI

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.ASVolI.ChC
  CFSG.LieType.BorelTits
open CFSG.Quasithin.B3 CFSG.Quasithin.C124 CFSG.Quasithin.H13.U3 CFSG.Quasithin.H13.U3.GC137
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

section Canonical

set_option linter.unusedSectionVars false

theorem burnsideC137_hatB
    [Finite G] {X T L P M V : Subgroup G}
    (hXLT : (X : Set G) = (L : Set G) * (T : Set G)) (hT : IsSylowTwoOf T X) (hL : L ∈ cComp X)
    (hX : CharTwo X) (hH : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)))
    (hTP : T ≤ P) (hPM : P ≤ M) (hM : IsMaxSubgroupIn X M)
    (hPeq : P = M ∨ (IsHat (↥L ⧸ CFSG.pCore 2 ↥L) ↥(alternatingGroup (Fin 6)) ∧
      P.relIndex M = 3 ∧ ¬ oTwoUpper P ≤ oTwoZIn L))
    (hred : IsTwoReducedIn X V) (hVL : ⁅V, L⁆ ≠ ⊥)
    (hredU : IsTwoReducedIn X ⁅V, L⁆) (hUU : ⁅⁅V, L⁆, L⁆ = ⁅V, L⁆)
    (hCeq : X ⊓ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) = X ⊓ centralizer (V : Set G))
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G))
    (h6 : TripleA6Six (autI hredU.2.2.1 L) ⊤ (fixV (autI hredU.2.2.1 L)))
    (hirr : XMod.IsIrrSec ↥(autI hredU.2.2.1 L)
      (XMod.fixed ↥(autI hredU.2.2.1 L) (⊤ : Subgroup (IntMod ⁅V, L⁆ hredU.2.2.1)))
      (⊤ : Subgroup (IntMod ⁅V, L⁆ hredU.2.2.1)))
    (hH6 : IsHat ↥(autI hredU.2.2.1 L) ↥(alternatingGroup (Fin 6)))
    (hcomm : commV (autI hredU.2.2.1 L) = ⊤) :
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
  have hRX : pCoreOf 2 P ≤ X := (pCoreOf_le 2 P).trans hPX
  have hZ3 : Nat.card ↥(Subgroup.center ↥(autI hU L)) = 3 := hH6.2.1
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥(Subgroup.center ↥(autI hU L)), z₀ ≠ 1 := by
    by_contra hne
    push Not at hne
    have h1 : Nat.card ↥(Subgroup.center ↥(autI hU L)) = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hne a).trans (hne b).symm⟩, ⟨1⟩⟩
    omega
  have hz3 : ((z₀ : ↥(autI hU L)) : MulAut (IntMod ⁅V, L⁆ hU)) ^ 3 = 1 := by
    have h1 : z₀ ^ Nat.card ↥(Subgroup.center ↥(autI hU L)) = 1 := pow_card_eq_one'
    rw [hZ3] at h1
    have h2 := congrArg (fun x : ↥(Subgroup.center ↥(autI hU L)) =>
      ((x : ↥(autI hU L)) : MulAut (IntMod ⁅V, L⁆ hU))) h1
    simpa using h2
  have hzne : ((z₀ : ↥(autI hU L)) : MulAut (IntMod ⁅V, L⁆ hU)) ≠ 1 := fun h =>
    hz₀ (Subtype.ext (Subtype.ext h))
  have hzc : ∀ h ∈ autI hU L, h * ((z₀ : ↥(autI hU L)) : MulAut (IntMod ⁅V, L⁆ hU)) =
      ((z₀ : ↥(autI hU L)) : MulAut (IntMod ⁅V, L⁆ hU)) * h := by
    intro h hh
    have := Subgroup.mem_center_iff.1 z₀.2 ⟨h, hh⟩
    exact congrArg Subtype.val this
  have hfix : fixV (autI hU L) = ⊥ :=
    burnsideC137_fixV_eq_bot (fun w => IntMod.sq_eq_one w) hcomm hirr (z₀ : ↥(autI hU L)).2 hzc
      hz3 hzne
  have h6' : TripleA6Six (autI hU L) ⊤ ⊥ := hfix ▸ h6
  have hHM : MS93.S38H.HatMod (autI hU L) :=
    MS93.S38H.HatMod.of_tripleA6Six (fun w => IntMod.sq_eq_one w) h6'
  have hUR : ⁅V, L⁆ ≤ pCoreOf 2 P := (le_pCoreOf_of_reduced hredU).trans hQP
  have hT2 : IsPGroup 2 ↥(autI hU T) := (B2F.isSylowTwoOf_autI hU hXU hT).2.1
  obtain ⟨hJL, hF16⟩ := burnsideC137_hat_J hU hHM hUR hRT hTX hXU hn hT2 hJ
  have hSL := burnsideC137_hat_baum hU hHM hUR hRX hXU hn hJL hF16
  have hbR : baum (pCoreOf 2 P) ≤ pCoreOf 2 P := B2F.baum_le _
  have hR₀R : baum (pCoreOf 2 P) ⊔ pCoreOf 2 X ≤ pCoreOf 2 P := sup_le hbR hQP
  have hR₀X : baum (pCoreOf 2 P) ⊔ pCoreOf 2 X ≤ X := hR₀R.trans hRX
  have hQN : pCoreOf 2 X ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    (pCoreOf_le 2 X).trans hXU
  have hR₀U : autOn (baum (pCoreOf 2 P) ⊔ pCoreOf 2 X) ⁅V, L⁆ ≤ autOn L ⁅V, L⁆ := by
    change autI hU (baum (pCoreOf 2 P) ⊔ pCoreOf 2 X) ≤ autI hU L
    rw [CFSG.Quasithin.autI_sup hU (hbR.trans (hRX.trans hXU)) hQN,
      autI_eq_bot_of_le_centralizer hU (C124.pCoreOf_le_centralizer hredU), sup_bot_eq]
    exact hSL
  have hR₀V : autOn (baum (pCoreOf 2 P) ⊔ pCoreOf 2 X) V ≤ autOn L V :=
    zf_autOn_le_of_centralizer_eq hred.2.1 hXU hR₀X hLX hCeq hR₀U
  have hc := as_C_1_24 G X V T L (baum (pCoreOf 2 P) ⊔ pCoreOf 2 X) ⟨hX, hred, hT⟩ hXLT hL hL2
    hVL le_sup_right (hR₀R.trans hRT) 6 (isAltQuotient_of_hatA6 hhat)
    (Or.inr (Or.inl ⟨rfl, hR₀V⟩))
  have hbeq : baum (pCoreOf 2 P) = baum (baum (pCoreOf 2 P) ⊔ pCoreOf 2 X) :=
    baum_eq_of_le le_sup_left hR₀R
  rcases hc with ⟨D, hD0, hDle, hDchar, hDn⟩ | hchi | ⟨-, hA7⟩ | ⟨-, hA6b⟩ | ⟨-, hHb⟩
  · rw [← hbeq] at hDle hDchar
    exact Or.inl ⟨D, hD0, hDle, hDchar, hDn⟩
  · exact (burnsideC137_not_isChiBlock2_of_card hchi (Or.inr hcard)).elim
  · exact (not_isExcA7Block_of_card hA7 (Or.inr hcard)).elim
  · have h1 := card_of_isAltBlockType hA6b
    rw [hcard] at h1
    norm_num at h1
  refine Or.inr (Or.inl ⟨Or.inr (Or.inr (Or.inl hHb)), fun _ => ?_⟩)
  have hJN : thompsonJ (pCoreOf 2 P) ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    (thompsonJ_le_self _).trans (hRX.trans hXU)
  set F := fixV (autI hU (thompsonJ (pCoreOf 2 P))) with hF
  have hEU : toG hU F ≤ ⁅V, L⁆ := toG_le hU F
  have hEcard : Nat.card ↥(toG hU F) = 16 := by
    rw [show toG hU F = F.map (valHom hU) from rfl,
      Subgroup.card_map_of_injective (valHom_injective hU), hF16]
  have hE2 : IsE2 4 ↥(toG hU F) := by
    refine MS93.isE2_of_card (fun x y => Subtype.ext ?_) (fun x => Subtype.ext ?_) ?_
    · exact B2F.isElemAbelian_comm hU (hEU x.2) (hEU y.2)
    · have := hU.2 _ (hEU x.2)
      rw [sq] at this
      exact this
    · rw [hEcard]
      norm_num
  have hOL : pCoreOf 2 L ≤ centralizer ((⁅V, L⁆ : Subgroup G) : Set G) :=
    (le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLX)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)).trans
      (C124.pCoreOf_le_centralizer hredU)
  have hPJ : P ≤ normalizer (thompsonJ (pCoreOf 2 P) : Set G) :=
    (le_normalizer_pCoreOf 2 P).trans (normalizer_le_normalizer_thompsonJ _)
  have hPE : P ≤ normalizer ((toG hU F : Subgroup G) : Set G) :=
    burnsideC137_le_normalizer_toG_fixV hU (hPX.trans hXU) (autI_le_normalizer_autI_gc hU hPJ)
  have hDE : H13.A6.o2Z L ≤ normalizer ((toG hU F : Subgroup G) : Set G) :=
    burnsideC137_le_normalizer_toG_fixV hU ((o2Z_le_gc L).trans hLU) fun φ hφ =>
      Subgroup.centralizer_le_normalizer _
        (Subgroup.centralizer_le hJL (burnsideC137_autI_o2Z_le_centralizer hU hLU hOL hφ))
  have hME : M ≤ normalizer ((toG hU F : Subgroup G) : Set G) := by
    rcases hPeq with hPM' | ⟨-, h3, hO⟩
    · rw [← hPM']
      exact hPE
    · have hDM : oTwoZIn L ≤ M :=
        burnsideC137_o2Z_le_of_maximal hT hprod hL hhat.1 (hTP.trans hPM) hMX hmax
      have hDP : ¬ oTwoZIn L ≤ P := burnsideC137_not_o2Z_le hT hprod hL hH hTP hPM hMX h3 hO
      rw [← burnsideC137_sup_eq_of_index_three hPM hDM h3 hDP]
      exact sup_le hPE hDE
  have hXE : ¬ X ≤ normalizer ((toG hU F : Subgroup G) : Set G) := by
    intro hXE
    have hinv : ∀ h ∈ autI hU L, ∀ w ∈ F, h w ∈ F := by
      intro h hh w hw
      obtain ⟨l, hl, rfl⟩ := (mem_autI hU).1 hh
      rw [← mem_toG_iff_of_mem hU, convI_apply_val]
      exact (Subgroup.mem_normalizer_iff.1 (hXE (hLX hl)) w.val).1
        ((mem_toG_iff_of_mem hU w).2 hw)
    have := hHM.finite
    rcases hHM.irr F hinv with h | h
    · rw [h, Subgroup.card_bot] at hF16
      omega
    · rw [h, Subgroup.card_top, hHM.card] at hF16
      norm_num at hF16
  have hMeq : X ⊓ normalizer ((toG hU F : Subgroup G) : Set G) = M := by
    rcases hmax _ (le_inf hMX.le hME) inf_le_left with h | h
    · exact h
    · exact absurd (h.symm.le.trans inf_le_right) hXE
  exact ⟨toG hU F, hEU, hE2, by rw [hMeq]⟩

theorem burnsideC137_caseHat
    : burnsideC137_CaseHat := by
  intro G _ _ X T L P M V hyp hH
  obtain ⟨hXLT, hT, hL, hX, -, -, hTP, hPM, hM, hPeq, hred, hVL, -⟩ := hyp
  have hprod := burnsideC137_prod hXLT
  have hL2 := burnsideC137_charTwo_L hL hX
  have hLX : L ≤ X := le_of_mem_cComp hL
  have hhat := burnsideC137_isHatA6 hH
  have halt : IsAltQuotient L (oTwoZIn L) 6 := isAltQuotient_of_hatA6 hhat
  have hLq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) :=
    isQuasisimple_of_altQuotient hL halt (by norm_num)
  obtain ⟨hredU, hUU, hCeq⟩ := burnsideC137_a6_reduce hred hT hprod hL hLq hVL
  have hU : IsElemAbelian 2 ⁅V, L⁆ := hredU.2.2.1
  have hLU : L ≤ normalizer ((⁅V, L⁆ : Subgroup G) : Set G) := hLX.trans hredU.2.1
  have hUL : ⁅⁅V, L⁆, L⁆ ≠ ⊥ := by
    rw [hUU]
    exact hVL
  have hSQ : SQTKGroup ↥X :=
    c137SQTKSupply_holds G X T L hX hT hprod hL hL2 (Or.inr (Or.inr (Or.inl hhat)))
  have hPX : P ≤ X := hPM.trans hM.1.le
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
  have hirr := E.case1i.1.2.2.2
  rw [hcomm] at hirr
  rcases burnsideC137_a6_classes E hcomm with ⟨h5, -⟩ | ⟨h5, -⟩ | ⟨-, π, hπ, -⟩ | ⟨h7, -⟩ |
      ⟨-, h6, hH6⟩ | ⟨h7, -⟩
  · omega
  · omega
  · exact burnsideC137_hatA hXLT hT hL hX hH hTP hPM hM hPeq hred hVL hSQ hredU hUU hCeq hπ hirr
  · omega
  · exact burnsideC137_hatB hXLT hT hL hX hH hTP hPM hM hPeq hred hVL hredU hUU hCeq E.hJ h6
      hirr hH6 hcomm
  · omega

end Canonical

end CFSG.ASVolI
