module

public import CFSG.Quasithin.H13.GoldschmidtC137L32Core
public import CFSG.Quasithin.H13.GoldschmidtC137L32ZFinW
public import CFSG.Quasithin.H13.GoldschmidtC137BaumMain
public import CFSG.Quasithin.H13.GoldschmidtC137Cases
public import CFSG.Quasithin.H13.GoldschmidtC137L32DE
public import CFSG.Quasithin.H13.GoldschmidtC137L32Lie
public import CFSG.Quasithin.H13.GoldschmidtC137MSd

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint
open CFSG.Quasithin.H13.U3

variable {G : Type} [Group G]

theorem l32_core_finalW [Finite G] {X T L P W : Subgroup G} {u : G} (hSQ : SQTKGroup ↥X)
    (hL2 : CharTwo L) (h : L32Ctx X T L P W u) (hC134 : C134L32CorrM) :
    CharNormal (baum (pCoreOf 2 P)) X ∨ BlockPart L := by
  by_cases hCN : CharNormal (baum (pCoreOf 2 P)) X
  · exact Or.inl hCN
  right
  set R := pCoreOf 2 P with hR
  set S := baum R with hS
  have hn1 : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ → (C.subgroupOf S).Characteristic →
      ¬ X ≤ normalizer (C : Set G) := fun C hCS hC0 hCc hCn => hCN ⟨C, hCS, hC0, hCc, hCn⟩
  have hM8 : Nat.card (IntMod W h.hWe) = 8 := h.hW8
  obtain ⟨φ⟩ := S153E58.nonempty_mulEquiv_pi_of_sq_eq_one
    (fun m : IntMod W h.hWe => IntMod.sq_eq_one m) (d := 3) (by rw [hM8]; norm_num)
  have hW1 : W ≠ ⊥ := by
    intro hb
    have h8 := h.hW8
    have h1 : Nat.card W = 1 := by rw [hb]; exact Subgroup.card_bot
    omega
  have hVL : ⁅W, L⁆ ≠ ⊥ := by rw [h.hWL]; exact hW1
  obtain ⟨-, -, -, hdich⟩ := C124.B2_10_2 h.hWe h.hred h.hQR h.hRT h.hT h.hLX h.hn h.hprod hVL
    (Or.inl (isQuasisimple_L32 h.lie))
  rcases hdich with hbq | ⟨hst, -⟩
  · exact absurd (charNormal_of_baum_eq (X := X) (R := R) (Q := pCoreOf 2 X)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
      ⟨W, C124.le_pCoreOf_of_reduced h.hred, h.hWe, hW1⟩ hbq) hCN
  obtain ⟨A₀, hA₀, hc⟩ := h.exists_offender_order_two φ hst
  have hRne : autI h.hWe R ≠ ⊥ := by
    intro hb
    have : autI h.hWe A₀ ≤ ⊥ := hb ▸ autI_mono h.hWe hA₀.1
    rw [le_bot_iff] at this
    rw [this, Subgroup.card_bot] at hc
    omega
  have hRv := h.autI_R_eq_v4M φ hRne
  have hJne : autI h.hWe (thompsonJ R) ≠ ⊥ := by
    intro hb
    have : autI h.hWe A₀ ≤ ⊥ := hb ▸ autI_mono h.hWe (le_iSup₂_of_le A₀ hA₀ le_rfl)
    rw [le_bot_iff] at this
    rw [this, Subgroup.card_bot] at hc
    omega
  have hJnorm : ∀ p ∈ P, ∀ y ∈ thompsonJ R, p * y * p⁻¹ ∈ thompsonJ R := by
    intro p hp y hy
    have hpn : p⁻¹ ∈ normalizer (R : Set G) :=
      Subgroup.inv_mem _ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hp)
    have := hy
    rw [← cjSub_thompsonJ hpn, mem_cjSub] at this
    simpa using this
  have hJv := h.autI_eq_v4M_of_normal φ (thompsonJ_le_self R) hJnorm hJne
  have hRS : autI h.hWe R ≤ autI h.hWe S := by
    rw [hRv, ← hJv]
    exact autI_mono h.hWe (B2F.thompsonJ_le_baum R)
  have hRX : R ≤ X := (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans h.hPX.le
  obtain ⟨hCV, -⟩ := b2_19_rel h.hWe h.hred.1 h.hXN h.hLeq.symm (isPGroup_pCoreOf_two_gc P) hRX
    h.hWR h.hA1 h.hA2 h.hA3 h.hB (h.hC φ) (h.hDE φ hA₀ hc)
  obtain ⟨hMS, hLcomp, hset⟩ := isMSPair_of_baumann hSQ h.hT h.hprod h.hL hL2 h.hn h.hTP h.hPX
    h.hXN (isRankTwoLie2Derived_L32 h.lie) hn1 hCV hRS
  obtain ⟨α, hα⟩ := exists_modO2Surj_L32 h.lie
  obtain ⟨i, hi⟩ := hC134 G (L ⊔ S) S L hMS hLcomp hset
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩
  obtain ⟨hHlt, hHodd, hSeq⟩ := msA_of_baumann h.hT h.hprod h.hL h.hn h.hTP h.hPX h.hXN hCV hRS
  set H' := P ⊓ (L ⊔ S) with hH'
  obtain ⟨S', hS'⟩ := exists_isSylowTwoOf H'
  have hSS' : S ≤ S' :=
    hSeq.le.trans (pCoreOf_two_le_of_sylowIn hS'.1 hS'.2.1 hS'.2.2)
  have hH'G : H' ≤ L ⊔ S := inf_le_right
  have hH'P : H' ≤ P := inf_le_left
  have hS'G : IsSylowTwoOf S' (L ⊔ S) := by
    refine ⟨hS'.1.trans hH'G, hS'.2.1, fun h2 => ?_⟩
    have h1 := Subgroup.relIndex_mul_relIndex S' H' (L ⊔ S) hS'.1 hH'G
    have h3 : 2 ∣ S'.relIndex H' * H'.relIndex (L ⊔ S) := by rw [h1]; exact h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h3 with h4 | h4
    · exact hS'.2.2 h4
    · exact hHodd h4
  have hLSX : L ⊔ S ≤ X := sup_le h.hLX (((inf_le_left : S ≤ R).trans
    (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).trans h.hPX.le)
  have hWL' : W ≤ L := by
    rw [← h.hWL]
    refine Subgroup.commutator_le.2 fun w hw l hl => ?_
    have h1 : w * l * w⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (h.hn (h.hred.1 hw)) l).1 hl
    have : w * l * w⁻¹ * l⁻¹ ∈ L := L.mul_mem h1 (L.inv_mem hl)
    simpa [commutatorElement_def] using this
  have hWO : W ≤ pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hWL' (h.hLX.trans h.hXN)
      (B2F.isPGroup_of_isElemAbelian h.hWe)
  have hSnOL : S ≤ normalizer ((pCoreOf 2 L : Subgroup G) : Set G) :=
    (((inf_le_left : S ≤ R).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).trans h.hPX.le).trans
      (h.hn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
  have hOLG : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) hSnOL)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  have hOGS' : pCoreOf 2 (L ⊔ S) ≤ S' :=
    pCoreOf_two_le_of_sylowIn hS'G.1 hS'G.2.1 hS'G.2.2
  have huS' : u ∈ S' := hOGS' (hOLG (hWO h.huW))
  have huC : u ∈ centralizer (S' : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have := h.hpu (hH'P (hS'.1 hs))
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [this]
  have hu2 : u ^ 2 = 1 := h.hWe.2 u h.huW
  have huΩ : u ∈ omegaOneCenterOf S' :=
    Subgroup.subset_closure ⟨⟨huS', huC⟩, hu2⟩
  have hCT : CharTwo (L ⊔ S) := hMS.1.2.1
  have hSP : S ≤ P := (inf_le_left : S ≤ R).trans (CFSG.LieType.BorelTits.pCoreOf_le 2 P)
  have hZeq : (2 ≤ i ∧ i ≤ 4) →
      S = pCoreOf 2 ((L ⊔ S) ⊓ centralizer (omegaOneCenterOf S' : Set G)) := by
    intro hi24
    have hCH : (L ⊔ S) ⊓ centralizer (omegaOneCenterOf S' : Set G) = H' := by
      apply le_antisymm
      · intro x hx
        have hcu : x ∈ centralizer ({u} : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          rw [Set.mem_singleton_iff] at hz
          rw [hz]
          exact Subgroup.mem_centralizer_iff.1 hx.2 u huΩ
        refine ⟨?_, hx.1⟩
        rw [h.hP]
        exact ⟨hLSX hx.1, hcu⟩
      · intro x hx
        have hxc : x ∈ centralizer (omegaOneCenterOf S' : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact (l32_zcentralW h hSP hCT hset hS' hS'G hSS' hi hi24.1 hi24.2 hz x hx).symm
        exact ⟨hH'G hx, hxc⟩
    rw [hCH]
    exact hSeq
  rcases i with _ | _ | _ | _ | _ | _ | i
  · exact (hi : False).elim
  · exact blockPart_of_psl32 h.lie (isLnBlock_of_isSL3Block (card_of_psl32 h.lie) hi.1)
  · exact absurd (hZeq ⟨by norm_num, by norm_num⟩) (hi.2 S' hS'G hSS')
  · exact absurd (hZeq ⟨by norm_num, by norm_num⟩) (hi.2 S' hS'G hSS')
  · exact absurd (hZeq ⟨by norm_num, by norm_num⟩) (hi.2 S' hS'G hSS')
  · exfalso
    have hz := (hi.2 S' hS'G hSS').1 huΩ
    have hcomm : ∀ l ∈ L, l * u = u * l := fun l hl =>
      Subgroup.mem_centralizer_iff.1 hz.2 l ((le_sup_left : L ≤ L ⊔ S) hl)
    have hfix : h.uM ∈ fixV (autI h.hWe L) := by
      intro a ha
      obtain ⟨l, hlL, rfl⟩ := (mem_autI h.hWe).1 ha
      apply IntMod.val_injective
      rw [convI_apply_val]
      show (l : G) * u * (l : G)⁻¹ = u
      rw [hcomm l hlL]
      group
    rw [h.autI_L_top, fixV_top φ, Subgroup.mem_bot] at hfix
    exact h.uM_ne_one hfix
  · exact (hi : False).elim

theorem c137CaseL32_finalW (hC134 : C134L32CorrM) : C137CaseL32 := by
  intro G _ _ X T V L P M hX hSQ hT hprod hL hL2 hlie hTP hPM hMX hmax hPeq hred hVL h8 hu
  obtain ⟨u, huW, hu1, hP⟩ := hu
  have hn := C124.le_normalizer_of_prod hT hprod hL
  obtain ⟨hWX, hXW, hWe, hWL, hred'⟩ := l32_reduce hL hlie hn hred h8
  have ctx : L32Ctx X T L P ⁅V, L⁆ u :=
    ⟨hT, hprod, hL, hlie, hTP, lt_of_le_of_lt hPM hMX, hred', hWL, h8, huW, hu1, hP⟩
  rcases l32_core_finalW hSQ hL2 ctx hC134 with h1 | h2
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)

end CFSG.Quasithin.H13.U3.GC137
