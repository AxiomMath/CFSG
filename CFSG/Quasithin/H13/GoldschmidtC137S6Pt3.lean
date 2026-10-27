module

public import CFSG.Quasithin.H13.GoldschmidtC137CPt3
public import CFSG.Quasithin.H13.GoldschmidtC137S6Pt2
public import CFSG.Quasithin.H13.GoldschmidtC137S6Blk
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.H13.GoldschmidtC137S6Dict
public import CFSG.Quasithin.H13.GoldschmidtC137S6Pt1

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]


theorem charNormal_of_baum_eq_gc [Finite G] {X R Q : Subgroup G}
    (hXQ : X ≤ normalizer (Q : Set G)) (hE : ∃ E ≤ Q, IsElemAbelian 2 E ∧ E ≠ ⊥)
    (h : baum R = baum Q) : CharNormal (baum R) X := by
  refine ⟨baum R, le_rfl, ?_, ?_, ?_⟩
  · obtain ⟨E, hEQ, hE2, hE0⟩ := hE
    obtain ⟨A, hA⟩ := exists_isMaxElemAbelian Q
    have hE1 : 1 < Nat.card E := (Subgroup.one_lt_card_iff_ne_bot _).2 hE0
    have hAE : Nat.card E ≤ Nat.card A := hA.2.2 E hEQ hE2
    have hA0 : A ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at hAE
      omega
    intro hb
    apply hA0
    rw [h] at hb
    exact le_bot_iff.1 (hb ▸ (le_iSup₂_of_le A hA le_rfl).trans (B2F.thompsonJ_le_baum Q))
  · rw [Subgroup.subgroupOf_self]
    infer_instance
  · rw [h]
    exact hXQ.trans (normalizer_le_normalizer_baum Q)

theorem not_J_le_of_conjIn_nonempty [Finite G] {X R V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hXN : X ≤ normalizer (V : Set G))
    (hne : (C124.offenderImagesConjIn hV X R).Nonempty) :
    ¬ thompsonJ R ≤ centralizer (V : Set G) := by
  obtain ⟨B, hB0, A, rfl, g, hg, hgA⟩ := hne
  intro hJ
  apply hB0
  have h1 : cjSub g⁻¹ A ≤ centralizer (V : Set G) :=
    (le_iSup₂_of_le _ hgA le_rfl : cjSub g⁻¹ A ≤ thompsonJ R).trans hJ
  have h2 : cjSub g (cjSub g⁻¹ A) ≤ centralizer (V : Set G) :=
    cjSub_le (B2F.normalizer_le_normalizer_centralizer V (hXN hg)) h1
  rw [cjSub_cjSub_inv] at h2
  exact autI_eq_bot_of_le_centralizer hV h2

theorem c124_tail_a6 [Finite G] {X L S R₀ : Subgroup G} (hS : S = baum R₀)
    (ht : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hcl : (∃ C : Subgroup G, C ≠ ⊥ ∧ C ≤ baum R₀ ∧ (C.subgroupOf (baum R₀)).Characteristic ∧
        X ≤ normalizer (C : Set G)) ∨ CFSG.Quasithin.IsChiBlock X L ∨
      (CFSG.QuasithinUnique.IsBlock2 X L ∧ (CFSG.Quasithin.IsExcA7Block L ∨
        CFSG.Quasithin.IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L))) :
    CharNormal S X ∨ BlockPart L := by
  rcases hcl with ⟨C, hC1, hC2, hC3, hC4⟩ | hchi | ⟨-, hA7 | hA6 | hH⟩
  · left
    rw [hS]
    exact ⟨C, hC2, hC1, hC3, hC4⟩
  · exact (not_isChiBlock_of_card hchi (Or.inl (card_of_a6 ht))).elim
  · exact (not_isExcA7Block_of_card hA7 (Or.inl (card_of_a6 ht))).elim
  · exact Or.inr (blockPart_of_a6 ht (isA6Block_of_isAltBlockType hA6))
  · have h1 : A6.IsHatA6 L := ⟨hH.2.1.1.1, hH.2.1.2.1, hH.2.1.2.2⟩
    have h2 := card_of_hatA6 h1
    rw [card_of_a6 ht] at h2
    omega

namespace S6Frame

variable [Finite G] {X T V L P M : Subgroup G} {h : S6Ctx X T V L P M} (F : S6Frame h)

theorem autI_baum_eq_Z1 (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ1 : autI h.hVe (thompsonJ (pCoreOf 2 P)) = Z1.map F.ρ) :
    autI h.hVe (baum (pCoreOf 2 P)) = Z1.map F.ρ :=
  F.toC137B.autI_baum_eq_Z1 hR hJ1

theorem point_a_concl (hC124 : C124StatementSQTK (G := G))
    (hCN : ¬ CharNormal (baum (pCoreOf 2 P)) X) (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ1 : autI h.hVe (thompsonJ (pCoreOf 2 P)) = Z1.map F.ρ) : BlockPart L := by
  set R := pCoreOf 2 P with hRdef
  have hSstar := F.autI_baum_eq_Z1 hR hJ1
  have hQT : pCoreOf 2 X ≤ T := pCoreOf_two_le_of_sylowIn h.hT.1 h.hT.2.1 h.hT.2.2
  have hbR : baum R ≤ R := B2F.baum_le R
  have hQN : pCoreOf 2 X ≤ normalizer (V : Set G) :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 X).trans h.hXN)
  have hR₀R : baum R ⊔ pCoreOf 2 X ≤ R := sup_le hbR h.hQR
  have hcard : Nat.card ↥(autOn (baum R ⊔ pCoreOf 2 X) V) = 2 := by
    have h1 := autI_sup h.hVe (hbR.trans h.R_le_N) hQN
    rw [autI_eq_bot_of_le_centralizer h.hVe (C124.pCoreOf_le_centralizer h.hred), sup_bot_eq,
      hSstar] at h1
    show Nat.card ↥(autI h.hVe (baum R ⊔ pCoreOf 2 X)) = 2
    rw [h1, F.card_ρ, card_Z1]
  have hcl := hC124 X T V L (baum R ⊔ pCoreOf 2 X) 6 h.hX h.hSQ h.hred h.hT h.hprod h.hL h.hL2
    h.hVL h.isAltQuotient le_sup_right (hR₀R.trans h.hRT)
    (Or.inr (Or.inr (Or.inr ⟨rfl, hcard⟩)))
  have hbeq : baum R = baum (baum R ⊔ pCoreOf 2 X) := baum_eq_of_le le_sup_left hR₀R
  exact (c124_tail_a6 hbeq (h.hA6) hcl).resolve_left hCN

theorem point_b_concl (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hCN : ¬ CharNormal (baum (pCoreOf 2 P)) X) (hR : autI h.hVe (pCoreOf 2 P) = R1.map F.ρ)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G))
    (hJ1 : autI h.hVe (thompsonJ (pCoreOf 2 P)) = R1.map F.ρ) : BlockPart L := by
  have hJR : autI h.hVe (thompsonJ (pCoreOf 2 P)) = autI h.hVe (pCoreOf 2 P) := hJ1.trans hR.symm
  have hRS : autI h.hVe (pCoreOf 2 P) ≤ autI h.hVe (baum (pCoreOf 2 P)) := by
    rw [← hJR]
    exact autI_mono h.hVe (B2F.thompsonJ_le_baum _)
  have hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G) :=
    fun C h1 h2 h3 h4 => hCN ⟨C, h1, h2, h3, h4⟩
  obtain ⟨hMS, hLcomp, hset, -⟩ := h.toBaum.ms_tail h.hSQ hn1 hRS (F.point_no_strong hR)
    (F.point_hDE hR hJ hJR)
  have hblk := hC132 G (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) L hMS hLcomp hset
  exact blockPart_of_a6 h.hA6 (isA6Block_of_isAltBlockType
    (isAltBlock_of_c132 (card_of_a6 h.hA6) hblk))

end S6Frame

end CFSG.Quasithin.H13.U3.GC137
