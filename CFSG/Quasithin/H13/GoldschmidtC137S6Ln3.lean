module

public import CFSG.Quasithin.H13.GoldschmidtC137CLn3
public import CFSG.Quasithin.H13.GoldschmidtC137S6Ln2
public import CFSG.Quasithin.H13.GoldschmidtC137TailW
public import CFSG.Quasithin.H13.GoldschmidtC137S6Blk
public import CFSG.Quasithin.H13.GoldschmidtC137S6Dict
public import CFSG.Quasithin.H13.GoldschmidtC137S6Pt1
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

@[expose] def inclV {V : Subgroup G} (hV : IsElemAbelian 2 V) : IntMod V hV →* G where
  toFun := IntMod.val
  map_one' := rfl
  map_mul' := fun a b => IntMod.val_mul a b

theorem inclV_injective {V : Subgroup G} (hV : IsElemAbelian 2 V) :
    Function.Injective (inclV hV) := fun _ _ h => IntMod.val_injective h

namespace S6Ctx

variable [Finite G] {X T V L P M : Subgroup G} (h : S6Ctx X T V L P M)
include h

theorem P_le_normalizer_line :
    P ≤ normalizer (((fixV (autI h.hVe (pCoreOf 2 P))).map (inclV h.hVe) : Subgroup G) :
      Set G) :=
  h.toBase.P_le_normalizer_line

theorem V_inf_centralizer_L :
    V ⊓ centralizer (L : Set G) = (fixV (autI h.hVe L)).map (inclV h.hVe) :=
  h.toBase.V_inf_centralizer_L

end S6Ctx

namespace S6Frame

variable [Finite G] {X T V L P M : Subgroup G} {h : S6Ctx X T V L P M} (F : S6Frame h)

include F in
theorem card_fixV_autI_L : Nat.card (fixV (autI h.hVe L)) = cK F.k :=
  F.toC137B.card_fixV_autI_L

include F in
theorem fixV_autI_X_eq_L : fixV (autI h.hVe X) = fixV (autI h.hVe L) :=
  F.toC137B.fixV_autI_X_eq_L

theorem card_fixV_R2 : Nat.card (fixV (R2.map (Mod.act 6 Mod.ut0))) = 4 :=
  C137FrameB.card_fixV_R2

theorem line_five (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (hA : ∃ A : Subgroup G, IsMaxElemAbelian T A ∧ 2 < Nat.card ↥(autOn A V)) :
    Concl X T V L P := by
  right
  right
  right
  refine ⟨Or.inl h.hA6, ?_, fun hh => absurd hh (not_hatA6_of_a6 h.hA6), hA⟩
  refine ⟨(fixV (autI h.hVe (pCoreOf 2 P))).map (inclV h.hVe), ?_, ?_, ?_, h.P_le_normalizer_line⟩
  · rw [h.V_inf_centralizer_L, ← F.fixV_autI_X_eq_L]
    exact Subgroup.map_mono (B1.fixV_le_fixV (autI_mono h.hVe h.R_le_X))
  · rintro _ ⟨u, -, rfl⟩
    exact u.val_mem
  · rw [h.V_inf_centralizer_L, Subgroup.card_map_of_injective (inclV_injective _),
      Subgroup.card_map_of_injective (inclV_injective _), F.card_fixV_autI_L, hR,
      F.card_fixV_ρ, card_fixV_R2]
    ring

theorem line_block (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
    (hCN : ¬ CharNormal (baum (pCoreOf 2 P)) X) (hP : autI h.hVe P = H2.map F.ρ)
    (hR : autI h.hVe (pCoreOf 2 P) = R2.map F.ρ)
    (h5 : ∀ A : Subgroup G, IsMaxElemAbelian T A → Nat.card ↥(autOn A V) ≤ 2)
    (hJ : ¬ thompsonJ (pCoreOf 2 P) ≤ centralizer (V : Set G)) : BlockPart L := by
  have hJ1 := F.line_J_eq hP hR h5 hJ
  have hRS : autI h.hVe (pCoreOf 2 P) ≤ autI h.hVe (baum (pCoreOf 2 P)) := by
    rw [hR, ← hJ1]
    exact autI_mono h.hVe (B2F.thompsonJ_le_baum _)
  have hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
      (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G) :=
    fun C h1 h2 h3 h4 => hCN ⟨C, h1, h2, h3, h4⟩
  obtain ⟨hMS, hLcomp, hset, -⟩ := h.toBaum.ms_tail' h.hSQ hn1 hRS (F.line_no_strong hR h5)
    (F.line_hDE hP hR h5 hJ)
  have hblk := hC132 G (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) L hMS hLcomp hset
  exact blockPart_of_a6 h.hA6 (isA6Block_of_isAltBlockType
    (isAltBlock_of_c132 (card_of_a6 h.hA6) hblk))

end S6Frame

end CFSG.Quasithin.H13.U3.GC137
