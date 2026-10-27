module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Blk2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.H13.GoldschmidtC137U33Ms3
public import CFSG.Quasithin.H13.GoldschmidtC137U33Pt2

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)
  (E : Entry33 X T V L (pCoreOf 2 P) h.hVe)
  (hF : G2Facts (autI h.hVe X) (autI h.hVe L))
include h E hF

theorem natural_of_entry :
    G2NaturalDerived (autI h.hVe L) ⊤ (fixV (autI h.hVe L)) 1 ∧ commV (autI h.hVe L) = ⊤ := by
  have hcomm := commV_autI_eq_top h.hVe h.hLN h.hVL
  have hpair := E.case1i.2.1
  rw [hcomm, inf_top_eq] at hpair
  exact ⟨g2NaturalDerived_of_modulePair E.card hpair, hcomm⟩

section Point

variable {A : Subgroup (MulAut (IntMod V h.hVe))}
  (hA : PtA (autI h.hVe X) (autI h.hVe P) A)
  {c : MulAut (IntMod V h.hVe)} (hc : c ∈ autI h.hVe L)
  (hLc : autI h.hVe L ≤ A ⊔ B1.conjAut c A)
  (hC132 : CFSG.Quasithin.ASInputs.AS_C_1_32)
  (hn1 : ∀ C : Subgroup G, C ≤ baum (pCoreOf 2 P) → C ≠ ⊥ →
    (C.subgroupOf (baum (pCoreOf 2 P))).Characteristic → ¬ X ≤ normalizer (C : Set G))
include hA hc hLc hC132 hn1

theorem blockPart_of_point : BlockPart L := by
  have hC : ∀ B, ¬ IsStrongFFStarOffender (autI h.hVe (pCoreOf 2 P)) B := h.no_strong E hA
  have hDE := h.hDE_u33 E hA hc hLc hF.rk_L
  obtain ⟨hCV, -⟩ := b2_19_rel h.hVe h.hred.1 h.hXN h.toBaum.hLeq.symm
    (pCoreOf_isPGroup 2 P) h.hRX h.hVR h.toBaum.hA1 h.toBaum.hA2 h.toBaum.hA3 h.toBaum.hB hC hDE
  obtain ⟨hMS, hLcomp, hset⟩ := h.isMSPair_u33 E hF hA hn1 hCV
  have h132 := hC132 G (L ⊔ baum (pCoreOf 2 P)) (baum (pCoreOf 2 P)) L hMS hLcomp hset
  have hG2 := isG2Block_of_c132 (card_of_psu33 h.hlie) h132
  obtain ⟨hnat, hcomm⟩ := h.natural_of_entry E hF
  exact blockPart_of_psu33 h.hlie (h.isG2Block_h13 hG2 hnat hcomm)

end Point

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
