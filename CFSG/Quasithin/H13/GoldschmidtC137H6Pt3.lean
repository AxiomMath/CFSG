module

public import CFSG.Quasithin.H13.GoldschmidtC137CPt3
public import CFSG.Quasithin.H13.GoldschmidtC137H6Pt2
public import CFSG.Quasithin.H13.GoldschmidtC137H6Blk
public import CFSG.Quasithin.H13.GoldschmidtC137H6Dict
public import CFSG.Quasithin.H13.GoldschmidtC137H6Pt1
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.B3

variable {G : Type} [Group G]

namespace H6Frame

variable [Finite G] {X T V L P : Subgroup G} {h : H6Ctx X T V L P} (F : H6Frame h)

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
  exact (c124_tail_hat hbeq h.hhat hcl).resolve_left hCN

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
  exact blockPart_of_hatA6 h.hhat (isHatA6Block_of
    (isHatBlock_of_c132 (card_of_hatA6 h.hhat) hblk))

end H6Frame

end CFSG.Quasithin.H13.U3.GC137
