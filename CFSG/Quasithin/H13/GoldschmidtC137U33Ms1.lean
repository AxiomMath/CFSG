module

public import CFSG.Quasithin.H13.GoldschmidtC137U33Mod
public import CFSG.Quasithin.H13.GoldschmidtC137U33Pt1

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits

variable {G : Type} [Group G]

namespace U33Cfg

variable [Finite G] {X T V L P M : Subgroup G} (h : U33Cfg X T V L P M)

section Base

include h

theorem hG0X : L ⊔ baum (pCoreOf 2 P) ≤ X :=
  sup_le h.hLX (((B2F.baum_le _).trans (pCoreOf_le 2 P)).trans h.hPX.le)

theorem hG0N : L ⊔ baum (pCoreOf 2 P) ≤ normalizer (V : Set G) := h.hG0X.trans h.hXN

theorem isPGroup_G0C :
    IsPGroup 2 ↥((L ⊔ baum (pCoreOf 2 P)) ⊓ centralizer (V : Set G)) :=
  h.isPGroup_C.to_le (inf_le_inf_right _ h.hG0X)

theorem hG0n : L ⊔ baum (pCoreOf 2 P) ≤
    normalizer (((L ⊔ baum (pCoreOf 2 P)) ⊓ centralizer (V : Set G) : Subgroup G) : Set G) :=
  B2F.le_normalizer_inf Subgroup.le_normalizer (fun _ hg =>
    B2F.normalizer_le_normalizer_centralizer V (h.hG0N hg))

end Base

variable (E : Entry33 X T V L (pCoreOf 2 P) h.hVe)
  (hF : G2Facts (autI h.hVe X) (autI h.hVe L))
  {A : Subgroup (MulAut (IntMod V h.hVe))} (hA : PtA (autI h.hVe X) (autI h.hVe P) A)
include h E hF hA

theorem hAL : ¬ A ≤ autI h.hVe L := by
  intro hle
  obtain ⟨-, hA1, hAe, hbest⟩ := hA.off
  refine hF.no_off A hle hA1 hAe ?_
  have h0 := hbest ⊥ bot_le
  rwa [Subgroup.card_bot, B1.fixV_bot, Subgroup.card_top, one_mul] at h0

theorem hX_eq : autI h.hVe L ⊔ A = autI h.hVe X := by
  have hLX : autI h.hVe L ≤ autI h.hVe X := autI_mono h.hVe h.hLX
  have hAX : A ≤ autI h.hVe X := hA.off.1
  refine eq_of_sandwich le_sup_left (sup_le hLX hAX) ?_ ?_
  · rw [hF.card_X, E.card]
  · exact fun hle => h.hAL E hF hA (le_sup_right.trans hle)

theorem autI_G0 : autI h.hVe (L ⊔ baum (pCoreOf 2 P)) = autI h.hVe X := by
  apply le_antisymm
  · exact autI_mono h.hVe h.hG0X
  · rw [← h.hX_eq E hF hA, ← autI_baum h E hA]
    exact sup_le (autI_mono h.hVe le_sup_left) (autI_mono h.hVe le_sup_right)

theorem pCoreOf_G0 : pCoreOf 2 (L ⊔ baum (pCoreOf 2 P)) =
    (L ⊔ baum (pCoreOf 2 P)) ⊓ centralizer (V : Set G) := by
  apply le_antisymm
  · have h1 := A38c5.autI_pCoreOf h.hVe h.hG0N h.isPGroup_G0C
    rw [h.autI_G0 E hF hA, C124.pCoreOf_autI_eq_bot h.hVe h.hred] at h1
    exact le_inf (pCoreOf_le 2 _)
      ((autI_eq_bot_iff h.hVe ((pCoreOf_le 2 _).trans h.hG0N)).1 h1)
  · exact le_pCoreOf_of_le_normalizer 2 inf_le_left h.hG0n h.isPGroup_G0C

@[expose] noncomputable def phi :
    ↥(L ⊔ baum (pCoreOf 2 P)) ⧸ CFSG.pCore 2 ↥(L ⊔ baum (pCoreOf 2 P)) ≃* ↥(autI h.hVe X) :=
  ((QuotientGroup.quotientMulEquivOfEq
      (C124.ker_starHom_eq_pCore h.hVe h.hG0N (h.pCoreOf_G0 E hF hA)).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (C124.starHom h.hVe _ h.hG0N)
      (C124.starHom_surjective h.hVe h.hG0N))).trans
    (MulEquiv.subgroupCongr (h.autI_G0 E hF hA))

theorem phi_mk (g : ↥(L ⊔ baum (pCoreOf 2 P))) :
    ((h.phi E hF hA (QuotientGroup.mk g) : ↥(autI h.hVe X)) : MulAut (IntMod V h.hVe)) =
      convI h.hVe ⟨g, h.hG0N g.2⟩ := rfl

end U33Cfg

end CFSG.Quasithin.H13.U3.GC137
