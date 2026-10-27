module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCBase
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCCard
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCStab
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCDirect
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrameCFour

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

theorem qTwoLMSkel_frame_stab {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x)
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hMul : PSUTrivialMultiplier m) (h3 : ¬ 3 ∣ m)
    (hV : IsAugModel m V F.permV) (hVT : IsAugModel m VT F.permVT) :
    Nat.card {a : MulAut ↥Bs // a ∈ ggInduced ⊤ Bs ∧ a ⟨x, F.hx⟩ = ⟨x, F.hx⟩} ≤
      2 * m.factorial :=
  qTwoLMFrameC_stab_card_of_form F (qTwoLMFrameC_x_not_mem hG hL hMul) hV hVT
    (qTwoLMFrameC_stab_form F hG hL h3 hVT)

theorem qTwoLMSkel_frame_direct {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x)
    (hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (hMul : PSUTrivialMultiplier m) (h3 : ¬ 3 ∣ m)
    (hV : IsAugModel m V F.permV) (hVT : IsAugModel m VT F.permVT) : DirectP3At 3 Bs L x F.hx := by
  intro r hr hrefl hrx
  have hm4 : 4 ≤ m := qTwoLMFrameC_four_le hL
  have hm5 : 5 ≤ m := by
    by_contra hlt
    have h4 : m = 4 := by omega
    rw [h4] at hMul
    exact qTwoLMFrameC_not_psuTrivialMultiplier_four hMul
  have hxL : x ∉ L := qTwoLMFrameC_x_not_mem hG hL hMul
  have hsplit := qTwoLMFrameC_split F hxL hV hVT
  obtain ⟨π, ε, hπ⟩ := qTwoLMFrameC_stab_form F hG hL h3 hVT r hr hrx
  cases ε
  · exact qTwoLMFrameC_direct_pos F hsplit (qTwoLMFrameC_le_centralizer hG) hrx π
      (by simpa using hπ)
  · exact (qTwoLMFrameC_direct_neg F hm5 hVT (qTwoLMFrameC_card_Bs F (by omega) hV) hsplit hrefl
      hrx π (by simpa using hπ)).elim

end CFSG.StandardType.QTwo

end
