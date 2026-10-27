module

public import CFSG.RankThree.GF2n.Stroth80.Sec57A
public import CFSG.RankThree.GF2n.Stroth80.Sec57B

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth_5_7_of_rootTrans (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (h : Sec5Hyp hc n t) (hRT : RootTrans M Q Z B) (hSL : SLNat hc t)
    (hb : ∃ g : G, ∃ b ∈ B, g * t * g⁻¹ = b) (hBt : B ≤ QB (Subgroup.zpowers t)) :
    Vt M (LB M Q B) B Z t ≤ (Q ⊓ QB (Subgroup.zpowers t)) ⊔ Z := by
  by_cases hA : CaseA Q Z t
  · exact stroth_5_7_caseA hc h hSL hBt hA
  · exact stroth_5_7_caseB h34 hc h hRT hSL hb hBt hA

theorem stroth_5_7_all (h34 : Stroth34Statement) : Stroth57AllStatement := by
  intro G _ _ M Q Z B hc n t h hall hSL hb hBt
  exact stroth_5_7_of_rootTrans h34 hc h (rootTrans_of_all h34 hc h hall) hSL hb hBt

@[expose] def StrothNoA2SpreadStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Ctx M Q Z B → ∀ n : ℕ,
    Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ B' : Subgroup G, Ctx M Q Z B' → NoA2 Q Z (LB M Q B')

theorem stroth57_of_all_of_spread (hall : Stroth57AllStatement)
    (hspread : StrothNoA2SpreadStatement) : Stroth57Statement := by
  intro G _ _ M Q Z B hc n t h hSL hb hBt
  exact hall G M Q Z B hc n t h
    (hspread G M Q Z B hc n h.width h.n_gt h.noA2 h.gen) hSL hb hBt

theorem stroth_5_7 (h34 : Stroth34Statement) (hspread : StrothNoA2SpreadStatement) :
    Stroth57Statement :=
  stroth57_of_all_of_spread (stroth_5_7_all h34) hspread

end CFSG.RankThree.GF2n.Stroth80
