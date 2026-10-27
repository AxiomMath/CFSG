module

public import CFSG.RankThree.GF2n.Smith81.S81BTacitDef
public import CFSG.RankThree.GF2n.Smith81.S81BNoA2U
public import CFSG.RankThree.GF2n.Smith81.S81BNoA2

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def ETacitE3UStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3U M Q Z B → ∀ B' : Subgroup G, Ctx M Q Z B' →
      NoA2 Q Z (LB M Q B') ∧ GenByB M Q B'

theorem eTacitE3L_of_genByB (hGen : StrothGenByBStatement) : ETacitE3LStatement := by
  intro G _ _ M Q Z B _ hc h3L B' hB'
  have hno : NoA2 Q Z (LB M Q B') :=
    noA2All_of_inCaseE3L hc.toCfg h3L B' hB'.conj hB'.le hB'.ne
  obtain ⟨-, -, hQ, -⟩ := h3L
  have hw : Width Q Z 10 := by simpa [Width] using hQ
  exact ⟨hno, hGen G M Q Z B' hB' 10 hw (by norm_num) hno⟩

theorem eTacitE3U_of_genByB (hGen : StrothGenByBStatement) : ETacitE3UStatement := by
  intro G _ _ M Q Z B _ hc h3U B' hB'
  have hno : NoA2 Q Z (LB M Q B') :=
    noA2All_of_inCaseE3U hc.toCfg h3U B' hB'.conj hB'.le hB'.ne
  obtain ⟨-, -, hQ, -⟩ := h3U
  have hw : Width Q Z 10 := by simpa [Width] using hQ
  exact ⟨hno, hGen G M Q Z B' hB' 10 hw (by norm_num) hno⟩

end CFSG.RankThree.GF2n.Smith81
