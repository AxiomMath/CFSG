module

public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylScIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRanks
public import CFSG.LocalAnalysis.StandardType.GGTwF4SUThreeRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Main

theorem largeEvenLabelAll_noLine_twF4 {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : lab.tag = .twF4 ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∃ r, (GGTorusLift p r R ∨ r = 0) ∧ GGTorusNoLine p r R I := by
  obtain ⟨ht, rfl, hpn⟩ := h
  have hs : LargeEvenSplit 3 lab :=
    Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted, ht], by simp [ht], hpn⟩)
  exact (TableBExcSmallRanks.largeEvenLabelAll_card_lt_twF4_of
    (fun a ha K _ _ _ hK _ E hE => TwF4SUThree.ggTwF4ThreeRankInput_holds a ha K hK E hE)
    hp hlab ht hs).mono fun _ _ _ _ hX _ _ => ⟨0, Or.inr rfl, ggTorusNoLine_of_card_lt hX⟩

theorem ggNbrInnerWeylOn_twF4 : GGNbrInnerWeylOn GGNbrWeylTwF4Label :=
  ggNbrInnerWeylOn_of_labels fun p lab hp hp2 hlab ⟨hpow, ht, hp3, hpq⟩ =>
    largeEvenLabelAll_weylInnerKLevel_of_noLine_or
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab hpow)
      (largeEvenLabelAll_noLine_twF4 hp hlab ⟨ht, hp3, hpq⟩)

end Main

end CFSG.StandardType

end
