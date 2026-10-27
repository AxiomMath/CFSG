module

public import CFSG.Quasithin.Recognition.SzVBBridge
public import CFSG.Quasithin.Recognition.SzVBKer

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G}

theorem benderBridge_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1))
    (hne : ¬ IsL2Quot 2 (OTwoQuot K1)) : BenderBridge K1 S (conjClosure Zs L2) := by
  obtain ⟨n', i, e, hA, h9⟩ := exists_isBenderAction_imgK hRO h hn hX
  exact ⟨⟨n', i, e, hA⟩, h9 hne, ker_inv_le_of_setting hRO h hn hX⟩

theorem benderLocalFacts_of_setting (hRO : RankOneListedFacts.{0}) (h : R1SettingLegacyBare K1 L2 S Zs)
    {n : ℕ} (hn : 2 ≤ n) (hX : IsBenderQuot n (OTwoQuot K1))
    (hne : ¬ IsL2Quot 2 (OTwoQuot K1)) :
    BenderLocalFacts (K1 ⊔ S) S (conjClosure Zs L2) := by
  have hamal := F112J2.amalgamHypV_of_setting hRO h
  exact benderLocalFacts_of_bridge h.hyp.h1.normalizes hamal.sylow₂
    ((le_sup_right : S ≤ L2 ⊔ S).trans hamal.normalizes)
    (benderBridge_of_setting hRO h hn hX hne)

end CFSG.Quasithin.SzVB
