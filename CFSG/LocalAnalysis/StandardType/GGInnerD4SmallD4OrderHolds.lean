module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallContracts
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.ClassicalInvolution.RouteD.TWRExoticArith

public section

namespace CFSG.StandardType.GGInnerD4SmallParts

open CFSG CFSG.Assembly CFSG.StandardType

private theorem ltrsm4_ordD_four_two_pow_le (n : ℕ) (hn : 1 ≤ n) :
    174182400 ≤ CFSG.Open.ordD 4 (2 ^ n) := by
  have hbase : 174182400 =
      2 ^ 12 * (2 ^ 4 - 1) * ((2 ^ 2 - 1) * ((2 ^ 4 - 1) * (2 ^ 6 - 1))) := by
    norm_num
  rw [hbase, CFSG.ClassicalInvolution.RouteD.TWR.ordD_four_eq,
    CFSG.Timmesfeld.ClassicalOrders.gcd_four_eq_one
      (CFSG.Timmesfeld.ClassicalOrders.odd_two_pow_pow_sub_one (f := n) (n := 4) hn
        (by norm_num)),
    Nat.div_one]
  have h2 : 2 ≤ 2 ^ n := by
    calc (2 : ℕ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  gcongr <;> first
    | exact Nat.pow_le_pow_left h2 _
    | exact Nat.sub_le_sub_right (Nat.pow_le_pow_left h2 _) 1

theorem d4OrderLowerInput_holds : S2MathAs51600Small.D4OrderLowerInput := by
  intro lab R _ hlab htag hrank hlabel
  rw [GGHasLabel] at hlabel
  simp only [LargeEvenRawDatum, htag, hrank] at hlabel
  rw [LargeEvenRecipeOmegaPlus] at hlabel
  obtain ⟨K, _, _, hKcard, hq⟩ := hlabel
  obtain ⟨e⟩ := hq
  have hcardX : Nat.card (LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K 4))) =
      CFSG.Open.ordD 4 (2 ^ lab.n) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two
      (statedClassicalModel_omegaPlus 4 lab.n hKcard
        ⟨Nat.prime_two, hlab.1, by norm_num⟩)).2.2.2.1 rfl
  have hcardR : Nat.card R = CFSG.Open.ordD 4 (2 ^ lab.n) := by
    rw [← hcardX]
    exact Nat.card_congr e.toEquiv
  rw [hcardR]
  exact ltrsm4_ordD_four_two_pow_le lab.n hlab.1

end CFSG.StandardType.GGInnerD4SmallParts

end
