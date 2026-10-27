module

public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.LocalAnalysis.StandardType.GGK1ADvd
public import CFSG.LocalAnalysis.StandardType.GGResRows
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeLinear

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank Matrix

theorem prime_dvd_card_of_hasLabel_linear
    {H : Type} [Group H] {p a f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 1 ≤ a) (hpq : p ∣ 2 ^ f - 1)
    (hH : GGHasLabel ⟨.A, a, f⟩ H) : p ∣ Nat.card H := by
  obtain ⟨F, hField, hFinite, hF, ⟨e⟩⟩ := hH
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card hF
  have hq : p ∣ Nat.card F ^ 2 - 1 := by
    rw [hF]
    exact hpq.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ f) 2)
  have hdiv := prime_dvd_card_statedProj_statedSL hp hp2 (by omega : 2 ≤ a + 1)
    (CharP.cast_eq_zero F 2) hq
  rw [Nat.card_congr e.toEquiv, largeEvenSLGroup_eq_statedSL]
  exact hdiv

theorem prime_dvd_card_of_hasLabel_unitary
    {H : Type} [Group H] {p a f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ha : 2 ≤ a) (hpq : p ∣ 2 ^ f + 1)
    (hH : GGHasLabel ⟨.twA, a, f⟩ H) : p ∣ Nat.card H := by
  dsimp only [GGHasLabel, LargeEvenRawDatum] at hH
  obtain ⟨F, hField, hFinite, hF, ⟨e⟩⟩ := hH
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card (by simpa only [← pow_mul] using hF)
  have hq : p ∣ (2 ^ f) ^ 2 - 1 := by
    have heq : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
      rw [sq, mul_self_tsub_one, mul_comm]
    rw [heq]
    exact dvd_mul_of_dvd_right hpq _
  have hdiv := prime_dvd_card_statedProj_statedSU hp hp2 (by omega : 2 ≤ a + 1) hF hq
  rw [Nat.card_congr e.toEquiv]
  exact hdiv

end CFSG.StandardType

end
