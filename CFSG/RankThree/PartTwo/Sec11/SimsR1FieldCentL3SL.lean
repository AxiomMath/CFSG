module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1FieldCentL3Tools
public import CFSG.RankThree.PartTwo.KFacts.K71Item119

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts (scalars_three_eq_bot_of_mod_three nonempty_sl3_mulEquiv_projSL
  card_sl_three_eq)
open Matrix

theorem exists_injective_rankTwo_sl {F : Type} [Field F] [Finite F] {r : ℕ} [Fact r.Prime]
    (hr : r ∣ Nat.card F - 1) :
    ∃ ψ : Multiplicative (Fin 2 → ZMod r) →* SpecialLinearGroup (Fin 3) F,
      Function.Injective ψ := by
  have hdvd : r ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hζr : ζ ^ r = 1 := hζ ▸ pow_orderOf_eq_one ζ
  haveI : NeZero r := ⟨(Fact.out : r.Prime).ne_zero⟩
  exact ⟨rankTwoHom (torusSL F) r (powZMod r ζ hζr),
    rankTwoHom_injective torusSL_injective (powZMod_injective hζr hζ)⟩

theorem isSimpleGroup_sl3 {F : Type} [Field F] (hF : Nat.card F % 3 = 2) :
    IsSimpleGroup (SpecialLinearGroup (Fin 3) F) ∧
      ∃ a b : SpecialLinearGroup (Fin 3) F, a * b ≠ b * a := by
  refine isSimpleGroup_of_quasisimple_center_eq_bot
    (CFSG.LieType.Universal.SpecialLinear.isQuasisimple 2 F le_rfl) ?_
  rw [← scalars_eq_center, scalars_three_eq_bot_of_mod_three hF]

theorem exists_prank_sl {m : ℕ} (hm : 3 ≤ m) (hq : 2 ^ m % 3 = 2) :
    ∃ r : ℕ, ∃ _ : Fact r.Prime, 5 ≤ r ∧
      ∃ ψ : Multiplicative (Fin 2 → ZMod r) →* projSL 3 (GaloisField 2 m),
        Function.Injective ψ := by
  set N := 2 ^ m with hN
  have h2N : 2 ∣ N := dvd_pow_self 2 (by omega)
  have h8 : 8 ≤ N := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hne : N - 1 ≠ 1 := by omega
  have hpr : (N - 1).minFac.Prime := Nat.minFac_prime hne
  have hdvd : (N - 1).minFac ∣ N - 1 := Nat.minFac_dvd _
  have h5 : 5 ≤ (N - 1).minFac := by
    by_contra hlt
    have hp2 := hpr.two_le
    have hcases : (N - 1).minFac = 2 ∨ (N - 1).minFac = 3 ∨ (N - 1).minFac = 4 := by omega
    rcases hcases with h | h | h
    · rw [h] at hdvd; omega
    · rw [h] at hdvd; omega
    · rw [h] at hpr; norm_num at hpr
  haveI : Fact (N - 1).minFac.Prime := ⟨hpr⟩
  have hF : Nat.card (GaloisField 2 m) = 2 ^ m := GaloisField.card 2 m (by omega)
  obtain ⟨ψ, hψ⟩ := exists_injective_rankTwo_sl (F := GaloisField 2 m) (r := (N - 1).minFac)
    (by rw [hF]; exact hdvd)
  obtain ⟨ν⟩ := nonempty_sl3_mulEquiv_projSL (F := GaloisField 2 m) (by rw [hF]; exact hq)
  exact ⟨_, ⟨hpr⟩, h5, ν.toMonoidHom.comp ψ, ν.injective.comp hψ⟩

theorem exists_prank_sl_one :
    ∃ ψ : Multiplicative (Fin 1 → ZMod 7) →* projSL 3 (GaloisField 2 1), Function.Injective ψ := by
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num)]; norm_num
  obtain ⟨ν⟩ := nonempty_sl3_mulEquiv_projSL (F := GaloisField 2 1) (by rw [hF])
  have hcard : Nat.card (projSL 3 (GaloisField 2 1)) = 168 := by
    rw [← Nat.card_congr ν.toEquiv, card_sl_three_eq, hF]
    norm_num
  haveI : Finite (projSL 3 (GaloisField 2 1)) := Finite.of_equiv _ ν.toEquiv
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := projSL 3 (GaloisField 2 1)) 7
    (by rw [hcard]; norm_num)
  have hx7 : x ^ 7 = 1 := hx ▸ pow_orderOf_eq_one x
  exact ⟨rankOneHom 7 (powZMod 7 x hx7), rankOneHom_injective (powZMod_injective hx7 hx)⟩

end CFSG.RankThree.PartTwo.Sec11.SimsR1.FieldCent.L3
