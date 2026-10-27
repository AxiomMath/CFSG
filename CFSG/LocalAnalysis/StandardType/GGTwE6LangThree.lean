module

public import CFSG.LocalAnalysis.StandardType.GGTwE6LangRank
public import CFSG.LocalAnalysis.StandardType.GGSmallKGInputsTwE6Center
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6ThreeRound

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.TwistedE6
  CFSG.LieType.Steinberg.Exceptional

namespace TwE6Lang

section Torus

variable {n : ℕ}

theorem exists_langTorus (hn : 1 ≤ n) {ζ : (GaloisField 2 (2 * n))ˣ}
    (hζ : ζ ^ (2 ^ n + 1) = 1) :
    ∃ T : Subgroup (twistedE6Group 2 n), Nat.card T = orderOf ζ ^ 6 ∧
      (∀ x ∈ T, ∀ y ∈ T, x * y = y * x) ∧ ∀ x ∈ T, x ^ orderOf ζ = 1 := by
  obtain ⟨l, hl⟩ := exists_frobQ_ne hn
  have hm : ζ ^ ((2 : ℤ) ^ n + 1) = 1 := by
    rw [show ((2 : ℤ) ^ n + 1) = ((2 ^ n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, hζ]
  have hle := langTorusE_le_fixedGroup (frobQ 2 n) (frobQ_frobQ 2 n hn) hl
    (units_map_frobQ ζ) hm
  refine ⟨(langTorusE _ (frobQ 2 n) l ζ).subgroupOf (fixedGroup _ (frobQ 2 n)), ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, card_langTorusE]
  · intro x hx y hy
    exact Subtype.ext (langTorusE_commute (frobQ 2 n) l ζ (Subgroup.mem_subgroupOf.1 hx)
      (Subgroup.mem_subgroupOf.1 hy)).eq
  · intro x hx
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, OneMemClass.coe_one]
      exact langTorusE_pow (frobQ 2 n) l (pow_orderOf_eq_one ζ) (Subgroup.mem_subgroupOf.1 hx))

theorem exists_isElemAbelian_twistedE6 (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime)
    (hpq : p ∣ 2 ^ n + 1) :
    ∃ E : Subgroup (twistedE6Group 2 n), IsElemAbelian p E ∧ Nat.card E = p ^ 6 := by
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (GaloisField 2 (2 * n)) :=
    Nat.finite_of_card_ne_zero (by rw [GaloisField.card 2 (2 * n) (by omega)]; positivity)
  have hdvd : p ∣ Nat.card (GaloisField 2 (2 * n))ˣ := by
    rw [card_units_galoisField hn]
    exact hpq.trans (add_one_dvd_sq_sub_one _)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hζq : ζ ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (hζ ▸ hpq)
  obtain ⟨T, hT, hcomm, hpow⟩ := exists_langTorus hn hζq
  refine ⟨T, ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, fun x hx => ?_⟩, by rw [hT, hζ]⟩
  rw [← hζ]
  exact hpow x hx

end Torus

end TwE6Lang

section Inputs

theorem ggTwE6ScThreeRankInput_holds : GGTwE6ScThreeRankInput := fun n hn h3 => by
  obtain ⟨E, hE, hc⟩ := TwE6Lang.exists_isElemAbelian_twistedE6 hn Nat.prime_three h3
  exact ⟨E, hE, hc.ge⟩

end Inputs

section Round

theorem ggTwE6ThreeCoverRankInput_holds : GGTwE6ThreeCoverRankInput :=
  ggTwE6ThreeCoverRankInput_of_sc ggTwE6ScThreeRankInput_holds

end Round

end CFSG.StandardType
