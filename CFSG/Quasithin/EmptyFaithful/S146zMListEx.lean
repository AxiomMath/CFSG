module

public import CFSG.RankThree.Chevalley.ExceptionalModelOrderThree
public import CFSG.LieType.Ree.LargeReeModelSchreier
public import CFSG.RankThree.SteinbergR3ELargeReeOrder
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A134EvenClassical

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.LieType.Ree

theorem three_dvd_card_chevalleyExceptional_model
    {S : Type} [Group S] [Finite S]
    {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {ℓ f : ℕ}
    (h : ChevalleyExceptionalModel S t ℓ f) : 3 ∣ Nat.card S :=
  CFSG.RankThree.Chevalley.Chevalley_exceptional_models_order_divisible_by_three S t ℓ f h

theorem zm_exists_gamma_of_model
    {X : Type} [Group X] {f : ℕ}
    (h : ReeTitsModel X .twistedF4 2 f) :
    ∃ (a : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K ReeTag.F4.prime),
      1 ≤ a ∧ f = 2 * a + 1 ∧ Nat.card K = 2 ^ f ∧
      Nonempty (X ≃* ReeTag.F4.reeGamma K a) := by
  obtain ⟨hFin, -, -, -, ⟨a, ha, hfa⟩, hmodel⟩ := ReeTag.large_Ree_model_Schreier X 2 f h
  obtain ⟨-, a', hfa', hrel⟩ := h
  obtain ⟨K, _, _, hKcard, ⟨e⟩⟩ := hrel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K ReeTag.F4.prime := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
  have haa : a' = a := by omega
  subst haa
  obtain ⟨e'⟩ := hmodel a' K hfa' hKcard ⟨e⟩
  exact ⟨a', K, inferInstance, inferInstance, hchar, ha, hfa', hKcard, ⟨e'⟩⟩

theorem three_dvd_card_twistedF4_model
    {S : Type} [Group S] {f : ℕ}
    (h : ReeTitsModel S .twistedF4 2 f) : 3 ∣ Nat.card S := by
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ := zm_exists_gamma_of_model h
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  rw [Nat.card_congr e.toEquiv,
    (CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion a K hK').1]
  have h3 : 3 ∣ 2 ^ (2 * a + 1) + 1 := by
    have := CFSG.QuasithinUnique.Vol2Native.EvenWit.two_pow_odd_mod a
    omega
  exact ((((dvd_pow h3 two_ne_zero).mul_left _).mul_right _).mul_right _).mul_right _

theorem three_dvd_card_tits_model
    {S : Type} [Group S] {p f : ℕ} (h : ReeTitsModel S .Tits p f) : 3 ∣ Nat.card S := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S p f h
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]
  norm_num

end CFSG.Quasithin
