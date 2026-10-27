module

public import CFSG.Quasithin.Background.FFC4Rank
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.FFC2Core

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank CFSG.Open Matrix

structure B58Inputs : Prop where
  g2 : ∀ (K : Type) [Field K] [Finite K], CharP K 2 → ThreeRank2 ↥(quasithinG2 K)
  g2d : ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ThreeRank2 ↥⁅quasithinG2 K, quasithinG2 K⁆
  ext : ∀ d : ℕ, 3 ≤ d → (FFModel.extSq (ZMod 2) d).Faithful

theorem exists_unit_order_three {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hn : Even n) : ∃ ζ : Kˣ, ζ ^ 3 = 1 ∧ ζ ≠ 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by
    rw [Nat.card_units, hK]
    obtain ⟨k, rfl⟩ := hn
    have h4 : 2 ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
    rw [h4]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 k
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
  exact ⟨ζ, by rw [← hζ]; exact pow_orderOf_eq_one ζ, fun h => by
    rw [h, orderOf_one] at hζ; omega⟩


theorem charP_two_of_card_pow {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    CharP K 2 := by
  have hfin : Fintype K := Fintype.ofFinite K
  obtain ⟨m, hp, hm⟩ := FiniteField.card K (ringChar K)
  have h2 : ringChar K = 2 := by
    have hdvd : ringChar K ∣ 2 ^ n := by
      rw [← hK, Nat.card_eq_fintype_card, hm]
      exact dvd_pow_self _ (PNat.ne_zero m)
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hdvd)
  have := ringChar.charP K
  rwa [h2] at this

theorem threeRank2_of_realizes {W : Type*} [CommGroup W] {D : FFModel} (hD : D.Faithful)
    {L : Subgroup (MulAut W)} {U Z : Subgroup W} {π : D.Gam →* ↥L} (h : D.RealizesVia L U Z π)
    (hX : ThreeRank2 D.Gam) : ThreeRank2 ↥L :=
  hX.of_injective π (injective_of_faithful_sec hD h)


theorem pairOK_of_pair (hI : B58Inputs) {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    {U Z : Subgroup W} (hno : ¬ ThreeRank2 ↥L) (hB : B42ModulePair L U Z) :
    (∃ n, BinaryNaturalSL L U Z 2 n) ∨ (∃ m, Odd m ∧ BinaryNaturalSL L U Z 3 m) ∨
      AlternatingNatural L U Z 5 := by
  rcases hB with h | ⟨n, hn⟩ | ⟨n, hn⟩ | ⟨n, hn⟩ | hn | h5 | h6 | h7 | h74 | h3a | h4 | h5' | hx4 | hx5
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨n, ?_, hn⟩)
    by_contra hnodd
    have hev : Even n := Nat.not_odd_iff_even.1 hnodd
    obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
    obtain ⟨ζ, hζ3, hζ1⟩ := exists_unit_order_three hc hev
    exact hno (threeRank2_of_realizes (FFModel.nat_faithful _) hπ
      (threeRank2_statedSL_three hζ3 hζ1))
  · obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
    exact absurd (threeRank2_of_realizes (FFModel.nat_faithful _) hπ threeRank2_statedSp) hno
  · obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
    have := charP_two_of_card_pow hc
    exact absurd (threeRank2_of_realizes (zornQ_faithful _ le_rfl) hπ (hI.g2 K ‹_›)) hno
  · obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
    have hc' : Nat.card K = 2 ^ 1 := hc
    have := charP_two_of_card_pow hc'
    exact absurd (threeRank2_of_realizes (zornQ_faithful _ (commutator_le_self_aux _)) hπ
      (hI.g2d K (by simpa using hc'))) hno
  · exact Or.inr (Or.inr h5)
  · obtain ⟨π, hπ⟩ := h6
    exact absurd (threeRank2_of_realizes (altDn_faithful (by norm_num)) hπ
      (threeRank2_alt (by norm_num))) hno
  · obtain ⟨π, hπ⟩ := h7
    exact absurd (threeRank2_of_realizes (altDn_faithful (by norm_num)) hπ
      (threeRank2_alt (by norm_num))) hno
  · obtain ⟨α, π, hπ⟩ := h74
    exact absurd (threeRank2_of_realizes (a7Four_faithful α) hπ (threeRank2_alt (n := 7) (by norm_num)))
      hno
  · obtain ⟨K, hK, hf, Γ₀, hc, -, hhat, -, π, hπ⟩ := h3a
    have hE9 : ThreeRank2 ↥Γ₀ := threeRank2_hat hhat
    exact absurd (threeRank2_of_realizes (FFModel.nat_faithful _) hπ hE9) hno
  · obtain ⟨K, hK, hf, hc, π, hπ⟩ := h4
    exact absurd (threeRank2_of_realizes (FFModel.nat_faithful _) hπ
      (threeRank2_statedSL (by norm_num))) hno
  · obtain ⟨K, hK, hf, hc, π, hπ⟩ := h5'
    exact absurd (threeRank2_of_realizes (FFModel.nat_faithful _) hπ
      (threeRank2_statedSL (by norm_num))) hno
  · obtain ⟨π, hπ⟩ := hx4
    exact absurd (threeRank2_of_realizes (hI.ext 4 (by norm_num)) hπ
      (threeRank2_statedSL (by norm_num))) hno
  · obtain ⟨π, hπ⟩ := hx5
    exact absurd (threeRank2_of_realizes (hI.ext 5 (by norm_num)) hπ
      (threeRank2_statedSL (by norm_num))) hno

end FFC

end CFSG.Quasithin
