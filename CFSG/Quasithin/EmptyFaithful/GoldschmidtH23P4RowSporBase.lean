module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Core

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique

theorem card_sylow_two_of_card {X : Type*} [Group X] [Finite X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) {a m : ℕ} (hm : ¬ 2 ∣ m) (hcard : Nat.card X = 2 ^ a * m) :
    Nat.card T = 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hp, hodd⟩ := isSylowTwoOf_top_iff.1 hT
  obtain ⟨s, hs⟩ := hp.exists_card_eq
  have hidx : Nat.card X = Nat.card T * T.index := (Subgroup.card_mul_index T).symm
  have hi0 : T.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero 2)
  rw [hs] at hidx ⊢
  have h12 : 2 ^ s * T.index = 2 ^ a * m := hidx.symm.trans hcard
  have e1 : padicValNat 2 (2 ^ s * T.index) = s := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hi0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hodd, add_zero]
  have e2 : padicValNat 2 (2 ^ a * m) = a := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hm, add_zero]
  have : s = a := e1.symm.trans ((congrArg (padicValNat 2) h12).trans e2)
  rw [this]

theorem noFiveIndex_of_card_cases {X : Type*} [Group X] [Finite X] {a m : ℕ} (hm : ¬ 2 ∣ m)
    (h3 : 3 ∣ m) (hcard : Nat.card X = 2 ^ a * m)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y →
      Y = ⊤ ∨ Nat.card Y = 2 ^ a ∨ 3 ∣ Nat.card Y) :
    NoFiveIndex X := by
  intro S₀ U hS hle b hb
  have hS' := card_sylow_two_of_card hS hm hcard
  have hrel : S₀.relIndex U * Nat.card S₀ = Nat.card U := by
    have := Subgroup.relIndex_mul_card (H := S₀) (K := U)
    rwa [inf_eq_left.2 hle] at this
  rw [hb, hS'] at hrel
  have hpos : 0 < 2 ^ a := by positivity
  have h3b : ¬ 3 ∣ 5 ^ b := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  by_contra hb0
  rcases hover S₀ U hS hle with hU | hU | hU
  · rw [hU, Subgroup.card_top, hcard] at hrel
    have hm5 : m = 5 ^ b := by
      have h2 : 5 ^ b * 2 ^ a = m * 2 ^ a := by rw [hrel, mul_comm]
      exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm
    exact h3b (hm5 ▸ h3)
  · rw [hU] at hrel
    have h2 : 5 ^ b * 2 ^ a = 1 * 2 ^ a := by rw [hrel, one_mul]
    have h1 : 5 ^ b = 1 := Nat.eq_of_mul_eq_mul_right hpos h2
    have : 1 < 5 ^ b := Nat.one_lt_pow hb0 (by norm_num)
    omega
  · rw [← hrel] at hU
    exact h3b ((Nat.Coprime.pow_right a (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_right hU)

theorem center_eq_bot_of_simple_of_card {X : Type*} [Group X] [Finite X] (hX : IsSimpleGroup X)
    {a m : ℕ} (ha : 1 ≤ a) (h3 : 3 ∣ m) (hcard : Nat.card X = 2 ^ a * m) :
    Subgroup.center X = ⊥ := by
  have := hX
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative X :=
      ⟨⟨fun x y => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y : y ∈ _) x)⟩⟩
    have hp : (Nat.card X).Prime := Group.is_simple_iff_prime_card.mp hX
    have h2 : 2 ∣ Nat.card X := hcard ▸ Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) m
    have h3' : 3 ∣ Nat.card X := hcard ▸ Dvd.dvd.mul_left h3 (2 ^ a)
    have e2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
    have e3 := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h3'
    omega

theorem rowOK_of_rows {X : Type*} [Group X] [Finite X] (hX : IsSimpleGroup X) {a m : ℕ}
    (ha : 1 ≤ a) (hm : ¬ 2 ∣ m) (h3 : 3 ∣ m) (hcard : Nat.card X = 2 ^ a * m)
    (hover : ∀ T Y : Subgroup X, IsSylowTwoOf T ⊤ → T ≤ Y →
      Y = ⊤ ∨ Nat.card Y = 2 ^ a ∨ 3 ∣ Nat.card Y)
    (hout : CFSG.Quasithin.H23Out.Out5Pow X) : RowOK X where
  center := center_eq_bot_of_simple_of_card hX ha h3 hcard
  out := hout
  idx := noFiveIndex_of_card_cases hm h3 hcard hover

end CFSG.Quasithin.H23P4
