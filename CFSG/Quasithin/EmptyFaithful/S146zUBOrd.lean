module

public import CFSG.Quasithin.EmptyFaithful.S153H30
public import CFSG.Quasithin.Background.F918P2
public import CFSG.Quasithin.EmptyFaithful.SBc16SAut

public section

namespace CFSG.Quasithin.S146zU.UB

theorem eq_four_of_isPSL_two_two_L216 {X : Type} [Group X] (e : Nonempty (X ≃* SBc16.L216))
    {n : ℕ} (h : IsPSL 2 2 n X) : n = 4 := by
  obtain ⟨e⟩ := e
  obtain ⟨hn1, hcard⟩ := S153H.card_psl_two_two h
  have h4080 : Nat.card X = 4080 := by
    rw [Nat.card_congr e.toEquiv]
    exact SBc16.card_L216
  rw [h4080] at hcard
  have hn : n < 6 := by
    by_contra hcon
    have h1 : 2 ^ 6 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (not_lt.mp hcon)
    have h2 : 64 ≤ 2 ^ n := by simpa using h1
    have h3 : 64 ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : 64 * (64 ^ 2 - 1) ≤ 2 ^ n * ((2 ^ n) ^ 2 - 1) :=
      Nat.mul_le_mul h2 (Nat.sub_le_sub_right h3 1)
    omega
  interval_cases n <;> first | rfl | omega

theorem eq_four_of_case_one {W : Type} [CommGroup W] {L : Subgroup (MulAut W)} {V : Subgroup W}
    (hV : V = ⊤) (e : Nonempty (↥L ≃* SBc16.L216)) {n : ℕ} (h : IsPSL 2 2 n ↥(autSub L V)) :
    n = 4 :=
  eq_four_of_isPSL_two_two_L216 e (isPSL_of_autSub_top hV h)

end CFSG.Quasithin.S146zU.UB
