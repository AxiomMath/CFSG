module

public import CFSG.Quasithin.Vol2.Ch10SecKIK2p
public import CFSG.Quasithin.Vol2.Ch10SecKIK2n
public import CFSG.RankThree.PartOne.S12K.Rigidity

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Vol2.Ch11.SecA CFSG.Blueprint

@[expose] def GoodLie (X : Type) [Group X] : Prop :=
  ∃ f : ℕ, (1 ≤ f ∧ IsPSL 3 2 f X) ∨ (1 ≤ f ∧ IsSL3 (2 ^ f) X) ∨ (2 ≤ f ∧ IsPSp4 2 f X) ∨
    (2 ≤ f ∧ IsG2 2 f X)

variable {X : Type} [Group X] {M : ℕ}

omit [Group X] in
theorem false_of_big (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M) {f u : ℕ}
    (hf : 1 ≤ f) (hu : Odd u) (hX : Nat.card X = 2 ^ (12 * f) * u)
    (hlt : u < ((2 ^ f) ^ 12 - 1) * ((2 ^ f) ^ 4 - 1)) : False := by
  rcases hc with h1 | h3
  · exact false_of_b56_big hf hu (by rw [← hX, h1]; exact hJ) hlt
  · have h3u : 3 ∣ u := by
      have : 3 ∣ 2 ^ (12 * f) * u := ⟨M, by rw [← hX, h3]⟩
      exact (Nat.Coprime.pow_right _ (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left this
    obtain ⟨w, rfl⟩ := h3u
    have hM : M = 2 ^ (12 * f) * w := by
      have : 3 * M = 3 * (2 ^ (12 * f) * w) := by rw [← h3, hX]; ring
      omega
    have hw : Odd w := by
      rcases hu with ⟨k, hk⟩
      by_contra hw
      rw [Nat.not_odd_iff_even] at hw
      obtain ⟨j, rfl⟩ := hw
      omega
    exact false_of_b56_big hf hw (hM ▸ hJ) (by omega)


theorem false_of_3D4 (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M) {f : ℕ}
    (h : Is3D4 2 f X) : False := by
  have hf : 1 ≤ f := h.1.2.1
  have hX : Nat.card X = ordTrialityD4 (2 ^ f) :=
    CFSG.Timmesfeld.card_chevalleyExceptionalModel_two h
  set x := 2 ^ f with hx
  have hx2 : 2 ≤ x := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have he : ∀ k, 1 ≤ k → Even (x ^ k) := fun k hk => by
    rw [hx, ← pow_mul]
    exact Nat.even_pow.2 ⟨even_two, by positivity⟩
  have hodd : Odd ((x ^ 8 + x ^ 4 + 1) * (x ^ 6 - 1) * (x ^ 2 - 1)) := by
    have h8 : Even (x ^ 8 + x ^ 4) := (he 8 (by norm_num)).add (he 4 (by norm_num))
    exact (h8.add_one.mul (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))).mul
      (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega) (by norm_num))
  refine false_of_big hJ hc hf hodd ?_ (key3D4 hx2)
  rw [hX, ordTrialityD4, mul_comm 12 f, pow_mul]
  ring

theorem false_of_2F4 (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M) {f : ℕ}
    (h : Is2F4 f X) : False := by
  have hf : 1 ≤ f := by
    obtain ⟨-, a, ha, -⟩ := h
    omega
  have hX : Nat.card X = ordTwistedF4 (2 ^ f) :=
    CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_twistedF4 h
  set x := 2 ^ f with hx
  have hx2 : 2 ≤ x := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have he : ∀ k, 1 ≤ k → Even (x ^ k) := fun k hk => by
    rw [hx, ← pow_mul]
    exact Nat.even_pow.2 ⟨even_two, by positivity⟩
  have hodd : Odd ((x ^ 6 + 1) * (x ^ 4 - 1) * (x ^ 3 + 1) * (x - 1)) := by
    have h1 : Odd (x - 1) := by
      have := CFSG.Timmesfeld.Orders.odd_pow_sub_one (f := f) (a := 1) (by omega) (by norm_num)
      rwa [pow_one] at this
    exact (((he 6 (by norm_num)).add_one.mul (CFSG.Timmesfeld.Orders.odd_pow_sub_one (by omega)
      (by norm_num))).mul ((he 3 (by norm_num)).add_one)).mul h1
  refine false_of_big hJ hc hf hodd ?_ (key2F4 hx2)
  rw [hX, ordTwistedF4, mul_comm 12 f, pow_mul]
  ring

theorem false_of_tits (hJ : B56Card M) (hc : Nat.card X = M ∨ Nat.card X = 3 * M)
    (h : IsTits X) : False := by
  have hX : Nat.card X = 17971200 := by
    rw [CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits h]
    decide
  exact false_of_card hJ hc hX 11 8775 11 2925 (by norm_num) (by decide) (by decide)
    (by norm_num) (by decide) (by decide)

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
