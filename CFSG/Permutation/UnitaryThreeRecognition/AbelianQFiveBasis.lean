module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveCoord
public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQ
public import CFSG.Permutation.UnitaryThreeRecognition.Exponent
public import CFSG.Permutation.UnitaryThreeRecognition.StdHyp

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

namespace StdHyp

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f : ℕ} (S : StdHyp G Q a b j s p f 3) [Finite G] [Finite Ω] (h5 : p ^ f = 5)
include S h5

omit [Finite G] [Finite Ω] in
theorem p_eq_five : p = 5 := by
  have h1 : p ∣ 5 := by rw [← h5]; exact dvd_pow_self p (by have := S.hf; omega)
  rcases (Nat.dvd_prime Nat.prime_five).mp h1 with h | h
  · exact absurd h S.hpp.one_lt.ne'
  · exact h

theorem pow_five_eq_one {x : G} (hx : x ∈ Q) : x ^ 5 = 1 := by
  have := S.root.pow_prime_eq_one S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2 S.hj1 S.hsq S.hpp S.hp
    S.hf S.hpodd S.hd S.hd3 S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 hx
  rwa [S.p_eq_five h5] at this

omit [Finite G] [Finite Ω] in
theorem card_Q_eq : Nat.card Q = 125 := by
  rw [S.hQcard, mul_comm 3 f, pow_mul, h5]; norm_num

theorem card_centQ_eq : Nat.card (centQ Q j) = 5 := by rw [S.card_centQ, h5]

omit [Finite G] [Finite Ω] in
theorem odd_card_Q : Odd (Nat.card Q) := by rw [S.card_Q_eq h5]; decide

theorem pow5_eq_one_iff {x : G} (hxQ : x ∈ Q) (hx1 : x ≠ 1) (c : ZMod 5) :
    pow5 x c = 1 ↔ c = 0 := by
  constructor
  · intro hc
    have hord : orderOf x = 5 := by
      have h5' : x ^ 5 = 1 := S.pow_five_eq_one h5 hxQ
      have hdvd := orderOf_dvd_of_pow_eq_one h5'
      rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have := orderOf_dvd_of_pow_eq_one hc
    rw [hord] at this
    have hlt : c.val < 5 := ZMod.val_lt c
    have h0 : c.val = 0 := by
      obtain ⟨k, hk⟩ := this
      omega
    exact (ZMod.val_eq_zero c).mp h0
  · rintro rfl; exact pow5_zero x

variable (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
include hQab

theorem card_invSub_eq : Nat.card (AbelianQ.invSub Q j hQab) = 25 := by
  have h := AbelianQ.card_eq_card_centQ_mul (hQab := hQab) (S.odd_card_Q h5)
    (fun x hx => S.root.normal j S.hj.1 x hx) S.hj2
  rw [S.card_Q_eq h5, S.card_centQ_eq h5] at h
  omega

end StdHyp

end CFSG.UnitaryThreeRecognition
