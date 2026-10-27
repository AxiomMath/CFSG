module

public import CFSG.RankThree.PartTwo.Sec4.Item49

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item49Tools

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {H K : Type*} [Group H] [Group K]

theorem oThreePrime_map_le (f : H →* K) : (oThreePrime H).map f ≤ oThreePrime K := by
  rw [oThreePrime, MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨g, ⟨k, hk⟩, rfl⟩
  exact Subgroup.subset_closure ⟨k, by rw [← map_pow, hk, map_one]⟩

theorem odd_card_oThreePrime_of_injective [Finite K] (f : H →* K) (hf : Function.Injective f)
    (hK : Odd (Nat.card (oThreePrime K))) : Odd (Nat.card (oThreePrime H)) := by
  have hle : (oThreePrime H).map f ≤ oThreePrime K := oThreePrime_map_le f
  have hcard : Nat.card ((oThreePrime H).map f) = Nat.card (oThreePrime H) :=
    Subgroup.card_map_of_injective hf
  have hdvd : Nat.card ((oThreePrime H).map f) ∣ Nat.card (oThreePrime K) :=
    Subgroup.card_dvd_of_le hle
  rw [hcard] at hdvd
  exact Odd.of_dvd_nat hK hdvd

theorem odd_card_oThreePrime_congr [Finite H] [Finite K] (e : H ≃* K) :
    Odd (Nat.card (oThreePrime H)) ↔ Odd (Nat.card (oThreePrime K)) :=
  ⟨fun h => odd_card_oThreePrime_of_injective e.symm.toMonoidHom e.symm.injective h,
    fun h => odd_card_oThreePrime_of_injective e.toMonoidHom e.injective h⟩

theorem isPGroup_oThreePrime_of_comm [Finite H] (hcomm : ∀ a b : H, a * b = b * a) :
    IsPGroup 3 (oThreePrime H) := by
  let T : Subgroup H :=
    { carrier := {g | ∃ k : ℕ, g ^ 3 ^ k = 1}
      one_mem' := ⟨0, by simp⟩
      mul_mem' := by
        rintro a b ⟨i, hi⟩ ⟨j, hj⟩
        refine ⟨i + j, ?_⟩
        have ha : a ^ 3 ^ (i + j) = 1 := by rw [pow_add, pow_mul, hi, one_pow]
        have hb : b ^ 3 ^ (i + j) = 1 := by rw [add_comm, pow_add, pow_mul, hj, one_pow]
        rw [(Commute.mul_pow (hcomm a b) _), ha, hb, one_mul]
      inv_mem' := by
        rintro a ⟨i, hi⟩
        exact ⟨i, by rw [inv_pow, hi, inv_one]⟩ }
  have hle : oThreePrime H ≤ T := by
    rw [oThreePrime, Subgroup.closure_le]
    exact fun g hg => hg
  intro g
  obtain ⟨k, hk⟩ := hle g.2
  exact ⟨k, Subtype.ext (by simpa using hk)⟩

theorem eq_one_of_sq_eq_one_of_isPGroup {P : Subgroup K} (hP : IsPGroup 3 P) {y : K} (hy : y ∈ P)
    (hy2 : y ^ 2 = 1) : y = 1 := by
  obtain ⟨k, hk⟩ := hP ⟨y, hy⟩
  have hk' : y ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf y ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
  have hcop : Nat.Coprime (3 ^ k) 2 := Nat.Coprime.pow_left _ (by norm_num)
  have : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp this

theorem odd_card_oThreePrime_of_quotient [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) (hQ : IsPGroup 3 (oThreePrime (H ⧸ N))) :
    Odd (Nat.card (oThreePrime H)) := by
  by_contra hev
  rw [Nat.not_odd_iff_even, even_iff_two_dvd] at hev
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := oThreePrime H) 2 hev
  have hx2 : (x : H) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at hx
    rw [← hx]
    exact pow_orderOf_eq_one _
  have hmem : (QuotientGroup.mk' N) (x : H) ∈ oThreePrime (H ⧸ N) :=
    oThreePrime_map_le (QuotientGroup.mk' N) ⟨x, x.2, rfl⟩
  have h1 := eq_one_of_sq_eq_one_of_isPGroup hQ hmem (by rw [← map_pow, hx2, map_one])
  have hxN : (x : H) ∈ N := by
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hdvd : orderOf (⟨x, hxN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hx] at hdvd
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr hdvd)

theorem odd_card_oThreePrime_of_comm_quotient [Finite H] (N : Subgroup H) [N.Normal]
    (hN : Odd (Nat.card N)) (hcomm : ∀ a b : H ⧸ N, a * b = b * a) :
    Odd (Nat.card (oThreePrime H)) :=
  odd_card_oThreePrime_of_quotient N hN (isPGroup_oThreePrime_of_comm hcomm)

theorem odd_card_oThreePrime_of_comm [Finite H] (hcomm : ∀ a b : H, a * b = b * a) :
    Odd (Nat.card (oThreePrime H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (isPGroup_oThreePrime_of_comm hcomm).exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

theorem oThreePrime_eq_bot_of_not_dvd [Finite H] (h3 : ¬ 3 ∣ Nat.card H) :
    oThreePrime H = ⊥ := by
  rw [oThreePrime, Subgroup.closure_eq_bot_iff]
  rintro g ⟨k, hk⟩
  have h1 : orderOf g ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf g ∣ Nat.card H := orderOf_dvd_natCard g
  have hcop : Nat.Coprime (3 ^ k) (Nat.card H) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem odd_card_oThreePrime_of_not_dvd [Finite H] (h3 : ¬ 3 ∣ Nat.card H) :
    Odd (Nat.card (oThreePrime H)) := by
  rw [oThreePrime_eq_bot_of_not_dvd h3, Subgroup.card_bot]
  exact odd_one

theorem odd_card_oThreePrime_outer_congr {X Y : Type*} [Group X] [Group Y] [Finite (Outer X)]
    [Finite (Outer Y)] (e : X ≃* Y) :
    Odd (Nat.card (oThreePrime (Outer X))) ↔ Odd (Nat.card (oThreePrime (Outer Y))) :=
  odd_card_oThreePrime_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e)

theorem odd_card_oThreePrime_outer_of_center (X : Type*) [Group X] [Group.IsPerfect X]
    [Finite (Outer (X ⧸ Subgroup.center X))]
    (h : Odd (Nat.card (oThreePrime (Outer (X ⧸ Subgroup.center X))))) :
    Odd (Nat.card (oThreePrime (Outer X))) :=
  odd_card_oThreePrime_of_injective _
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective X) h

end CFSG.RankThree.PartTwo.Sec4.Item49Tools
