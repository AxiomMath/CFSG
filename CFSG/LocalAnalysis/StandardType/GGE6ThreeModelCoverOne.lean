module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.E6ThreeModel

theorem card_dvd_two_pow_mul_three {G : Type} [Group G] [Finite G] (Z : Subgroup G) (m : ℕ)
    (h1 : ∀ z ∈ Z, (z ^ 4 ^ m) ^ 3 = 1)
    (h2 : ∀ z₀ ∈ Z, ∀ z ∈ Z, orderOf z₀ = 3 → z ^ 3 = 1 → z ∈ Subgroup.zpowers z₀) :
    ∃ k : ℕ, Nat.card Z ∣ 2 ^ k * 3 := by
  classical
  have hNpos : Nat.card Z ≠ 0 := (Nat.card_pos (α := ↥Z)).ne'
  have hprime : ∀ p : ℕ, p.Prime → p ∣ Nat.card Z → p = 2 ∨ p = 3 := by
    intro p hp hpdvd
    haveI : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥Z) p hpdvd
    have hzG : ((z : G) ^ 4 ^ m) ^ 3 = 1 := h1 z z.2
    have hzpow : (z : G) ^ (4 ^ m * 3) = 1 := by rw [pow_mul]; exact hzG
    have hdvd : orderOf (z : G) ∣ 4 ^ m * 3 := orderOf_dvd_of_pow_eq_one hzpow
    rw [Subgroup.orderOf_coe, hz] at hdvd
    rcases hp.dvd_mul.mp hdvd with h4 | h3
    · left
      have hp4 : p ∣ 4 := hp.dvd_of_dvd_pow h4
      have hp2 : p ∣ 2 := by
        have h4' : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [h4'] at hp4
        exact hp.dvd_of_dvd_pow hp4
      exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp hp2
    · right
      exact (Nat.prime_dvd_prime_iff_eq hp (by decide)).mp h3
  have h9 : ¬ 9 ∣ Nat.card Z := by
    intro h9dvd
    haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
    let P : Sylow 3 ↥Z := default
    let Psub : Subgroup ↥Z := (P : Subgroup ↥Z)
    let j : ℕ := (Nat.card Z).factorization 3
    have hj2 : 2 ≤ j := by
      show 2 ≤ (Nat.card Z).factorization 3
      have hdvd : 3 ^ 2 ∣ Nat.card Z := by
        rwa [show (3 : ℕ) ^ 2 = 9 by norm_num]
      exact (Nat.Prime.pow_dvd_iff_le_factorization (show Nat.Prime 3 by decide) hNpos).mp hdvd
    have hcardP : Nat.card Psub = 3 ^ j := Sylow.card_eq_multiplicity P
    have hxj : ∀ x ∈ Psub, x ^ 3 = 1 := by
      intro x hx
      have hord1 : orderOf x ∣ 3 ^ j := by
        have := Subgroup.orderOf_dvd_natCard Psub hx
        rwa [hcardP] at this
      have hxpow : x ^ (3 ^ j) = 1 := (orderOf_dvd_iff_pow_eq_one).mp hord1
      have hx1G : ((x : G) ^ 4 ^ m) ^ 3 = 1 := h1 x x.2
      have hx1G' : (x : G) ^ (4 ^ m * 3) = 1 := by rw [pow_mul]; exact hx1G
      have hxpow2 : x ^ (4 ^ m * 3) = 1 := by
        apply Subtype.coe_injective
        simpa using hx1G'
      have hj1 : 1 ≤ j := by omega
      have hsplit : 3 ^ j = 3 * 3 ^ (j - 1) := by
        conv_lhs => rw [show j = j - 1 + 1 by omega]
        rw [pow_succ]
        exact Nat.mul_comm _ _
      have hA : (x ^ 3) ^ (3 ^ (j - 1)) = 1 := by
        rw [← pow_mul, ← hsplit]; exact hxpow
      have hB : (x ^ 3) ^ (4 ^ m) = 1 := by
        rw [← pow_mul, show 3 * 4 ^ m = 4 ^ m * 3 by rw [Nat.mul_comm]]
        exact hxpow2
      have hcop : Nat.Coprime (3 ^ (j - 1)) (4 ^ m) :=
        Nat.Coprime.pow (j - 1) m (by decide : Nat.Coprime 3 4)
      exact (pow_eq_one_iff_of_coprime hcop).mp ⟨hA, hB⟩
    have hjne : j ≠ 0 := by omega
    have h3dvd : 3 ∣ Nat.card Psub := by
      rw [hcardP]
      exact dvd_pow_self 3 hjne
    obtain ⟨z0, hz0order⟩ := exists_prime_orderOf_dvd_card' (G := ↥Psub) 3 h3dvd
    let z₀ : ↥Z := (z0 : ↥Z)
    have hz0orderZ : orderOf z₀ = 3 := by
      dsimp only [z₀]
      rw [Subgroup.orderOf_coe, hz0order]
    have hPsub : Psub ≤ Subgroup.zpowers z₀ := by
      intro x hx
      have hx3' : x ^ 3 = 1 := hxj x hx
      have hx3G : (x : G) ^ 3 = 1 := by
        have := congrArg (fun y : ↥Z => (y : G)) hx3'
        simpa using this
      have hz0orderG : orderOf (z₀ : G) = 3 := by
        rw [Subgroup.orderOf_coe]; exact hz0orderZ
      have hmem : (x : G) ∈ Subgroup.zpowers (z₀ : G) :=
        h2 (z₀ : G) z₀.2 (x : G) x.2 hz0orderG hx3G
      rw [Subgroup.mem_zpowers_iff] at hmem ⊢
      obtain ⟨k, hk⟩ := hmem
      exact ⟨k, by apply Subtype.coe_injective; simpa using hk⟩
    have hcard_zp : Nat.card (Subgroup.zpowers z₀) = 3 := by
      letI : Fintype ↥Z := Fintype.ofFinite ↥Z
      rw [Nat.card_eq_fintype_card, Fintype.card_zpowers, hz0orderZ]
    have hle : Nat.card Psub ≤ 3 := by
      have := Subgroup.card_le_of_le hPsub
      rwa [hcard_zp] at this
    have hge : 9 ≤ Nat.card Psub := by
      rw [hcardP]
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    omega
  refine ⟨Nat.card Z, ?_⟩
  have h2nz : 2 ^ Nat.card Z ≠ 0 := by
    have : (0 : ℕ) < 2 ^ Nat.card Z := by positivity
    exact this.ne'
  have hM : 2 ^ Nat.card Z * 3 ≠ 0 :=
    mul_ne_zero h2nz (by norm_num)
  apply (Nat.factorization_le_iff_dvd hNpos hM).mp
  intro p
  have h2fac : (2 ^ Nat.card Z * 3).factorization 2 = Nat.card Z := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f 2)
      (Nat.factorization_mul (a := 2 ^ Nat.card Z) (b := 3) h2nz (by norm_num))
    simp only [Finsupp.add_apply] at h
    rw [Nat.factorization_pow_self (show Nat.Prime 2 by decide),
      Nat.factorization_eq_zero_of_not_dvd (show ¬ (2 : ℕ) ∣ 3 by norm_num)] at h
    simpa using h
  have h3fac : (2 ^ Nat.card Z * 3).factorization 3 = 1 := by
    have h := congrArg (fun f : ℕ →₀ ℕ => f 3)
      (Nat.factorization_mul (a := 2 ^ Nat.card Z) (b := 3) h2nz (by norm_num))
    simp only [Finsupp.add_apply] at h
    have h3n2 : ¬ (3 : ℕ) ∣ 2 ^ Nat.card Z := by
      intro hd
      have h32 : (3 : ℕ) ∣ 2 := (show Nat.Prime 3 by decide).dvd_of_dvd_pow hd
      norm_num at h32
    rw [Nat.factorization_eq_zero_of_not_dvd h3n2,
      Nat.Prime.factorization_self (show Nat.Prime 3 by decide)] at h
    simpa using h
  by_cases hp : p.Prime
  · by_cases hp2 : p = 2
    · subst hp2
      rw [h2fac]
      exact le_of_lt (Nat.factorization_lt 2 hNpos)
    · by_cases hp3 : p = 3
      · subst hp3
        rw [h3fac]
        have hlt : (Nat.card Z).factorization 3 < 2 := by
          by_contra hcon
          push Not at hcon
          have hdvd : 9 ∣ Nat.card Z := by
            rw [show (9 : ℕ) = 3 ^ 2 by norm_num]
            exact (Nat.Prime.pow_dvd_iff_le_factorization (show Nat.Prime 3 by decide) hNpos).mpr hcon
          exact h9 hdvd
        omega
      · rw [Nat.factorization_eq_zero_of_not_dvd]
        · exact Nat.zero_le _
        · intro hpd
          rcases hprime p hp hpd with h | h
          · exact hp2 h
          · exact hp3 h
  · rw [Nat.factorization_eq_zero_of_not_prime (Nat.card Z) hp]
    exact Nat.zero_le _

end CFSG.StandardType.E6ThreeModel
