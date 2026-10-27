module

public import CFSG.Quasithin.EmptyFaithful.SzN15Out
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin.SzN15

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

@[expose] def XOrd (N : ℕ) : Prop :=
  20160 ≤ N ∧ ((∃ n c : ℕ, 2 ≤ n ∧ (c = 1 ∨ c = 3) ∧
      c * N = 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1))) ∨ N = 979200)

theorem two_pow_mul_odd_inj {a b u w : ℕ} (hu : Odd u) (hw : Odd w) (h : 2 ^ a * u = 2 ^ b * w) :
    a = b := by
  have hu' : ¬ 2 ∣ u := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hu
  have hw' : ¬ 2 ∣ w := by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.2 hw
  have h1 : padicValNat 2 (2 ^ a * u) = a := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hu.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hu', add_zero]
  have h2 : padicValNat 2 (2 ^ b * w) = b := by
    rw [padicValNat.mul (pow_ne_zero _ two_ne_zero) hw.pos.ne', padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hw', add_zero]
  rw [← h1, ← h2, h]

theorem odd_two_pow_sub_one {k : ℕ} (hk : 1 ≤ k) : Odd (2 ^ k - 1) := by
  have h1 : Even (2 ^ k) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact Nat.Even.sub_odd (Nat.one_le_two_pow) h1 odd_one

theorem odd_mul_c {c u : ℕ} (hc : c = 1 ∨ c = 3) (hu : Odd u) : Odd (c * u) := by
  rcases hc with rfl | rfl
  · simpa using hu
  · exact Odd.mul (by decide) hu

theorem key_sl2 (a c : ℕ) (ha : 2 ≤ a) (hc : c = 1 ∨ c = 3)
    (h : c * (a ^ 3 * ((a ^ 3) ^ 2 - 1)) = a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1))) : False := by
  have hpos : 0 < a ^ 3 := by positivity
  have h1 : c * ((a ^ 3) ^ 2 - 1) = (a ^ 2 - 1) * (a ^ 3 - 1) := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc a ^ 3 * (c * ((a ^ 3) ^ 2 - 1)) = c * (a ^ 3 * ((a ^ 3) ^ 2 - 1)) := by ring
      _ = a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) := h
  have hx : a ^ 2 ≤ a ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  have hy : 2 ≤ a ^ 3 := by
    calc 2 ≤ a := ha
      _ ≤ a ^ 3 := Nat.le_self_pow (by norm_num) a
  have hc1 : 1 ≤ c := by rcases hc with rfl | rfl <;> norm_num
  have h2 : (a ^ 2 - 1) * (a ^ 3 - 1) ≤ (a ^ 3 - 1) * (a ^ 3 - 1) :=
    Nat.mul_le_mul (Nat.sub_le_sub_right hx 1) le_rfl
  have h3 : (a ^ 3 - 1) * (a ^ 3 - 1) < (a ^ 3) ^ 2 - 1 := by
    obtain ⟨y, hy'⟩ : ∃ y, a ^ 3 = y + 2 := ⟨a ^ 3 - 2, by omega⟩
    rw [hy']
    have e1 : y + 2 - 1 = y + 1 := by omega
    have e2 : (y + 2) ^ 2 - 1 = y ^ 2 + 4 * y + 3 := by
      have : (y + 2) ^ 2 = y ^ 2 + 4 * y + 4 := by ring
      omega
    rw [e1, e2]
    nlinarith
  have h4 : (a ^ 3) ^ 2 - 1 ≤ c * ((a ^ 3) ^ 2 - 1) := Nat.le_mul_of_pos_left _ hc1
  omega

theorem key_g2 (r c : ℕ) (hr : 2 ≤ r) (hc : c = 1 ∨ c = 3)
    (h : c * (r ^ 6 * ((r ^ 6 - 1) * (r ^ 2 - 1))) = r ^ 6 * ((r ^ 4 - 1) * (r ^ 6 - 1))) :
    False := by
  have hpos : 0 < r ^ 6 * (r ^ 6 - 1) := by
    have h1 : 0 < r ^ 6 := by positivity
    have h2 : 0 < r ^ 6 - 1 := by
      have : 2 ^ 6 ≤ r ^ 6 := Nat.pow_le_pow_left hr 6
      omega
    exact Nat.mul_pos h1 h2
  have h1 : c * (r ^ 2 - 1) = r ^ 4 - 1 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc r ^ 6 * (r ^ 6 - 1) * (c * (r ^ 2 - 1))
        = c * (r ^ 6 * ((r ^ 6 - 1) * (r ^ 2 - 1))) := by ring
      _ = r ^ 6 * ((r ^ 4 - 1) * (r ^ 6 - 1)) := h
      _ = r ^ 6 * (r ^ 6 - 1) * (r ^ 4 - 1) := by ring
  have h4 : r ^ 4 - 1 = (r ^ 2 - 1) * (r ^ 2 + 1) := by
    have e : r ^ 4 = (r ^ 2) ^ 2 := by ring
    have h2 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
    rw [e]
    zify [h2, Nat.one_le_pow 2 (r ^ 2) (by omega)]
    ring
  have hr2 : 4 ≤ r ^ 2 := by nlinarith
  have hpos2 : 0 < r ^ 2 - 1 := by omega
  rw [h4] at h1
  have h5 : c = r ^ 2 + 1 := by
    apply Nat.eq_of_mul_eq_mul_right hpos2
    rw [h1]; ring
  rcases hc with rfl | rfl <;> omega

theorem sl2_not {N m : ℕ} (hN : XOrd N) (h : N = 2 ^ m * ((2 ^ m) ^ 2 - 1)) : False := by
  obtain ⟨h20, ⟨n, c, hn, hc, hcN⟩ | h979⟩ := hN
  · have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h
        omega
      · exact hm
    have hu : Odd (c * ((2 ^ m) ^ 2 - 1)) := by
      have e : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul]; ring_nf
      rw [e]
      exact odd_mul_c hc (odd_two_pow_sub_one (by omega))
    have hw : Odd ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) :=
      Odd.mul (odd_two_pow_sub_one (by omega)) (odd_two_pow_sub_one (by omega))
    have heq : c * (2 ^ m * ((2 ^ m) ^ 2 - 1)) =
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) := h ▸ hcN
    have heq' : 2 ^ m * (c * ((2 ^ m) ^ 2 - 1)) =
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) := by rw [← heq]; ring
    have hm3 : m = 3 * n := two_pow_mul_odd_inj hu hw heq'
    subst hm3
    have e3 : 2 ^ (3 * n) = (2 ^ n) ^ 3 := pow_mul' 2 3 n
    have e2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := pow_mul' 2 2 n
    rw [e3, e2] at heq
    exact key_sl2 (2 ^ n) c (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)) hc heq
  · have hm : m < 7 := by
      by_contra hm
      push Not at hm
      have h1 : 2 ^ 7 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      have h2 : (2 ^ 7) ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h1 2
      have h3 : 2 ^ 7 * ((2 ^ 7) ^ 2 - 1) ≤ 2 ^ m * ((2 ^ m) ^ 2 - 1) :=
        Nat.mul_le_mul h1 (Nat.sub_le_sub_right h2 1)
      omega
    interval_cases m <;> omega

theorem g2_not {N m : ℕ} (hN : XOrd N)
    (h : N = (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) : False := by
  obtain ⟨h20, ⟨n, c, hn, hc, hcN⟩ | h979⟩ := hN
  · have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · simp at h
        omega
      · exact hm
    have hu : Odd (c * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) := by
      have e6 : (2 ^ m) ^ 6 = 2 ^ (6 * m) := by rw [← pow_mul]; ring_nf
      have e2 : (2 ^ m) ^ 2 = 2 ^ (2 * m) := by rw [← pow_mul]; ring_nf
      rw [e6, e2]
      exact odd_mul_c hc (Odd.mul (odd_two_pow_sub_one (by omega)) (odd_two_pow_sub_one (by omega)))
    have hw : Odd ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) :=
      Odd.mul (odd_two_pow_sub_one (by omega)) (odd_two_pow_sub_one (by omega))
    have heq : c * ((2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) =
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) := h ▸ hcN
    have e6' : (2 ^ m) ^ 6 = 2 ^ (6 * m) := by rw [← pow_mul]; ring_nf
    have heq' : 2 ^ (6 * m) * (c * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1))) =
        2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) - 1)) := by
      rw [← heq, e6']; ring
    have hmn : 6 * m = 3 * n := two_pow_mul_odd_inj hu hw heq'
    have hn2 : n = 2 * m := by omega
    subst hn2
    have e3 : 2 ^ (3 * (2 * m)) = (2 ^ m) ^ 6 := by rw [← pow_mul]; ring_nf
    have e2 : 2 ^ (2 * (2 * m)) = (2 ^ m) ^ 4 := by rw [← pow_mul]; ring_nf
    rw [e3, e2] at heq
    exact key_g2 (2 ^ m) c (by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm) hc heq
  · have hm : m < 2 := by
      by_contra hm
      push Not at hm
      have h1 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      have h2 : (2 ^ 2) ^ 6 ≤ (2 ^ m) ^ 6 := Nat.pow_le_pow_left h1 6
      have h3 : (2 ^ 2) ^ 2 ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left h1 2
      have h4 : (2 ^ 2) ^ 6 * (((2 ^ 2) ^ 6 - 1) * ((2 ^ 2) ^ 2 - 1)) ≤
          (2 ^ m) ^ 6 * (((2 ^ m) ^ 6 - 1) * ((2 ^ m) ^ 2 - 1)) :=
        Nat.mul_le_mul h2 (Nat.mul_le_mul (Nat.sub_le_sub_right h2 1) (Nat.sub_le_sub_right h3 1))
      omega
    interval_cases m <;> omega


section Excl

variable {V : Type} [CommGroup V] {X : Subgroup (MulAut V)} {U Z : Subgroup V}

theorem not_binaryNaturalSL_two' (hN : XOrd (Nat.card ↥X)) {m : ℕ} (h : BinaryNaturalSL X U Z 2 m) :
    False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hc := card_eq_of_nat_realizes1527d hπ
  rw [card_statedSL_two1527d, hF] at hc
  exact sl2_not hN hc

theorem not_g2Natural' (hN : XOrd (Nat.card ↥X)) {m : ℕ} (h : G2Natural X U Z m) : False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hcard : Nat.card ↥X = Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    have := FFC.charP_two_of_card_pow hF
    exact (Nat.card_congr (Equiv.ofBijective π
      ⟨FFC.injective_of_faithful_sec (FFC.zornQ_faithful _ le_rfl) hπ, hπ.1⟩)).symm
  rw [card_quasithinG2_1527d hF, hF] at hcard
  exact g2_not hN hcard

theorem not_g2NaturalDerived_one' (hN : XOrd (Nat.card ↥X)) (h : G2NaturalDerived X U Z 1) :
    False := by
  obtain ⟨F, _, _, hF, π, hπ⟩ := h
  have hG2 := card_quasithinG2_1527d hF
  have hfin : Finite ↥(CFSG.Open.quasithinG2 F) :=
    Nat.finite_of_card_ne_zero (by rw [hG2, hF]; norm_num)
  have h1 : Nat.card ↥X ≤ Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ :=
    Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card ↥⁅CFSG.Open.quasithinG2 F, CFSG.Open.quasithinG2 F⁆ ≤
      Nat.card ↥(CFSG.Open.quasithinG2 F) := by
    refine Subgroup.card_le_of_le ?_
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (CFSG.Open.quasithinG2 F).mul_mem
      ((CFSG.Open.quasithinG2 F).mul_mem ((CFSG.Open.quasithinG2 F).mul_mem ha hb)
        ((CFSG.Open.quasithinG2 F).inv_mem ha)) ((CFSG.Open.quasithinG2 F).inv_mem hb)
  rw [hG2, hF] at h2
  norm_num at h2
  have := hN.1
  omega

theorem not_a7Four' (hN : XOrd (Nat.card ↥X)) (h : A7Four X U Z) : False := by
  obtain ⟨α, π, hπ⟩ := h
  have h1 : Nat.card ↥X ≤ Nat.card ↥(alternatingGroup (Fin 7)) :=
    Nat.card_le_card_of_surjective π hπ.1
  rw [card_alternatingGroup1527d 7 (by norm_num)] at h1
  have := hN.1
  norm_num [Nat.factorial] at h1
  omega

theorem not_tripleA6Six' (hN : XOrd (Nat.card ↥X)) (h : TripleA6Six X U Z) : False := by
  obtain ⟨F, _, _, Γ₀, hF, -, hhat, -, π, hπ⟩ := h
  have h1 : Nat.card ↥X ≤ Nat.card ↥Γ₀ := Nat.card_le_card_of_surjective π hπ.1
  have h2 : Nat.card ↥Γ₀ = 1080 :=
    card_of_isHat1527d hhat (by
      rw [card_alternatingGroup1527d 6 (by norm_num)]
      norm_num [Nat.factorial])
  rw [h2] at h1
  have := hN.1
  omega

theorem not_alternatingNatural' (hN : XOrd (Nat.card ↥X)) {n : ℕ} (hn : 2 ≤ n) (hn7 : n ≤ 7)
    (h : AlternatingNatural X U Z n) : False := by
  refine not_alternatingNatural1527d hn ?_ h
  have := hN.1
  have h1 : n.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le hn7
  have h2 : (7 : ℕ).factorial = 5040 := by decide
  omega

end Excl

theorem natOutcome_of_part1 {V : Type} [CommGroup V] [Finite V] {J X : Subgroup (MulAut V)}
    (h1 : B51Part1 J X) (hN : XOrd (Nat.card ↥X))
    (hL45 : ∀ m : ℕ, (m = 4 ∨ m = 5) → ∀ π : ↥(StatedSL m (ZMod 2)) →* ↥X, ¬ Function.Surjective π) :
    NatOutcome X := by
  obtain ⟨-, hc⟩ := h1
  rcases hc with hi | hii | ⟨n, hiii⟩ | hiv
  · obtain ⟨-, hpair, -⟩ := hi
    rcases hpair with ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩ | ⟨m, h⟩ | h | h | h | h | h | h | h | h | h | h
    · exact (not_binaryNaturalSL_two' hN h).elim
    · obtain ⟨K, hF, hFin, hK, hreal⟩ := h
      exact Or.inl ⟨K, hF, hFin, m, hK, hreal⟩
    · obtain ⟨K, hF, hFin, hK, hreal⟩ := h
      exact Or.inr (Or.inl ⟨K, hF, hFin, m, hK, hreal⟩)
    · exact (not_g2Natural' hN h).elim
    · exact (not_g2NaturalDerived_one' hN h).elim
    · exact (not_alternatingNatural' hN (by norm_num) (by norm_num) h).elim
    · exact (not_alternatingNatural' hN (by norm_num) (by norm_num) h).elim
    · exact (not_alternatingNatural' hN (by norm_num) (by norm_num) h).elim
    · exact (not_a7Four' hN h).elim
    · exact (not_tripleA6Six' hN h).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      exact (hL45 4 (Or.inl rfl) π hπ.1).elim
    · obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
      exact (hL45 5 (Or.inr rfl) π hπ.1).elim
    · obtain ⟨π, hπ⟩ := h
      exact (hL45 4 (Or.inl rfl) π hπ.1).elim
    · obtain ⟨π, hπ⟩ := h
      exact (hL45 5 (Or.inr rfl) π hπ.1).elim
  · obtain ⟨-, n, K, hF, hFin, hK, I, π, hind, hI, hreal, -⟩ := hii
    exact Or.inr (Or.inr ⟨K, hF, hFin, n, I, π, hK, hind, hI, hreal⟩)
  · obtain ⟨-, hn, π, U₁, U₂, -, hr1, -⟩ := hiii
    exact (hL45 n hn π hr1.1).elim
  · obtain ⟨-, n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := hiv
    exact (hL45 n hn π (hreal ⟨0, hk1⟩).1).elim

end CFSG.Quasithin.SzN15
