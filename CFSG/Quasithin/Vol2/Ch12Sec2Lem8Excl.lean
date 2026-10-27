module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem8L34
public import CFSG.Timmesfeld.Orders.ClassicalLinear
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.L34

open CFSG.Assembly.LowTwoRank CFSG.Open

@[expose] def pslOrd (q : ℕ) : ℕ := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1)

@[expose] def psuOrd (q : ℕ) : ℕ := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) / Nat.gcd 3 (q + 1)

@[expose] def slOrd (q : ℕ) : ℕ := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1))

@[expose] def suOrd (q : ℕ) : ℕ := q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1))

theorem prod_Icc_two_three (f : ℕ → ℕ) : ∏ j ∈ Finset.Icc 2 3, f j = f 2 * f 3 := by
  rw [show Finset.Icc 2 3 = {2, 3} by rfl, Finset.prod_pair (by norm_num)]

@[expose] def ListOrd (N : ℕ) : Prop :=
  N = 20160 ∨ N = 9999360 ∨ N = 6048 ∨ N = 360 ∨ N = 2520 ∨ N = 1080 ∨ N = 7560

theorem big_bound {q : ℕ} (hq : 9 ≤ q) :
    729 * (80 * 728) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h3 : 729 ≤ q ^ 3 := by
    calc 729 = 9 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h2 : 81 ≤ q ^ 2 := by
    calc 81 = 9 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
  exact Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))

theorem big_bound' {q : ℕ} (hq : 9 ≤ q) :
    729 * (80 * 728) ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
  (big_bound hq).trans (Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl (by omega)))

theorem gcd_three_le (n : ℕ) : Nat.gcd 3 n ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left 3 n)

theorem gcd_three_pos (n : ℕ) : 0 < Nat.gcd 3 n := Nat.gcd_pos_of_pos_left n (by norm_num)

theorem pslOrd_listOrd {q : ℕ} (hq : 2 ≤ q) (hN : ListOrd (pslOrd q)) : q = 4 := by
  by_cases h9 : 9 ≤ q
  · exfalso
    have hb := big_bound h9
    have hd : 729 * (80 * 728) / 3 ≤ pslOrd q :=
      (Nat.div_le_div_left (gcd_three_le _) (gcd_three_pos _)).trans'
        (Nat.div_le_div_right hb)
    unfold ListOrd at hN
    omega
  · interval_cases q <;> simp [pslOrd, ListOrd] at hN ⊢

theorem psuOrd_not_listOrd {q : ℕ} (hq : 2 ≤ q) (hq3 : q % 3 = 2) : ¬ ListOrd (psuOrd q) := by
  intro hN
  by_cases h9 : 9 ≤ q
  · have hb := big_bound' h9
    have hd : 729 * (80 * 728) / 3 ≤ psuOrd q :=
      (Nat.div_le_div_left (gcd_three_le _) (gcd_three_pos _)).trans'
        (Nat.div_le_div_right hb)
    unfold ListOrd at hN
    omega
  · interval_cases q <;> simp_all [psuOrd, ListOrd]

theorem slOrd_not_listOrd {q : ℕ} (hq : 2 ≤ q) : ¬ ListOrd (slOrd q) := by
  intro hN
  by_cases h9 : 9 ≤ q
  · have hb := big_bound h9
    unfold ListOrd slOrd at hN
    omega
  · interval_cases q <;> simp [slOrd, ListOrd] at hN

theorem suOrd_listOrd {q : ℕ} (hq : 2 ≤ q) (hN : ListOrd (suOrd q)) : q = 3 := by
  by_cases h9 : 9 ≤ q
  · exfalso
    have hb := big_bound' h9
    unfold ListOrd suOrd at hN
    omega
  · interval_cases q <;> simp [suOrd, ListOrd] at hN ⊢

theorem two_le_card_field (K : Type) [Field K] [Finite K] : 2 ≤ Nat.card K :=
  Finite.one_lt_card_iff_nontrivial.mpr inferInstance

theorem card_of_isPSLEps3q {X : Type} [Group X] {s : Bool} {q : ℕ} (h : IsPSLEps3q s q X) :
    2 ≤ q ∧ Nat.card X = cond s (pslOrd q) (psuOrd q) := by
  obtain ⟨p, e, hp, he, rfl, hX⟩ := h
  have hq2 : 2 ≤ p ^ e := by
    calc 2 ≤ p := hp.two_le
      _ ≤ p ^ e := Nat.le_self_pow (by omega) p
  refine ⟨hq2, ?_⟩
  cases s with
  | true =>
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
    rw [Bool.cond_true, Nat.card_congr φ.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hK,
      prod_Icc_two_three]
    rfl
  | false =>
    obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
    rw [Bool.cond_false, Nat.card_congr φ.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU hp he hK (by norm_num)]
    have h1 : 1 ≤ p ^ e := by omega
    have e2 : ((((p ^ e : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat) = (p ^ e) ^ 2 - 1 := by
      have : (1 : ℕ) ≤ (p ^ e) ^ 2 := Nat.one_le_pow _ _ (by omega)
      rw [show ((-1 : ℤ)) ^ 2 = 1 by norm_num, show (((p ^ e : ℕ) : ℤ) ^ 2 - 1) =
        (((p ^ e) ^ 2 - 1 : ℕ) : ℤ) by push_cast [this]; ring, Int.toNat_natCast]
    have e3 : ((((p ^ e : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat) = (p ^ e) ^ 3 + 1 := by
      rw [show ((-1 : ℤ)) ^ 3 = -1 by norm_num, show (((p ^ e : ℕ) : ℤ) ^ 3 - -1) =
        (((p ^ e) ^ 3 + 1 : ℕ) : ℤ) by push_cast; ring, Int.toNat_natCast]
    have hprod : ∏ i ∈ Finset.Icc 2 3, ((((p ^ e : ℕ) : ℤ) ^ i - (-1) ^ i).toNat) =
        ((p ^ e) ^ 2 - 1) * ((p ^ e) ^ 3 + 1) := by
      rw [prod_Icc_two_three, e2, e3]
    rw [hprod]
    rfl

theorem card_of_isSLEps3 {X : Type} [Group X] {s : Bool} {q : ℕ} (h : IsSLEps3 s q X) :
    2 ≤ q ∧ Nat.card X = cond s (slOrd q) (suOrd q) := by
  cases s with
  | true =>
    obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
    refine ⟨hK ▸ two_le_card_field K, ?_⟩
    rw [Bool.cond_true, Nat.card_congr φ.toEquiv,
      ← Nat.card_congr (specialLinearGroupEquivStatedSL 3 K).toEquiv,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK,
      prod_Icc_two_three]
    rfl
  | false =>
    obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h
    obtain ⟨p, hchar⟩ := CharP.exists K
    have := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K p
    have : Fact p.Prime := ⟨hp⟩
    have hqdvd : q ∣ p ^ (n : ℕ) := by
      rw [← hn, ← Nat.card_eq_fintype_card, hK]
      exact dvd_pow_self q (by norm_num)
    obtain ⟨m, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hqdvd
    have hq2 : 2 ≤ p ^ m := by
      have h4 := two_le_card_field K
      rw [hK] at h4
      by_contra hlt
      have : p ^ m ≤ 1 := by omega
      have : (p ^ m) ^ 2 ≤ 1 := by
        calc (p ^ m) ^ 2 ≤ 1 ^ 2 := Nat.pow_le_pow_left this 2
          _ = 1 := by norm_num
      omega
    refine ⟨hq2, ?_⟩
    rw [Bool.cond_false, Nat.card_congr φ.toEquiv,
      CFSG.SectionRank.OddCover.card_statedSU_three hK]
    unfold suOrd
    ring

@[expose] def σ15 : Equiv.Perm (Fin 8) := List.formPerm [0, 1, 2] * List.formPerm [3, 4, 5, 6, 7]

theorem orderOf_σ15 : orderOf σ15 = 15 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide +kernel, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide +kernel

theorem not_isPSL_three_four_of_alternating_eight
    {X : Type} [Group X]
    (eA : X ≃* alternatingGroup (Fin 8)) (h : IsPSLEps3q true 4 X) : False := by
  obtain ⟨p, e, hp, he, hq, hX⟩ := h
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
  rw [← hq] at hK
  have hσ : σ15 ∈ alternatingGroup (Fin 8) := Equiv.Perm.mem_alternatingGroup.mpr (by decide)
  have hord : orderOf (⟨σ15, hσ⟩ : alternatingGroup (Fin 8)) = 15 := by
    rw [Subgroup.orderOf_mk, orderOf_σ15]
  have h15 : orderOf (φ (eA.symm ⟨σ15, hσ⟩)) = 15 := by
    rw [MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, hord]
  exact no_orderOf_eq_fifteen hK _ h15

theorem not_isPSLEps3q_of_card
    {X : Type} [Group X] (hX : ListOrd (Nat.card X))
    (h20160 : Nat.card X = 20160 → Nonempty (X ≃* alternatingGroup (Fin 8))) (s : Bool) (q : ℕ)
    (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1)) (h : IsPSLEps3q s q X) : False := by
  obtain ⟨hq2, hcard⟩ := card_of_isPSLEps3q h
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hX
    have h4 := pslOrd_listOrd hq2 hX
    subst h4
    obtain ⟨eA⟩ := h20160 (by rw [hcard]; rfl)
    exact not_isPSL_three_four_of_alternating_eight eA h
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hX
    have hq3 : q % 3 = 2 := by
      simp only [Bool.false_eq_true, ↓reduceIte] at hq
      have := Int.emod_emod_of_dvd (q : ℤ) (dvd_refl (3 : ℤ))
      unfold Int.ModEq at hq
      omega
    exact psuOrd_not_listOrd hq2 hq3 hX

theorem not_isSLEps3_of_card {X : Type} [Group X] (hX : ListOrd (Nat.card X)) (s : Bool) (q : ℕ)
    (hq : Int.ModEq 3 (q : ℤ) (if s then 1 else -1)) (h : IsSLEps3 s q X) : False := by
  obtain ⟨hq2, hcard⟩ := card_of_isSLEps3 h
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hX
    exact slOrd_not_listOrd hq2 hX
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hX
    have h3 := suOrd_listOrd hq2 hX
    subst h3
    simp only [Bool.false_eq_true, ↓reduceIte] at hq
    unfold Int.ModEq at hq
    omega

theorem not_isSLEps3_of_card_hat {X : Type} [Group X]
    (hX : Nat.card X = 1080 ∨ Nat.card X = 7560) (s : Bool) (q : ℕ) (h : IsSLEps3 s q X) :
    False := by
  obtain ⟨hq2, hcard⟩ := card_of_isSLEps3 h
  have hL : ListOrd (Nat.card X) := by unfold ListOrd; omega
  cases s with
  | true =>
    rw [Bool.cond_true] at hcard
    rw [hcard] at hL
    exact slOrd_not_listOrd hq2 hL
  | false =>
    rw [Bool.cond_false] at hcard
    rw [hcard] at hL hX
    have h3 := suOrd_listOrd hq2 hL
    subst h3
    simp [suOrd] at hX

end CFSG.Quasithin.H13.L34
