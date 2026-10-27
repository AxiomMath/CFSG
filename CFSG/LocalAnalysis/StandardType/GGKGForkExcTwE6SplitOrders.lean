module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Frame
public import CFSG.ClassicalInvolution.Orders.Twisted

public section

namespace CFSG.StandardType

namespace ExcTwE6Split

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

private theorem ggKGTq_pow_sub_one_ne_zero {q d : ℕ} (hq : 1 < q) (hd : d ≠ 0) :
    q ^ d - 1 ≠ 0 := by
  have h : 1 < q ^ d := one_lt_pow₀ hq hd
  omega

private theorem ggKGTq_padicValNat_list_prod {p : ℕ} [Fact p.Prime] (l : List ℕ)
    (h : ∀ a ∈ l, a ≠ 0) :
    padicValNat p l.prod = (l.map (padicValNat p)).sum := by
  induction l with
  | nil => simp
  | cons a t ih =>
    have ha : a ≠ 0 := h a (by simp)
    have ht : ∀ b ∈ t, b ≠ 0 := fun b hb => h b (by simp [hb])
    have hprod : t.prod ≠ 0 := List.prod_ne_zero (fun h0 => ht 0 h0 rfl)
    rw [List.prod_cons, padicValNat.mul ha hprod, ih ht, List.map_cons, List.sum_cons]

private theorem ggKGTq_not_dvd_pow_add_one {p q e : ℕ} (hp5 : 5 ≤ p) (hq : 1 < q)
    (hpq : p ∣ q - 1) : ¬ p ∣ q ^ e + 1 := by
  have hqmod : (q : ZMod p) = 1 := by
    have h : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (q - 1) p).mpr hpq
    rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_eq_zero] at h
    exact h
  intro hd
  have hz : ((q ^ e + 1 : ℕ) : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff (q ^ e + 1) p).mpr hd
  rw [Nat.cast_add, Nat.cast_pow, Nat.cast_one, hqmod, one_pow] at hz
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    rw [show ((2 : ℕ) : ZMod p) = (1 : ZMod p) + 1 by norm_num]
    exact hz
  have hp2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
    intro h
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  exact hp2 h2

private theorem ggKGTq_padicValNat_prodT {p q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hq : 1 < q) (hpq : p ∣ q - 1) :
    padicValNat p (q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1)) = 4 * padicValNat p (q - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp_not_dvd_q : ¬ p ∣ q := by
    intro hd
    have h1 : p ∣ q - (q - 1) := Nat.dvd_sub hd hpq
    have hsub : q - (q - 1) = 1 := by omega
    rw [hsub] at h1
    exact hp.not_dvd_one h1
  have hpodd : Odd p := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact Nat.odd_iff.mpr h
  have hLTE : ∀ d : ℕ, d ≠ 0 →
      padicValNat p (q ^ d - 1) = padicValNat p (q - 1) + padicValNat p d := by
    intro d hd
    have := padicValNat.pow_sub_pow (p := p) (x := q) (y := 1) hpodd hq hpq hp_not_dvd_q hd
    simpa using this
  have h36 : padicValNat p (q ^ 36) = 0 := by
    rw [padicValNat.pow, padicValNat.eq_zero_of_not_dvd hp_not_dvd_q]
  have h2 : padicValNat p 2 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd; have := Nat.le_of_dvd (by norm_num) hd; omega)
  have h6 : padicValNat p 6 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd
    rw [show (6 : ℕ) = 2 * 3 by norm_num] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h2' | h3'
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2'; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'; omega)
  have h8 : padicValNat p 8 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hd
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd); omega)
  have h12 : padicValNat p 12 = 0 := padicValNat.eq_zero_of_not_dvd (by
    intro hd
    rw [show (12 : ℕ) = 2 ^ 2 * 3 by norm_num] at hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with h2' | h3'
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2'); omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'; omega)
  have h9p : padicValNat p (q ^ 9 + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (ggKGTq_not_dvd_pow_add_one hp5 hq hpq)
  have h5p : padicValNat p (q ^ 5 + 1) = 0 :=
    padicValNat.eq_zero_of_not_dvd (ggKGTq_not_dvd_pow_add_one hp5 hq hpq)
  have hne : ∀ a ∈ ([q ^ 36, q ^ 12 - 1, q ^ 9 + 1, q ^ 8 - 1, q ^ 6 - 1, q ^ 5 + 1,
      q ^ 2 - 1] : List ℕ), a ≠ 0 := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact pow_ne_zero 36 (by omega)
    · exact ggKGTq_pow_sub_one_ne_zero hq (by norm_num)
    · omega
    · exact ggKGTq_pow_sub_one_ne_zero hq (by norm_num)
    · exact ggKGTq_pow_sub_one_ne_zero hq (by norm_num)
    · omega
    · exact ggKGTq_pow_sub_one_ne_zero hq (by norm_num)
  have hAeq : q ^ 36 * (q ^ 12 - 1) * (q ^ 9 + 1) * (q ^ 8 - 1) * (q ^ 6 - 1) *
      (q ^ 5 + 1) * (q ^ 2 - 1) =
      ([q ^ 36, q ^ 12 - 1, q ^ 9 + 1, q ^ 8 - 1, q ^ 6 - 1, q ^ 5 + 1,
        q ^ 2 - 1] : List ℕ).prod := by
    simp only [List.prod_cons, List.prod_nil, mul_one]
    ring
  rw [hAeq, ggKGTq_padicValNat_list_prod _ hne]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  rw [h36, hLTE 12 (by norm_num), h9p, hLTE 8 (by norm_num), hLTE 6 (by norm_num),
    h5p, hLTE 2 (by norm_num)]
  rw [h12, h8, h6, h2]
  ring

theorem padicValNat_card_twE6_split
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n - 1) :
    padicValNat p (Nat.card (twistedE6RootGroup K σ)) = 4 * padicValNat p (2 ^ n - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hK2 : 1 < Nat.card K := Finite.one_lt_card
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    rw [hn0] at hK
    simp only [pow_zero, one_pow] at hK
    omega
  have hq1 : 1 < 2 ^ n := one_lt_pow₀ (by norm_num) (by omega)
  have hcard := CFSG.ClassicalInvolution.card_graphFixedRootGroup_E6 (p := 2) (f := n)
    Nat.prime_two hn hK σ.toRingHom (fun c => hσ c)
  have hg_dvd : Nat.gcd 3 (2 ^ n + 1) ∣ (2 ^ n) ^ 2 - 1 :=
    dvd_trans (Nat.gcd_dvd_right 3 (2 ^ n + 1)) (by
      have h : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        simpa using Nat.sq_sub_sq (2 ^ n) 1
      rw [h]; exact dvd_mul_right _ _)
  have hgA : Nat.gcd 3 (2 ^ n + 1) ∣
      (2 ^ n) ^ 36 * ((2 ^ n) ^ 12 - 1) * ((2 ^ n) ^ 9 + 1) * ((2 ^ n) ^ 8 - 1) *
        ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 5 + 1) * ((2 ^ n) ^ 2 - 1) :=
    dvd_mul_of_dvd_right hg_dvd _
  have hp_not_dvd_three : ¬ p ∣ 3 := by
    intro h
    have := Nat.le_of_dvd (by norm_num) h
    omega
  have hpg : padicValNat p (Nat.gcd 3 (2 ^ n + 1)) = 0 :=
    padicValNat.eq_zero_of_not_dvd (fun hd =>
      hp_not_dvd_three (dvd_trans hd (Nat.gcd_dvd_left 3 (2 ^ n + 1))))
  have hvalA : padicValNat p (ordTwistedE6 (2 ^ n)) =
      padicValNat p ((2 ^ n) ^ 36 * ((2 ^ n) ^ 12 - 1) * ((2 ^ n) ^ 9 + 1) *
        ((2 ^ n) ^ 8 - 1) * ((2 ^ n) ^ 6 - 1) * ((2 ^ n) ^ 5 + 1) * ((2 ^ n) ^ 2 - 1)) := by
    have hdiv := padicValNat.div_of_dvd (p := p) hgA
    rw [hpg, tsub_zero] at hdiv
    simpa only [ordTwistedE6] using hdiv
  rw [hcard, hvalA, ggKGTq_padicValNat_prodT (q := 2 ^ n) hp hp5 hq1 hpq]

end ExcTwE6Split

end CFSG.StandardType

end
