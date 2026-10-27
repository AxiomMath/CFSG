module

public import CFSG.Quasithin.Vol2.Ch11SecAFacts12c
public import CFSG.Quasithin.Vol2.Ch11SecQ9aL34B
public import CFSG.Timmesfeld.Orders.Classical
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace C11P9B

theorem mul_sq_sub_one_mono {a b : ℕ} (h : a ≤ b) : a * (a ^ 2 - 1) ≤ b * (b ^ 2 - 1) :=
  Nat.mul_le_mul h (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)

theorem mul_sq_sub_one_ne {p a N : ℕ} (h1 : a * (a ^ 2 - 1) < N)
    (h2 : N < (a + 1) * ((a + 1) ^ 2 - 1)) : p * (p ^ 2 - 1) ≠ N := by
  intro h
  rcases Nat.lt_or_ge a p with hp | hp
  · have := mul_sq_sub_one_mono (show a + 1 ≤ p from hp)
    omega
  · have := mul_sq_sub_one_mono hp
    omega

theorem ordSL3_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 3 * ((a ^ 2 - 1) * (a ^ 3 - 1)) ≤ b ^ 3 * ((b ^ 2 - 1) * (b ^ 3 - 1)) :=
  Nat.mul_le_mul (Nat.pow_le_pow_left h 3) (Nat.mul_le_mul
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 3) 1))

theorem ordSp4_mono {a b : ℕ} (h : a ≤ b) :
    a ^ 4 * ((a ^ 2 - 1) * (a ^ 4 - 1)) ≤ b ^ 4 * ((b ^ 2 - 1) * (b ^ 4 - 1)) :=
  Nat.mul_le_mul (Nat.pow_le_pow_left h 4) (Nat.mul_le_mul
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 2) 1)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left h 4) 1))

theorem pow_three_sub_one (r : ℕ) (hr : 1 ≤ r) : r ^ 3 - 1 = (r - 1) * (r ^ 2 + r + 1) := by
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  exact Nat.sub_eq_of_eq_add (by ring)

theorem pow_four_sub_one (q : ℕ) : q ^ 4 - 1 = (q ^ 2 + 1) * (q ^ 2 - 1) := by
  rw [show q ^ 4 = (q ^ 2) ^ 2 by ring]
  have h := Nat.sq_sub_sq (q ^ 2) 1
  rwa [one_pow] at h

theorem eq_three_or_five_le {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : r = 3 ∨ 5 ≤ r := by
  have := hr.two_le
  rcases (show r = 3 ∨ r = 4 ∨ 5 ≤ r by omega) with h | h | h
  · exact Or.inl h
  · exact absurd (h ▸ hr) (by norm_num)
  · exact Or.inr h

theorem ordSL3_cases {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    (r = 3 ∧ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) = 5616) ∨
      372000 ≤ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
  rcases eq_three_or_five_le hr hr2 with rfl | h
  · exact Or.inl ⟨rfl, by norm_num⟩
  · exact Or.inr ((by norm_num : (372000 : ℕ) ≤ 5 ^ 3 * ((5 ^ 2 - 1) * (5 ^ 3 - 1))).trans
      (ordSL3_mono h))

theorem poly_SL3_int {x : ℤ} (hx : 3 ≤ x) :
    3 * ((x ^ 2 + x + 1) * ((x ^ 2 + x + 1) ^ 2 - 1)) <
      2 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1))) := by
  have h4 : 4 ≤ (x - 1) ^ 2 := by nlinarith
  have hb : 0 < 2 * x ^ 2 * (x - 1) ^ 2 - 3 * (x ^ 2 + x + 2) := by
    nlinarith [mul_nonneg (sq_nonneg x) (sub_nonneg.mpr h4)]
  have hpos : 0 < x * (x + 1) * (x ^ 2 + x + 1) *
      (2 * x ^ 2 * (x - 1) ^ 2 - 3 * (x ^ 2 + x + 2)) :=
    mul_pos (mul_pos (mul_pos (by linarith) (by linarith)) (by nlinarith)) hb
  have key : 2 * (x ^ 3 * ((x ^ 2 - 1) * (x ^ 3 - 1))) -
      3 * ((x ^ 2 + x + 1) * ((x ^ 2 + x + 1) ^ 2 - 1)) = x * (x + 1) * (x ^ 2 + x + 1) *
      (2 * x ^ 2 * (x - 1) ^ 2 - 3 * (x ^ 2 + x + 2)) := by ring
  linarith

theorem poly_SL3 {r : ℕ} (hr : 3 ≤ r) :
    3 * ((r ^ 2 + r + 1) * ((r ^ 2 + r + 1) ^ 2 - 1)) <
      2 * (r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1))) := by
  have h1 : 1 ≤ r ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ r ^ 3 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (r ^ 2 + r + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3]
  exact poly_SL3_int (by exact_mod_cast hr)

theorem poly_Sp4_int {x : ℤ} (hx : 2 ≤ x) :
    (x ^ 2 + 1) * ((x ^ 2 + 1) ^ 2 - 1) < 2 * (x ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1))) := by
  have hy : 4 ≤ x ^ 2 := by nlinarith
  have h5 : 9 ≤ (x ^ 2 - 1) ^ 2 := by nlinarith
  have hb : 0 < 2 * x ^ 2 * (x ^ 2 - 1) ^ 2 - (x ^ 2 + 2) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ x ^ 2 by linarith) (sub_nonneg.mpr h5)]
  have hpos : 0 < x ^ 2 * (x ^ 2 + 1) * (2 * x ^ 2 * (x ^ 2 - 1) ^ 2 - (x ^ 2 + 2)) :=
    mul_pos (mul_pos (by linarith) (by linarith)) hb
  have key : 2 * (x ^ 4 * ((x ^ 2 - 1) * (x ^ 4 - 1))) - (x ^ 2 + 1) * ((x ^ 2 + 1) ^ 2 - 1) =
      x ^ 2 * (x ^ 2 + 1) * (2 * x ^ 2 * (x ^ 2 - 1) ^ 2 - (x ^ 2 + 2)) := by ring
  linarith

theorem poly_Sp4 {q : ℕ} (hq : 2 ≤ q) :
    (q ^ 2 + 1) * ((q ^ 2 + 1) ^ 2 - 1) < 2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) := by
  have h1 : 1 ≤ q ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h2 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1 ≤ (q ^ 2 + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h2, h3]
  exact poly_Sp4_int (by exact_mod_cast hq)

theorem false_of_L2p_SL3 {p r N d : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hr : r.Prime)
    (hr2 : r ≠ 2) (h1 : 2 * N = p * (p ^ 2 - 1)) (hd : d ≤ 3)
    (h2 : N * d = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1))) : False := by
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hpN : p ∣ N := by
    rcases (Nat.Prime.dvd_mul hp).mp (⟨p ^ 2 - 1, h1⟩ : p ∣ 2 * N) with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · exact h
  have hpS : p ∣ r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
    rw [← h2]
    exact Dvd.dvd.mul_right hpN d
  have hR : p ≤ r ^ 2 + r + 1 := by
    rcases (Nat.Prime.dvd_mul hp).mp hpS with h | h
    · have := (Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow h)
      omega
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have h9 : 9 ≤ r ^ 2 := by nlinarith
      have := Nat.le_of_dvd (by omega) h
      omega
    · rw [pow_three_sub_one r (by omega)] at h
      rcases (Nat.Prime.dvd_mul hp).mp h with h | h
      · have := Nat.le_of_dvd (by omega) h
        omega
      · exact Nat.le_of_dvd (by positivity) h
  have hmono := mul_sq_sub_one_mono hR
  have hS3 : r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) ≤ 3 * N := by
    rw [← h2, mul_comm 3 N]
    exact Nat.mul_le_mul_left N hd
  have := poly_SL3 hr3
  omega

theorem false_of_L2p_Sp4 {p m N : ℕ} (hp : p.Prime) (hp11 : 11 ≤ p) (hm : 1 ≤ m)
    (h1 : 2 * N = p * (p ^ 2 - 1))
    (h2 : N = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1))) : False := by
  have hq : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hq2 : 0 < (2 ^ m) ^ 2 - 1 := by
    have : 4 ≤ (2 ^ m) ^ 2 := by
      calc 4 = 2 * 2 := rfl
        _ ≤ 2 ^ m * 2 ^ m := Nat.mul_le_mul hq hq
        _ = (2 ^ m) ^ 2 := (sq _).symm
    omega
  have hpN : p ∣ N := by
    rcases (Nat.Prime.dvd_mul hp).mp (⟨p ^ 2 - 1, h1⟩ : p ∣ 2 * N) with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · exact h
  have hR : p ≤ (2 ^ m) ^ 2 + 1 := by
    rw [h2] at hpN
    rcases (Nat.Prime.dvd_mul hp).mp hpN with h | h
    · have := Nat.le_of_dvd (by norm_num) (hp.dvd_of_dvd_pow (hp.dvd_of_dvd_pow h))
      omega
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · have := Nat.le_of_dvd hq2 h
      omega
    rw [pow_four_sub_one] at h
    rcases (Nat.Prime.dvd_mul hp).mp h with h | h
    · exact Nat.le_of_dvd (by positivity) h
    · have := Nat.le_of_dvd hq2 h
      omega
  have hmono := mul_sq_sub_one_mono hR
  have := poly_Sp4 hq
  rw [h2] at h1
  omega

theorem card_of_isPSL_three_two_two {X : Type} [Group X] (h : IsPSL 3 2 2 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem card_of_isPSL_four_two_one {X : Type} [Group X] (h : IsPSL 4 2 1 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_of_isPSL_five_two_one {X : Type} [Group X] (h : IsPSL 5 2 1 X) :
    Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

theorem two_mul_card_of_isPSL2 {X : Type} [Group X] {p : ℕ} (hp2 : p ≠ 2)
    (h : IsPSL 2 p 1 X) : 2 * Nat.card X = p * (p ^ 2 - 1) := by
  obtain ⟨⟨hp, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hg : Nat.gcd 2 (p - 1) = 2 :=
    Nat.gcd_eq_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd odd_one))
  have h2 : 2 ∣ p * (p ^ 2 - 1) :=
    Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd hodd.pow odd_one)) p
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (n := 2) (by norm_num), hK, Finset.Icc_self, Finset.prod_singleton, hg,
    show (2 * (2 - 1) / 2 : ℕ) = 1 from rfl, pow_one]
  exact Nat.mul_div_cancel' h2

theorem card_of_isSL3 {X : Type} [Group X] {r : ℕ} (h : IsSL3 r X) :
    Nat.card X = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := h
  rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 3 K).symm).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 3) (by norm_num), hK,
    show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide, Finset.prod_pair (by norm_num),
    show (3 * (3 - 1) / 2 : ℕ) = 3 from rfl]

theorem card_mul_gcd_of_isPSL3 {X : Type} [Group X] {r : ℕ} (h : IsPSL 3 r 1 X) :
    Nat.card X * Nat.gcd 3 (r - 1) = r ^ 3 * ((r ^ 2 - 1) * (r ^ 3 - 1)) := by
  obtain ⟨⟨hr, -⟩, K, _, _, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL
    (n := 3) (by norm_num), hK, show Finset.Icc 2 3 = ({2, 3} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), show (3 * (3 - 1) / 2 : ℕ) = 3 from rfl]
  refine Nat.div_mul_cancel ((Nat.gcd_dvd_right 3 (r - 1)).trans ?_)
  refine Dvd.dvd.mul_left (Dvd.dvd.mul_left ?_ _) _
  rw [pow_three_sub_one r hr.one_le]
  exact Dvd.intro _ rfl

theorem card_of_isPSp4 {X : Type} [Group X] {m : ℕ} (h : IsPSp4 2 m X) :
    2 ≤ m ∧ Nat.card X = (2 ^ m) ^ 4 * (((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 4 - 1)) := by
  have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.2.1 rfl
  obtain ⟨⟨-, hm, -, hne⟩, -⟩ := h
  have hm2 : 2 ≤ m := by
    by_contra h1
    have : m = 1 := by omega
    subst this
    exact hne (by decide)
  refine ⟨hm2, ?_⟩
  have hodd : Odd (2 ^ m - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow ((Nat.even_pow).mpr ⟨even_two, by omega⟩) odd_one
  rw [hc, ordBC, show Finset.Icc 1 2 = ({1, 2} : Finset ℕ) by decide,
    Finset.prod_pair (by norm_num), show Nat.gcd 2 (2 ^ m - 1) = 1 from
      Nat.coprime_two_left.mpr hodd, Nat.div_one, show (2 * 2 : ℕ) = 4 from rfl,
    show (2 * 1 : ℕ) = 2 from rfl]

end C11P9B

open C11P9B

theorem factNoOverlap_holds : FactNoOverlap := by
  intro X _ _ hX
  have hM11 : ∀ _ : IsSporadic .M11 X, Nat.card X = 7920 := fun ⟨e⟩ => by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M11
  rcases hX with hA | ⟨p, hp, hp11, hB⟩ | ⟨F, _, _, hF, ⟨e⟩⟩
  · have hc := card_of_isPSL_three_two_two hA
    refine ⟨fun r hr hr2 => ⟨fun h => ?_, fun h => ?_⟩, fun m h => ?_, fun h => ?_,
      SecS.factL34NotL42_holds X hA, fun h => ?_⟩
    · have := card_of_isSL3 h
      rcases ordSL3_cases hr hr2 with ⟨-, h5⟩ | h5 <;> omega
    · have := card_mul_gcd_of_isPSL3 h
      have hd := Nat.gcd_le_left (r - 1) (show 0 < 3 by norm_num)
      rw [hc] at this
      rcases ordSL3_cases hr hr2 with ⟨rfl, h5⟩ | h5
      · rw [show Nat.gcd 3 (3 - 1) = 1 by norm_num] at this
        omega
      · omega
    · obtain ⟨hm, hc'⟩ := card_of_isPSp4 h
      have := (by norm_num : (979200 : ℕ) ≤ (2 ^ 2) ^ 4 * (((2 ^ 2) ^ 2 - 1) *
        ((2 ^ 2) ^ 4 - 1))).trans (ordSp4_mono (Nat.pow_le_pow_right (by norm_num) hm))
      omega
    · have := hM11 h
      omega
    · have := card_of_isPSL_five_two_one h
      omega
  · have hc := two_mul_card_of_isPSL2 (by omega) hB
    refine ⟨fun r hr hr2 => ⟨fun h => ?_, fun h => ?_⟩, fun m h => ?_, fun h => ?_,
      fun h => ?_, fun h => ?_⟩
    · exact false_of_L2p_SL3 hp hp11 hr hr2 hc (d := 1) (by norm_num)
        (by rw [mul_one]; exact card_of_isSL3 h)
    · exact false_of_L2p_SL3 hp hp11 hr hr2 hc (Nat.gcd_le_left _ (by norm_num))
        (card_mul_gcd_of_isPSL3 h)
    · obtain ⟨hm, hc'⟩ := card_of_isPSp4 h
      exact false_of_L2p_Sp4 hp hp11 (by omega) hc hc'
    · rw [hM11 h] at hc
      exact mul_sq_sub_one_ne (a := 25) (by norm_num) (by norm_num) hc.symm
    · rw [card_of_isPSL_four_two_one h] at hc
      exact mul_sq_sub_one_ne (a := 34) (by norm_num) (by norm_num) hc.symm
    · rw [card_of_isPSL_five_two_one h] at hc
      exact mul_sq_sub_one_ne (a := 271) (by norm_num) (by norm_num) hc.symm
  · have hc : Nat.card X = 60 := by
      rw [Nat.card_congr e.toEquiv,
        CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (n := 2) (by norm_num), hF]
      decide
    refine ⟨fun r hr hr2 => ⟨fun h => ?_, fun h => ?_⟩, fun m h => ?_, fun h => ?_,
      fun h => ?_, fun h => ?_⟩
    · have := card_of_isSL3 h
      rcases ordSL3_cases hr hr2 with ⟨-, h5⟩ | h5 <;> omega
    · have := card_mul_gcd_of_isPSL3 h
      have hd := Nat.gcd_le_left (r - 1) (show 0 < 3 by norm_num)
      rw [hc] at this
      rcases ordSL3_cases hr hr2 with ⟨-, h5⟩ | h5 <;> omega
    · obtain ⟨hm, hc'⟩ := card_of_isPSp4 h
      have := (by norm_num : (979200 : ℕ) ≤ (2 ^ 2) ^ 4 * (((2 ^ 2) ^ 2 - 1) *
        ((2 ^ 2) ^ 4 - 1))).trans (ordSp4_mono (Nat.pow_le_pow_right (by norm_num) hm))
      omega
    · have := hM11 h
      omega
    · have := card_of_isPSL_four_two_one h
      omega
    · have := card_of_isPSL_five_two_one h
      omega

end CFSG.Quasithin.Vol2.Ch11.SecA
