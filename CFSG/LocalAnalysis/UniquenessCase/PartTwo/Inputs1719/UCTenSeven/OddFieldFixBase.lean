module

public import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafInputs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Open.SignalizerFunctorDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven

open Subgroup
open CFSG.ComponentClassification.CatLeaf

theorem factorization_two_pow_sub_one_of_odd {x k : ℕ} (hx : Odd x) (hk : Odd k) :
    (x ^ k - 1).factorization 2 = (x - 1).factorization 2 := by
  rcases eq_or_ne x 1 with hx1 | hxne
  · subst x; simp
  have hxpos : 0 < x := hx.pos
  set g : ℕ := ∑ i ∈ Finset.range k, x ^ i with hgdef
  have hoddg : Odd g := by
    rw [hgdef, Finset.odd_sum_iff_odd_card_odd]
    have hfilt : {i ∈ Finset.range k | Odd (x ^ i)} = Finset.range k := by
      ext i
      simp [hx.pow]
    rw [hfilt, Finset.card_range]
    exact hk
  have hg0 : g ≠ 0 := hoddg.pos.ne'
  have hprod : x ^ k - 1 = (x - 1) * g := by
    rw [hgdef, mul_comm, geom_sum_mul_of_one_le (Nat.succ_le_of_lt hxpos) k]
  have hfac : g.factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat hoddg)
  have hx1' : x - 1 ≠ 0 := by omega
  rw [hprod, Nat.factorization_mul hx1' hg0, Finsupp.add_apply, hfac, add_zero]

theorem factorization_two_pow_add_one_of_odd {x k : ℕ} (hx : Odd x) (hk : Odd k) :
    (x ^ k + 1).factorization 2 = (x + 1).factorization 2 := by
  rcases eq_or_ne x 1 with hx1 | hxne
  · subst x; simp
  have hx3 : 3 ≤ x := by
    rcases hx with ⟨m, hm⟩
    omega
  have hx2odd : Odd (x ^ 2) := hx.pow
  have hsub1 := factorization_two_pow_sub_one_of_odd (x := x ^ 2) (k := k) hx2odd hk
  have hsub2 := factorization_two_pow_sub_one_of_odd (x := x) (k := k) hx hk
  have hpow : (x ^ 2) ^ k = (x ^ k) ^ 2 := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hsq1 : (x ^ 2) ^ k - 1 = (x ^ k - 1) * (x ^ k + 1) := by
    rw [hpow]
    conv_lhs => rw [← one_pow 2]
    rw [Nat.sq_sub_sq]
    ring
  have hsq2 : x ^ 2 - 1 = (x - 1) * (x + 1) := by
    conv_lhs => rw [← one_pow 2]
    rw [Nat.sq_sub_sq]
    ring
  have hA0 : x ^ k - 1 ≠ 0 := by
    have hk0 : k ≠ 0 := hk.pos.ne'
    have hx1 : 1 < x := by omega
    have hlt : 1 < x ^ k := Nat.one_lt_pow hk0 hx1
    omega
  have hB0 : x ^ k + 1 ≠ 0 := by omega
  have hC0 : x - 1 ≠ 0 := by omega
  have hD0 : x + 1 ≠ 0 := by omega
  have hAB : (x ^ k - 1).factorization 2 + (x ^ k + 1).factorization 2 =
      (x - 1).factorization 2 + (x + 1).factorization 2 := by
    have h := hsub1
    rw [hsq1, hsq2, Nat.factorization_mul hA0 hB0, Nat.factorization_mul hC0 hD0,
      Finsupp.add_apply, Finsupp.add_apply] at h
    exact h
  have hAC : (x ^ k - 1).factorization 2 = (x - 1).factorization 2 := hsub2
  omega

private def V2Eq (a b : ℕ) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a.factorization 2 = b.factorization 2

private theorem V2Eq.mul {a b a' b' : ℕ} (h : V2Eq a a') (h' : V2Eq b b') :
    V2Eq (a * b) (a' * b') := by
  obtain ⟨ha, ha', hfa⟩ := h
  obtain ⟨hb, hb', hfb⟩ := h'
  refine ⟨mul_ne_zero ha hb, mul_ne_zero ha' hb', ?_⟩
  rw [Nat.factorization_mul ha hb, Nat.factorization_mul ha' hb']
  simp only [Finsupp.add_apply]
  omega

private theorem V2Eq.one : V2Eq 1 1 := ⟨one_ne_zero, one_ne_zero, rfl⟩

private theorem V2Eq.prod {ι : Type*} {s : Finset ι} {f g : ι → ℕ}
    (h : ∀ i ∈ s, V2Eq (f i) (g i)) : V2Eq (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using V2Eq.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem V2Eq.of_odd {a b : ℕ} (ha : Odd a) (hb : Odd b) : V2Eq a b := by
  refine ⟨ha.pos.ne', hb.pos.ne', ?_⟩
  rw [Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat ha),
      Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat hb)]

private theorem three_le_pow {y p : ℕ} (hy3 : 3 ≤ y) (hp : 1 ≤ p) : 3 ≤ y ^ p :=
  calc 3 ≤ y := hy3
    _ = y ^ 1 := (pow_one y).symm
    _ ≤ y ^ p := Nat.pow_le_pow_right (by omega) hp

private theorem V2Eq.pow_sub_one {x p : ℕ} (hx : Odd x) (hx3 : 3 ≤ x) (hp : Odd p)
    {k : ℕ} (hk : 1 ≤ k) : V2Eq ((x ^ p) ^ k - 1) (x ^ k - 1) := by
  have hy3 : 3 ≤ x ^ k := three_le_pow hx3 hk
  have hz3 : 3 ≤ (x ^ k) ^ p := three_le_pow hy3 hp.pos
  have e : (x ^ p) ^ k = (x ^ k) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨by omega, by omega, ?_⟩
  rw [e]
  exact factorization_two_pow_sub_one_of_odd (hx.pow) hp

private theorem V2Eq.pow_add_one {x p : ℕ} (hx : Odd x) (hx3 : 3 ≤ x) (hp : Odd p)
    {k : ℕ} (_hk : 1 ≤ k) : V2Eq ((x ^ p) ^ k + 1) (x ^ k + 1) := by
  have e : (x ^ p) ^ k = (x ^ k) ^ p := by rw [← pow_mul, ← pow_mul, mul_comm]
  refine ⟨by positivity, by positivity, ?_⟩
  rw [e]
  exact factorization_two_pow_add_one_of_odd (hx.pow) hp

private theorem V2Eq.pow_pow {x p N : ℕ} (hx : Odd x) : V2Eq ((x ^ p) ^ N) (x ^ N) :=
  V2Eq.of_odd (hx.pow.pow) (hx.pow)

private theorem V2Eq.tri {x p : ℕ} (hx : Odd x) :
    V2Eq ((x ^ p) ^ 8 + (x ^ p) ^ 4 + 1) (x ^ 8 + x ^ 4 + 1) := by
  apply V2Eq.of_odd
  · exact (hx.pow.pow.add_odd hx.pow.pow).add_one
  · exact (hx.pow.add_odd hx.pow).add_one

private theorem V2Eq.numerator (t : CFSG.Open.StatedLieTag) (n : ℕ) {x p : ℕ}
    (hx : Odd x) (hx3 : 3 ≤ x) (hp : Odd p)
    (hn : (t = .POmegaPlus ∨ t = .POmegaMinus) → 1 ≤ n) :
    V2Eq (lieOrderNumerator t n (x ^ p)) (lieOrderNumerator t n x) := by
  have hs : ∀ {k : ℕ}, 1 ≤ k → V2Eq ((x ^ p) ^ k - 1) (x ^ k - 1) :=
    fun hk => V2Eq.pow_sub_one hx hx3 hp hk
  have ha : ∀ {k : ℕ}, 1 ≤ k → V2Eq ((x ^ p) ^ k + 1) (x ^ k + 1) :=
    fun hk => V2Eq.pow_add_one hx hx3 hp hk
  have h1 : V2Eq (x ^ p - 1) (x - 1) := by simpa [one_pow] using hs (k := 1) le_rfl
  have h1' : V2Eq (x ^ p + 1) (x + 1) := by simpa [one_pow] using ha (k := 1) le_rfl
  cases t with
  | PSL =>
    simp only [lieOrderNumerator]
    exact (V2Eq.pow_pow hx).mul (V2Eq.prod fun i hi => hs (by simp at hi; omega))
  | PSU =>
    simp only [lieOrderNumerator]
    refine (V2Eq.pow_pow hx).mul (V2Eq.prod fun i hi => ?_)
    have hi2 : 1 ≤ i := by simp at hi; omega
    by_cases he : Even i
    · simpa [he] using hs hi2
    · simpa [he] using ha hi2
  | PSp =>
    simp only [lieOrderNumerator]
    exact (V2Eq.pow_pow hx).mul (V2Eq.prod fun i hi => hs (by simp at hi; omega))
  | POmegaOdd =>
    simp only [lieOrderNumerator]
    exact (V2Eq.pow_pow hx).mul (V2Eq.prod fun i hi => hs (by simp at hi; omega))
  | POmegaPlus =>
    simp only [lieOrderNumerator]
    exact ((V2Eq.pow_pow hx).mul (hs (hn (Or.inl rfl)))).mul
      (V2Eq.prod fun i hi => hs (by simp at hi; omega))
  | POmegaMinus =>
    simp only [lieOrderNumerator]
    exact ((V2Eq.pow_pow hx).mul (ha (hn (Or.inr rfl)))).mul
      (V2Eq.prod fun i hi => hs (by simp at hi; omega))
  | G2 =>
    simp only [lieOrderNumerator]
    exact ((V2Eq.pow_pow hx).mul (hs (k := 6) (by norm_num))).mul (hs (k := 2) (by norm_num))
  | F4 =>
    simp only [lieOrderNumerator]
    exact ((((V2Eq.pow_pow hx).mul (hs (k := 12) (by norm_num))).mul
      (hs (k := 8) (by norm_num))).mul (hs (k := 6) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | E6 =>
    simp only [lieOrderNumerator]
    exact ((((((V2Eq.pow_pow hx).mul (hs (k := 12) (by norm_num))).mul
      (hs (k := 9) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 6) (by norm_num))).mul (hs (k := 5) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | E7 =>
    simp only [lieOrderNumerator]
    exact (((((((V2Eq.pow_pow hx).mul (hs (k := 18) (by norm_num))).mul
      (hs (k := 14) (by norm_num))).mul (hs (k := 12) (by norm_num))).mul
      (hs (k := 10) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 6) (by norm_num))).mul (hs (k := 2) (by norm_num))
  | E8 =>
    simp only [lieOrderNumerator]
    exact ((((((((V2Eq.pow_pow hx).mul (hs (k := 30) (by norm_num))).mul
      (hs (k := 24) (by norm_num))).mul (hs (k := 20) (by norm_num))).mul
      (hs (k := 18) (by norm_num))).mul (hs (k := 14) (by norm_num))).mul
      (hs (k := 12) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | twistedE6 =>
    simp only [lieOrderNumerator]
    exact ((((((V2Eq.pow_pow hx).mul (hs (k := 12) (by norm_num))).mul
      (ha (k := 9) (by norm_num))).mul (hs (k := 8) (by norm_num))).mul
      (hs (k := 6) (by norm_num))).mul (ha (k := 5) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | trialityD4 =>
    simp only [lieOrderNumerator]
    exact (((V2Eq.pow_pow hx).mul (V2Eq.tri hx)).mul (hs (k := 6) (by norm_num))).mul
      (hs (k := 2) (by norm_num))
  | twistedB2 =>
    simp only [lieOrderNumerator]
    exact ((V2Eq.pow_pow hx).mul (ha (k := 2) (by norm_num))).mul h1
  | twistedG2 =>
    simp only [lieOrderNumerator]
    exact ((V2Eq.pow_pow hx).mul (ha (k := 3) (by norm_num))).mul h1
  | twistedF4 =>
    simp only [lieOrderNumerator]
    exact ((((V2Eq.pow_pow hx).mul (ha (k := 6) (by norm_num))).mul
      (hs (k := 4) (by norm_num))).mul (ha (k := 3) (by norm_num))).mul h1
  | Tits =>
    simp only [lieOrderNumerator]
    exact ⟨by norm_num, by norm_num, rfl⟩

private theorem factorization_pow_sub_one_eq {q k i : ℕ} (hq : Odd q) (hk : Odd k) :
    ((q ^ k) ^ i - 1).factorization 2 = (q ^ i - 1).factorization 2 := by
  have h : (q ^ k) ^ i = (q ^ i) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h]
  exact factorization_two_pow_sub_one_of_odd (hq.pow) hk

private theorem factorization_pow_add_one_eq {q k i : ℕ} (hq : Odd q) (hk : Odd k) :
    ((q ^ k) ^ i + 1).factorization 2 = (q ^ i + 1).factorization 2 := by
  have h : (q ^ k) ^ i = (q ^ i) ^ k := by rw [← pow_mul, ← pow_mul, mul_comm]
  rw [h]
  exact factorization_two_pow_add_one_of_odd (hq.pow) hk

private theorem factorization_gcd_eq {n b d : ℕ} (hn : n ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : b.factorization 2 = d.factorization 2) :
    (Nat.gcd n b).factorization 2 = (Nat.gcd n d).factorization 2 := by
  rw [Nat.factorization_gcd hn hb, Nat.factorization_gcd hn hd]
  simp only [Finsupp.inf_apply]
  rw [h]

private theorem pow_sub_one_pos {x p : ℕ} (hx3 : 3 ≤ x) (hp : 1 ≤ p) : 0 < x ^ p - 1 := by
  have : 1 < x ^ p := Nat.one_lt_pow (by omega) (by omega)
  omega

private theorem pow_add_one_pos {x p : ℕ} : 0 < x ^ p + 1 := by positivity

private theorem V2Eq.divisor (t : CFSG.Open.StatedLieTag) (n : ℕ) {x p : ℕ}
    (hx : Odd x) (hx3 : 3 ≤ x) (hp : Odd p) :
    V2Eq (lieOrderDivisor t n (x ^ p)) (lieOrderDivisor t n x) := by
  cases t with
  | PSL =>
    simp only [lieOrderDivisor]
    rcases eq_or_ne n 0 with hn | hn
    · subst n; simp only [Nat.gcd_zero_left]
      simpa using V2Eq.pow_sub_one hx hx3 hp (k := 1) le_rfl
    · have h : (x ^ p - 1).factorization 2 = (x - 1).factorization 2 := by
        simpa [one_pow] using (V2Eq.pow_sub_one hx hx3 hp (k := 1) le_rfl).2.2
      refine ⟨?_, ?_, factorization_gcd_eq hn (pow_sub_one_pos hx3 hp.pos).ne' (by omega) h⟩
      · exact (Nat.gcd_pos_of_pos_right n (pow_sub_one_pos hx3 hp.pos)).ne'
      · exact (Nat.gcd_pos_of_pos_right n (by omega)).ne'
  | PSU =>
    simp only [lieOrderDivisor]
    rcases eq_or_ne n 0 with hn | hn
    · subst n; simp only [Nat.gcd_zero_left]
      simpa [one_pow] using V2Eq.pow_add_one hx hx3 hp (k := 1) le_rfl
    · have h : (x ^ p + 1).factorization 2 = (x + 1).factorization 2 := by
        simpa [one_pow] using (V2Eq.pow_add_one hx hx3 hp (k := 1) le_rfl).2.2
      refine ⟨?_, ?_, factorization_gcd_eq hn pow_add_one_pos.ne' (by positivity) h⟩
      · exact (Nat.gcd_pos_of_pos_right n pow_add_one_pos).ne'
      · exact (Nat.gcd_pos_of_pos_right n (by positivity)).ne'
  | PSp =>
    simp only [lieOrderDivisor]
    have h : (x ^ p - 1).factorization 2 = (x - 1).factorization 2 := by
      simpa [one_pow] using (V2Eq.pow_sub_one hx hx3 hp (k := 1) le_rfl).2.2
    refine ⟨?_, ?_, factorization_gcd_eq (by norm_num : (2:ℕ) ≠ 0)
      (pow_sub_one_pos hx3 hp.pos).ne' (by omega) h⟩
    · exact (Nat.gcd_pos_of_pos_right 2 (pow_sub_one_pos hx3 hp.pos)).ne'
    · exact (Nat.gcd_pos_of_pos_right 2 (by omega)).ne'
  | POmegaOdd =>
    simp only [lieOrderDivisor]
    exact ⟨by norm_num, by norm_num, rfl⟩
  | POmegaPlus =>
    simp only [lieOrderDivisor]
    rcases eq_or_ne n 0 with hn | hn
    · subst n; simp only [pow_zero]
      exact ⟨by norm_num, by norm_num, rfl⟩
    · refine ⟨?_, ?_, factorization_gcd_eq (by norm_num : (4:ℕ) ≠ 0)
        (pow_sub_one_pos (three_le_pow hx3 hp.pos) (by omega)).ne'
        (pow_sub_one_pos hx3 (by omega)).ne' (factorization_pow_sub_one_eq hx hp (i := n))⟩
      · exact (Nat.gcd_pos_of_pos_right 4
          (pow_sub_one_pos (three_le_pow hx3 hp.pos) (by omega))).ne'
      · exact (Nat.gcd_pos_of_pos_right 4 (pow_sub_one_pos hx3 (by omega))).ne'
  | POmegaMinus =>
    simp only [lieOrderDivisor]
    refine ⟨?_, ?_, factorization_gcd_eq (by norm_num : (4:ℕ) ≠ 0)
      pow_add_one_pos.ne' pow_add_one_pos.ne' (factorization_pow_add_one_eq hx hp (i := n))⟩
    · exact (Nat.gcd_pos_of_pos_right 4 pow_add_one_pos).ne'
    · exact (Nat.gcd_pos_of_pos_right 4 pow_add_one_pos).ne'
  | E6 =>
    simp only [lieOrderDivisor]
    have h : (x ^ p - 1).factorization 2 = (x - 1).factorization 2 := by
      simpa [one_pow] using (V2Eq.pow_sub_one hx hx3 hp (k := 1) le_rfl).2.2
    refine ⟨?_, ?_, factorization_gcd_eq (by norm_num : (3:ℕ) ≠ 0)
      (pow_sub_one_pos hx3 hp.pos).ne' (by omega) h⟩
    · exact (Nat.gcd_pos_of_pos_right 3 (pow_sub_one_pos hx3 hp.pos)).ne'
    · exact (Nat.gcd_pos_of_pos_right 3 (by omega)).ne'
  | E7 =>
    simp only [lieOrderDivisor]
    have h : (x ^ p - 1).factorization 2 = (x - 1).factorization 2 := by
      simpa [one_pow] using (V2Eq.pow_sub_one hx hx3 hp (k := 1) le_rfl).2.2
    refine ⟨?_, ?_, factorization_gcd_eq (by norm_num : (2:ℕ) ≠ 0)
      (pow_sub_one_pos hx3 hp.pos).ne' (by omega) h⟩
    · exact (Nat.gcd_pos_of_pos_right 2 (pow_sub_one_pos hx3 hp.pos)).ne'
    · exact (Nat.gcd_pos_of_pos_right 2 (by omega)).ne'
  | twistedE6 =>
    simp only [lieOrderDivisor]
    have h : (x ^ p + 1).factorization 2 = (x + 1).factorization 2 := by
      simpa [one_pow] using (V2Eq.pow_add_one hx hx3 hp (k := 1) le_rfl).2.2
    refine ⟨?_, ?_, factorization_gcd_eq (by norm_num : (3:ℕ) ≠ 0)
      pow_add_one_pos.ne' (by positivity) h⟩
    · exact (Nat.gcd_pos_of_pos_right 3 pow_add_one_pos).ne'
    · exact (Nat.gcd_pos_of_pos_right 3 (by positivity)).ne'
  | G2 | F4 | E8 | trialityD4 | twistedB2 | twistedG2 | twistedF4 | Tits =>
    simp only [lieOrderDivisor]
    exact V2Eq.one


private theorem toNat_even {q i : ℕ} (hq : 1 ≤ q) (hi : Even i) :
    (((q : ℤ) ^ i - (-1 : ℤ) ^ i)).toNat = q ^ i - 1 := by
  rw [hi.neg_one_pow]
  rw [show ((q : ℤ) ^ i - 1) = ((q ^ i - 1 : ℕ) : ℤ) by
    rw [Nat.cast_sub (Nat.one_le_pow i q hq)]
    push_cast
    ring]
  exact Int.toNat_natCast _

private theorem toNat_odd {q i : ℕ} (hi : Odd i) :
    (((q : ℤ) ^ i - (-1 : ℤ) ^ i)).toNat = q ^ i + 1 := by
  rw [hi.neg_one_pow, sub_neg_eq_add]
  rw [show ((q : ℤ) ^ i + 1) = ((q ^ i + 1 : ℕ) : ℤ) by
    push_cast
    ring]
  exact Int.toNat_natCast _

private theorem lieOrd_eq_num_div (t : CFSG.Open.StatedLieTag) (n : ℕ) (q : ℕ) (hq : Odd q)
    (hq3 : 3 ≤ q)
    (hn : (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd) → 1 ≤ n)
    (ht : t ≠ .Tits ∧ t ≠ .twistedF4) :
    CFSG.EvenSmallLie.CatalogOrders.lieOrd t n q =
      lieOrderNumerator t n q / lieOrderDivisor t n q := by
  cases t with
  | PSL =>
    have hn' := hn (Or.inl rfl)
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordA]
    rw [Nat.sub_add_cancel hn', Nat.mul_comm (n - 1) n]
  | PSU =>
    have hn' := hn (Or.inr (Or.inl rfl))
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordTwistedA]
    rw [Nat.sub_add_cancel hn', Nat.mul_comm (n - 1) n]
    have hprod : (∏ i ∈ Finset.Icc 2 n, ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat) =
        (∏ i ∈ Finset.Icc 2 n, if Even i then q ^ i - 1 else q ^ i + 1) := by
      apply Finset.prod_congr rfl
      intro i hi
      by_cases he : Even i
      · rw [if_pos he, toNat_even (by omega) he]
      · rw [if_neg he]
        rcases Nat.even_or_odd i with he' | ho
        · exact absurd he' he
        · exact toNat_odd ho
    rw [hprod]
  | PSp =>
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordBC]
    rw [pow_two]
  | POmegaOdd =>
    have h2 : 2 ∣ q - 1 := by
      rcases hq with ⟨m, hm⟩
      exact ⟨m, by omega⟩
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordBC]
    rw [pow_two, Nat.gcd_eq_left h2]
  | POmegaPlus => rfl
  | POmegaMinus => rfl
  | G2 =>
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordG2]
    rw [Nat.div_one]
  | F4 =>
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordF4]
    rw [Nat.div_one]
  | E6 => rfl
  | E7 => rfl
  | E8 =>
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordE8]
    rw [Nat.div_one]
  | twistedE6 => rfl
  | trialityD4 =>
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordTrialityD4]
    rw [Nat.div_one]
  | twistedB2 =>
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordSuzuki]
    rw [Nat.div_one]
  | twistedG2 =>
    simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd, lieOrderNumerator, lieOrderDivisor,
      CFSG.Open.ordRee]
    rw [Nat.div_one]
  | twistedF4 => exfalso; exact ht.2 rfl
  | Tits => exfalso; exact ht.1 rfl

private theorem lieOrderDivisor_dvd_numerator (t : CFSG.Open.StatedLieTag) (n : ℕ) (q : ℕ)
    (hq : Odd q) (hq3 : 3 ≤ q)
    (hn : (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd) → 1 ≤ n) :
    lieOrderDivisor t n q ∣ lieOrderNumerator t n q := by
  have h2 : 2 ∣ q - 1 := by
    rcases hq with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  cases t with
  | PSL =>
    have hn' := hn (Or.inl rfl)
    rcases Nat.eq_or_lt_of_le hn' with hn1 | hn2
    · subst n
      simp only [lieOrderNumerator, lieOrderDivisor]
      rw [Nat.gcd_one_left]
      exact one_dvd _
    · have hn2' : 2 ≤ n := by omega
      simp only [lieOrderNumerator, lieOrderDivisor]
      refine Dvd.dvd.mul_left ?_ _
      refine (Nat.gcd_dvd_right _ _).trans
        ((CFSG.EvenSmallLie.CatalogOrders.sub_one_dvd_sq_sub_one q).trans ?_)
      exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, hn2'⟩)
  | PSU =>
    have hn' := hn (Or.inr (Or.inl rfl))
    rcases Nat.eq_or_lt_of_le hn' with hn1 | hn2
    · subst n
      simp only [lieOrderNumerator, lieOrderDivisor]
      rw [Nat.gcd_one_left]
      exact one_dvd _
    · have hn2' : 2 ≤ n := by omega
      simp only [lieOrderNumerator, lieOrderDivisor]
      refine Dvd.dvd.mul_left ?_ _
      refine (Nat.gcd_dvd_right _ _).trans
        ((CFSG.EvenSmallLie.CatalogOrders.add_one_dvd_sq_sub_one q).trans ?_)
      exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, hn2'⟩)
  | PSp =>
    have hn' := hn (Or.inr (Or.inr (Or.inl rfl)))
    simp only [lieOrderNumerator, lieOrderDivisor]
    refine Dvd.dvd.mul_left ?_ _
    refine (Nat.gcd_dvd_right _ _).trans
      ((CFSG.EvenSmallLie.CatalogOrders.sub_one_dvd_sq_sub_one q).trans ?_)
    exact Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, hn'⟩)
  | POmegaOdd =>
    have hn' := hn (Or.inr (Or.inr (Or.inr rfl)))
    simp only [lieOrderNumerator, lieOrderDivisor]
    refine Dvd.dvd.mul_left ?_ _
    have hfac : 2 ∣ q ^ (2 * 1) - 1 := by
      simpa using h2.trans (CFSG.EvenSmallLie.CatalogOrders.sub_one_dvd_sq_sub_one q)
    exact hfac.trans (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.mpr ⟨le_rfl, hn'⟩))
  | POmegaPlus =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _) _
  | POmegaMinus =>
    simp only [lieOrderNumerator, lieOrderDivisor]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left (Nat.gcd_dvd_right _ _) _) _
  | E6 =>
    have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .E6 n q := by
      simp only [lieOrderNumerator]
      exact dvd_mul_of_dvd_right dvd_rfl _
    exact (Nat.gcd_dvd_right _ _).trans
      ((CFSG.EvenSmallLie.CatalogOrders.sub_one_dvd_sq_sub_one q).trans hfac)
  | E7 =>
    have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .E7 n q := by
      simp only [lieOrderNumerator]
      exact dvd_mul_of_dvd_right dvd_rfl _
    exact (Nat.gcd_dvd_right _ _).trans
      ((CFSG.EvenSmallLie.CatalogOrders.sub_one_dvd_sq_sub_one q).trans hfac)
  | twistedE6 =>
    have hfac : q ^ 2 - 1 ∣ lieOrderNumerator .twistedE6 n q := by
      simp only [lieOrderNumerator]
      exact dvd_mul_of_dvd_right dvd_rfl _
    exact (Nat.gcd_dvd_right _ _).trans
      ((CFSG.EvenSmallLie.CatalogOrders.add_one_dvd_sq_sub_one q).trans hfac)
  | G2 => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _
  | F4 => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _
  | E8 => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _
  | trialityD4 => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _
  | twistedB2 => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _
  | twistedG2 => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _
  | twistedF4 => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _
  | Tits => simp only [lieOrderNumerator, lieOrderDivisor]; exact one_dvd _

private theorem factorization_div_eq_of_factorization_eq {a₁ a₂ d₁ d₂ : ℕ}
    (hd₁ : d₁ ∣ a₁) (hd₂ : d₂ ∣ a₂)
    (ha : a₁.factorization 2 = a₂.factorization 2)
    (hd : d₁.factorization 2 = d₂.factorization 2) :
    (a₁ / d₁).factorization 2 = (a₂ / d₂).factorization 2 := by
  rw [Nat.factorization_div hd₁, Nat.factorization_div hd₂]
  rw [Finsupp.tsub_apply, Finsupp.tsub_apply]
  rw [ha, hd]

private theorem factorization_div_of_V2Eq {Nq Nqk Dq Dqk : ℕ}
    (hdqk : Dqk ∣ Nqk) (hdq : Dq ∣ Nq) (hnum : V2Eq Nqk Nq) (hdiv : V2Eq Dqk Dq) :
    (Nqk / Dqk).factorization 2 = (Nq / Dq).factorization 2 :=
  factorization_div_eq_of_factorization_eq hdqk hdq hnum.2.2 hdiv.2.2


private theorem ordBC_zero_of_odd {q : ℕ} (hq : Odd q) : CFSG.Open.ordBC 0 q = 0 := by
  have h2 : 2 ∣ q - 1 := by
    rcases hq with ⟨m, hm⟩
    exact ⟨m, by omega⟩
  simp [CFSG.Open.ordBC, Nat.gcd_eq_left h2]

private theorem factorization_lieOrd_pow_of_eq (t : CFSG.Open.StatedLieTag) (n q k : ℕ)
    (hq : Odd q) (hk : Odd k) (hq3 : 3 ≤ q)
    (hNq : CFSG.EvenSmallLie.CatalogOrders.lieOrd t n q =
      lieOrderNumerator t n q / lieOrderDivisor t n q)
    (hNqk : CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (q ^ k) =
      lieOrderNumerator t n (q ^ k) / lieOrderDivisor t n (q ^ k))
    (hnNum : (t = .POmegaPlus ∨ t = .POmegaMinus) → 1 ≤ n)
    (hnDiv : (t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd) → 1 ≤ n) :
    (CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (q ^ k)).factorization 2 =
      (CFSG.EvenSmallLie.CatalogOrders.lieOrd t n q).factorization 2 := by
  rw [hNqk, hNq]
  exact factorization_div_of_V2Eq
    (lieOrderDivisor_dvd_numerator t n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
      (fun h => hnDiv h))
    (lieOrderDivisor_dvd_numerator t n q hq hq3 hnDiv)
    (V2Eq.numerator t n hq hq3 hk hnNum)
    (V2Eq.divisor t n hq hq3 hk)


theorem factorization_two_lieOrd_pow (t : CFSG.Open.StatedLieTag) (n : ℕ) {q k : ℕ}
    (hq : Odd q) (hk : Odd k) :
    (CFSG.EvenSmallLie.CatalogOrders.lieOrd t n (q ^ k)).factorization 2 =
      (CFSG.EvenSmallLie.CatalogOrders.lieOrd t n q).factorization 2 := by
  rcases eq_or_ne q 1 with hq1 | hqne
  · subst q; simp
  have hq3 : 3 ≤ q := by
    rcases hq with ⟨m, hm⟩
    omega
  cases t with
  | PSL =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst n
      simp [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordA]
    · exact factorization_lieOrd_pow_of_eq .PSL n q k hq hk hq3
        (lieOrd_eq_num_div .PSL n q hq hq3 (fun _ => by omega) (by simp))
        (lieOrd_eq_num_div .PSL n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
          (fun _ => by omega) (by simp))
        (by simp) (fun _ => by omega)
  | PSU =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst n
      simp [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordTwistedA]
    · exact factorization_lieOrd_pow_of_eq .PSU n q k hq hk hq3
        (lieOrd_eq_num_div .PSU n q hq hq3 (fun _ => by omega) (by simp))
        (lieOrd_eq_num_div .PSU n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
          (fun _ => by omega) (by simp))
        (by simp) (fun _ => by omega)
  | PSp =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst n
      simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd]
      rw [ordBC_zero_of_odd hq, ordBC_zero_of_odd hq.pow]
    · exact factorization_lieOrd_pow_of_eq .PSp n q k hq hk hq3
        (lieOrd_eq_num_div .PSp n q hq hq3 (fun _ => by omega) (by simp))
        (lieOrd_eq_num_div .PSp n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
          (fun _ => by omega) (by simp))
        (by simp) (fun _ => by omega)
  | POmegaOdd =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst n
      simp only [CFSG.EvenSmallLie.CatalogOrders.lieOrd]
      rw [ordBC_zero_of_odd hq, ordBC_zero_of_odd hq.pow]
    · exact factorization_lieOrd_pow_of_eq .POmegaOdd n q k hq hk hq3
        (lieOrd_eq_num_div .POmegaOdd n q hq hq3 (fun _ => by omega) (by simp))
        (lieOrd_eq_num_div .POmegaOdd n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
          (fun _ => by omega) (by simp))
        (by simp) (fun _ => by omega)
  | POmegaPlus =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst n
      simp [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordD]
    · exact factorization_lieOrd_pow_of_eq .POmegaPlus n q k hq hk hq3
        (lieOrd_eq_num_div .POmegaPlus n q hq hq3 (by simp) (by simp))
        (lieOrd_eq_num_div .POmegaPlus n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
          (by simp) (by simp))
        (fun _ => by omega) (by simp)
  | POmegaMinus =>
    rcases Nat.eq_zero_or_pos n with hn0 | hn
    · subst n
      simp [CFSG.EvenSmallLie.CatalogOrders.lieOrd, CFSG.Open.ordTwistedD]
    · exact factorization_lieOrd_pow_of_eq .POmegaMinus n q k hq hk hq3
        (lieOrd_eq_num_div .POmegaMinus n q hq hq3 (by simp) (by simp))
        (lieOrd_eq_num_div .POmegaMinus n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
          (by simp) (by simp))
        (fun _ => by omega) (by simp)
  | G2 =>
    exact factorization_lieOrd_pow_of_eq .G2 n q k hq hk hq3
      (lieOrd_eq_num_div .G2 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .G2 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | F4 =>
    exact factorization_lieOrd_pow_of_eq .F4 n q k hq hk hq3
      (lieOrd_eq_num_div .F4 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .F4 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | E6 =>
    exact factorization_lieOrd_pow_of_eq .E6 n q k hq hk hq3
      (lieOrd_eq_num_div .E6 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .E6 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | E7 =>
    exact factorization_lieOrd_pow_of_eq .E7 n q k hq hk hq3
      (lieOrd_eq_num_div .E7 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .E7 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | E8 =>
    exact factorization_lieOrd_pow_of_eq .E8 n q k hq hk hq3
      (lieOrd_eq_num_div .E8 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .E8 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | twistedE6 =>
    exact factorization_lieOrd_pow_of_eq .twistedE6 n q k hq hk hq3
      (lieOrd_eq_num_div .twistedE6 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .twistedE6 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | trialityD4 =>
    exact factorization_lieOrd_pow_of_eq .trialityD4 n q k hq hk hq3
      (lieOrd_eq_num_div .trialityD4 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .trialityD4 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | twistedB2 =>
    exact factorization_lieOrd_pow_of_eq .twistedB2 n q k hq hk hq3
      (lieOrd_eq_num_div .twistedB2 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .twistedB2 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | twistedG2 =>
    exact factorization_lieOrd_pow_of_eq .twistedG2 n q k hq hk hq3
      (lieOrd_eq_num_div .twistedG2 n q hq hq3 (by simp) (by simp))
      (lieOrd_eq_num_div .twistedG2 n (q ^ k) hq.pow (three_le_pow hq3 hk.pos)
        (by simp) (by simp))
      (by simp) (by simp)
  | twistedF4 => rfl
  | Tits => rfl


theorem exists_isSylowOf_le_of_factorization_two_eq {X : Type} [Group X] [Finite X]
    {H : Subgroup X} (hH : (Nat.card H).factorization 2 = (Nat.card X).factorization 2) :
    ∃ S : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S ⊤ ∧ S ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := H)
  refine ⟨(P : Subgroup H).map H.subtype, ?_, Subgroup.map_subtype_le _⟩
  apply CFSG.ABGLocalTools.isSylowOf_of_card (K := ⊤)
  · exact le_top
  · rw [Subgroup.card_map_of_injective H.subtype_injective, Sylow.card_eq_multiplicity,
      Subgroup.card_top, hH]

theorem exists_isSylowOf_fixed_of_le {X : Type} [Group X] [Finite X] (θ : MulAut X)
    {Y : Subgroup X} (hY : Y ≤ CFSG.Open.signalizerFixedSubgroup θ)
    (hcard : (Nat.card Y).factorization 2 = (Nat.card X).factorization 2) :
    ∃ S₀ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S₀ ⊤ ∧ ∀ x ∈ S₀, θ x = x := by
  obtain ⟨S, hS, hSY⟩ := exists_isSylowOf_le_of_factorization_two_eq hcard
  refine ⟨S, hS, ?_⟩
  intro x hx
  exact hY (hSY hx)

theorem exists_isSylowOf_fixed_of_injective {X H : Type} [Group X] [Finite X] [Group H]
    (ι : H →* X) (hι : Function.Injective ι) (θ : MulAut X) (hfix : ∀ y, θ (ι y) = ι y)
    (hcard : (Nat.card H).factorization 2 = (Nat.card X).factorization 2) :
    ∃ S₀ : Subgroup X, CFSG.ABGLocalTools.IsSylowOf 2 S₀ ⊤ ∧ ∀ x ∈ S₀, θ x = x := by
  have hcard' : (Nat.card (ι.range : Subgroup X)).factorization 2 =
      (Nat.card X).factorization 2 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hι).toEquiv]
    exact hcard
  have hY : (ι.range : Subgroup X) ≤ CFSG.Open.signalizerFixedSubgroup θ := by
    intro x hx
    rw [MonoidHom.mem_range] at hx
    obtain ⟨y, rfl⟩ := hx
    exact hfix y
  exact exists_isSylowOf_fixed_of_le θ hY hcard' 

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCTenSeven
