module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection13.PFsection13_13

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi, Section 13: PFsection13_14
-/

noncomputable section

open scoped BigOperators Pointwise

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section13

universe v
universe u

/-! ## (13.14) -/


/-! ## Arithmetic helpers for (13.14) -/

public theorem section13_odd_geom_quotient
    {p q : ℕ} (hp : Nat.Prime p) (hpOdd : Odd p) (hqOdd : Odd q) :
    Odd ((p ^ q - 1) / (p - 1)) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  have hodd_sum : ∀ m : ℕ, Odd (∑ i ∈ Finset.range m, p ^ i) ↔ Odd m := by
    intro m
    induction m with
    | zero =>
        simp
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have hpown : Odd (p ^ m) := hpOdd.pow
        have hpown_not_even : ¬ Even (p ^ m) := Nat.not_even_iff_odd.mpr hpown
        rw [Nat.odd_add]
        simp [hpown_not_even, ih, Nat.odd_add_one]
  exact (hodd_sum q).mpr hqOdd

public theorem section13_geom_quotient_dvd_of_mod_eq_one
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpmod : p % q = 1) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
  have hpModEq : p ≡ 1 [MOD q] := by
    rw [Nat.ModEq]
    simpa [h1mod] using hpmod
  have hsum_mod : ∀ m : ℕ, (∑ i ∈ Finset.range m, p ^ i) ≡ m [MOD q] := by
    intro m
    induction m with
    | zero =>
        simp [Nat.ModEq]
    | succ m ih =>
        rw [Finset.sum_range_succ]
        have hpow : p ^ m ≡ 1 ^ m [MOD q] := Nat.ModEq.pow m hpModEq
        have hpow1 : p ^ m ≡ 1 [MOD q] := by
          simpa using hpow
        simpa [Nat.succ_eq_add_one] using ih.add hpow1
  exact Nat.modEq_zero_iff_dvd.mp ((hsum_mod q).trans Nat.modulus_modEq_zero)

public theorem section13_geom_sum_modEq_card_of_modEq_one
    {p q r : ℕ} (hpmod : p ≡ 1 [MOD r]) :
    (∑ i ∈ Finset.range q, p ^ i) ≡ q [MOD r] := by
  induction q with
  | zero =>
      simp [Nat.ModEq]
  | succ q ih =>
      rw [Finset.sum_range_succ]
      have hpow : p ^ q ≡ 1 ^ q [MOD r] := Nat.ModEq.pow q hpmod
      have hpow1 : p ^ q ≡ 1 [MOD r] := by
        simpa using hpow
      simpa [Nat.succ_eq_add_one] using ih.add hpow1

public theorem section13_prime_not_dvd_p_sub_one_of_dvd_geom_quotient
    {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod_ne : p % q ≠ 1) (hr : Nat.Prime r)
    (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    ¬ r ∣ p - 1 := by
  intro hrdvd_sub
  have hpmod_r : p ≡ 1 [MOD r] := by
    have h1p : 1 ≡ p [MOD r] := (Nat.modEq_iff_dvd' hp.one_le).mpr hrdvd_sub
    exact h1p.symm
  have hsum_mod : (∑ i ∈ Finset.range q, p ^ i) ≡ q [MOD r] :=
    section13_geom_sum_modEq_card_of_modEq_one hpmod_r
  have hsum_dvd : r ∣ ∑ i ∈ Finset.range q, p ^ i := by
    simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
  have hsum_zero : (∑ i ∈ Finset.range q, p ^ i) ≡ 0 [MOD r] :=
    Nat.modEq_zero_iff_dvd.mpr hsum_dvd
  have hq_zero : q ≡ 0 [MOD r] := hsum_mod.symm.trans hsum_zero
  have hr_dvd_q : r ∣ q := Nat.modEq_zero_iff_dvd.mp hq_zero
  have hr_eq_q : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).mp hr_dvd_q
  have hq_dvd_sub : q ∣ p - 1 := by
    simpa [hr_eq_q] using hrdvd_sub
  have h1p_q : 1 ≡ p [MOD q] := (Nat.modEq_iff_dvd' hp.one_le).mpr hq_dvd_sub
  have hpmod : p % q = 1 := by
    have hpmodq : p ≡ 1 [MOD q] := h1p_q.symm
    rw [Nat.ModEq] at hpmodq
    have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
    simpa [h1mod] using hpmodq
  exact hpmod_ne hpmod

public theorem section13_geom_quotient_coprime_p_sub_one_of_mod_ne_one
    {p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod_ne : p % q ≠ 1) :
    Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) := by
  refine Nat.coprime_of_dvd ?_
  intro r hr hrdvd
  exact section13_prime_not_dvd_p_sub_one_of_dvd_geom_quotient hp hq hpmod_ne hr hrdvd

public theorem section13_prime_dvd_geom_quotient_mod_eq_one
    {p q r : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod_ne : p % q ≠ 1) (hr : Nat.Prime r)
    (hrdvd : r ∣ (p ^ q - 1) / (p - 1)) :
    r % q = 1 := by
  haveI : Fact (Nat.Prime q) := ⟨hq⟩
  haveI : Fact (Nat.Prime r) := ⟨hr⟩
  have hroot : (Polynomial.cyclotomic q (ZMod r)).IsRoot (p : ZMod r) := by
    rw [Polynomial.cyclotomic_prime (ZMod r) q]
    rw [Polynomial.IsRoot]
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_pow, Polynomial.eval_X]
    have hsum_dvd : r ∣ ∑ i ∈ Finset.range q, p ^ i := by
      simpa [Nat.geomSum_eq hp.two_le q] using hrdvd
    simpa using ((ZMod.natCast_eq_zero_iff (∑ i ∈ Finset.range q, p ^ i) r).mpr
      hsum_dvd)
  let hpcoprime : p.Coprime r := Polynomial.coprime_of_root_cyclotomic hq.pos hroot
  let zunit : (ZMod r)ˣ := ZMod.unitOfCoprime p hpcoprime
  have horder_dvd_q : orderOf zunit ∣ q := by
    simpa [hpcoprime, zunit] using Polynomial.orderOf_root_cyclotomic_dvd hq.pos hroot
  have hnot_dvd_sub : ¬ r ∣ p - 1 :=
    section13_prime_not_dvd_p_sub_one_of_dvd_geom_quotient hp hq hpmod_ne hr hrdvd
  have hzunit_ne_one : zunit ≠ 1 := by
    intro hzunit
    have hpcast_one : (p : ZMod r) = 1 := by
      have hcoerce := congrArg (fun z : (ZMod r)ˣ => (z : ZMod r)) hzunit
      simpa [zunit, hpcoprime] using hcoerce
    have hcast : (p : ZMod r) = (1 : ℕ) := by
      simpa using hpcast_one
    have hpmod_r : p ≡ 1 [MOD r] := (ZMod.natCast_eq_natCast_iff p 1 r).mp hcast
    have hrdvd_sub : r ∣ p - 1 :=
      (Nat.modEq_iff_dvd' hp.one_le).mp hpmod_r.symm
    exact hnot_dvd_sub hrdvd_sub
  have horder_ne_one : orderOf zunit ≠ 1 := by
    intro horder
    exact hzunit_ne_one (orderOf_eq_one_iff.mp horder)
  have horder_eq_q : orderOf zunit = q := by
    rcases (Nat.dvd_prime hq).mp horder_dvd_q with h | h
    · exact False.elim (horder_ne_one h)
    · exact h
  have hq_dvd_sub : q ∣ r - 1 := by
    simpa [horder_eq_q] using (ZMod.orderOf_units_dvd_card_sub_one zunit)
  have h1r_q : 1 ≡ r [MOD q] := (Nat.modEq_iff_dvd' hr.one_le).mpr hq_dvd_sub
  have hrmod : r % q = 1 := by
    have hrmodq : r ≡ 1 [MOD q] := h1r_q.symm
    rw [Nat.ModEq] at hrmodq
    have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
    simpa [h1mod] using hrmodq
  exact hrmod

public theorem section13_divisor_geom_quotient_mod_eq_one
    {p q x : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpmod_ne : p % q ≠ 1) (hxpos : 0 < x)
    (hxdvd : x ∣ (p ^ q - 1) / (p - 1)) :
    x % q = 1 := by
  induction x using Nat.strong_induction_on with
  | h x ih =>
      by_cases hxone : x = 1
      · subst x
        exact Nat.mod_eq_of_lt hq.one_lt
      · obtain ⟨r, hr, hrdvdx⟩ := Nat.exists_prime_and_dvd hxone
        have hrmod : r % q = 1 :=
          section13_prime_dvd_geom_quotient_mod_eq_one hp hq hpmod_ne hr (hrdvdx.trans hxdvd)
        let y := x / r
        have hypos : 0 < y := by
          have hrle : r ≤ x := Nat.le_of_dvd hxpos hrdvdx
          exact Nat.div_pos hrle hr.pos
        have hylt : y < x :=
          Nat.div_lt_self hxpos hr.one_lt
        have hydvd : y ∣ (p ^ q - 1) / (p - 1) :=
          (Nat.div_dvd_of_dvd hrdvdx).trans hxdvd
        have hymod : y % q = 1 := ih y hylt hypos hydvd
        have hrModEq : r ≡ 1 [MOD q] := by
          rw [Nat.ModEq]
          have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
          simpa [h1mod] using hrmod
        have hyModEq : y ≡ 1 [MOD q] := by
          rw [Nat.ModEq]
          have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
          simpa [h1mod] using hymod
        have hxModEq : x ≡ 1 [MOD q] := by
          have hmul : r * y ≡ 1 * 1 [MOD q] := hrModEq.mul hyModEq
          simpa [y, Nat.mul_div_cancel' hrdvdx] using hmul
        rw [Nat.ModEq] at hxModEq
        have h1mod : 1 % q = 1 := Nat.mod_eq_of_lt hq.one_lt
        simpa [h1mod] using hxModEq

/-! ## Numeric helpers for (13.11) -/

public theorem theorem_13_14
    (p q x : ℕ)
    : Nat.Prime p → Nat.Prime q → Odd p → Odd q →
      Odd ((p ^ q - 1) / (p - 1)) ∧
        (p % q = 1 → q ∣ (p ^ q - 1) / (p - 1)) ∧
        (p % q ≠ 1 →
          Nat.Coprime ((p ^ q - 1) / (p - 1)) (p - 1) ∧
            (0 < x → x ∣ (p ^ q - 1) / (p - 1) → x % q = 1)) := by
  intro hp hq hpOdd hqOdd
  refine ⟨section13_odd_geom_quotient hp hpOdd hqOdd, ?_, ?_⟩
  · intro hpmod
    exact section13_geom_quotient_dvd_of_mod_eq_one hp hq hpmod
  · intro hpmod_ne
    exact ⟨section13_geom_quotient_coprime_p_sub_one_of_mod_ne_one hp hq hpmod_ne,
      fun hxpos hxdvd =>
        section13_divisor_geom_quotient_mod_eq_one hp hq hpmod_ne hxpos hxdvd⟩
end CFSG.Section13
