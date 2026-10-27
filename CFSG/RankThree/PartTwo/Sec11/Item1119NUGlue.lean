module

public import CFSG.RankThree.PartTwo.Sec11.Item1119SymToolNumbers
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Multiplicity

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119NU

theorem three_pow_dvd_of_pow_mem {M : Type*} [Group M] {ω : M} {S : Subgroup M} {e n : ℕ}
    (he : 1 ≤ e) (hω : ω ^ 3 ^ e = 1) (hnot : ω ^ 3 ^ (e - 1) ∉ S) (hmem : ω ^ n ∈ S) :
    3 ^ e ∣ n := by
  by_contra hndvd
  obtain ⟨v, hv, hgv⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (Nat.gcd_dvd_right n (3 ^ e))
  have hve : v ≤ e - 1 := by
    rcases Nat.lt_or_ge v e with h | h
    · omega
    · exfalso
      have hve' : v = e := by omega
      apply hndvd
      have h1 : Nat.gcd n (3 ^ e) ∣ n := Nat.gcd_dvd_left n (3 ^ e)
      rw [hgv, hve'] at h1
      exact h1
  obtain ⟨k, hk⟩ : Nat.gcd n (3 ^ e) ∣ 3 ^ (e - 1) := by
    rw [hgv]
    exact pow_dvd_pow 3 hve
  have hgS : ω ^ Nat.gcd n (3 ^ e) ∈ S := by
    have hbez := Nat.gcd_eq_gcd_ab n (3 ^ e)
    have hzp : ω ^ ((Nat.gcd n (3 ^ e) : ℕ) : ℤ) = (ω ^ n) ^ Nat.gcdA n (3 ^ e) := by
      rw [hbez, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hω, one_zpow, mul_one]
    have hzn : ω ^ ((Nat.gcd n (3 ^ e) : ℕ) : ℤ) = ω ^ Nat.gcd n (3 ^ e) := zpow_natCast ω _
    rw [← hzn, hzp]
    exact Subgroup.zpow_mem S hmem _
  apply hnot
  rw [hk, pow_mul]
  exact S.pow_mem hgS k

theorem pow_three_pow_pred_mem {G : Type} [Group G] {r c a : G} {e : ℕ} (he : 2 ≤ e)
    (hr : orderOf r = 3 ^ e) (hrc : r * c = c * r) (ha3 : a ^ 3 = 1) (hc3 : c ^ 3 = 1)
    (ha : a ∈ Subgroup.closure ({r, c} : Set G)) (hac : a ∉ Subgroup.zpowers c) :
    r ^ 3 ^ (e - 1) ∈ Subgroup.closure ({a, c} : Set G) ∧
      r ^ 3 ^ (e - 1) ∉ Subgroup.zpowers c := by
  obtain ⟨f, rfl⟩ : ∃ f, e = f + 2 := ⟨e - 2, by omega⟩
  rw [show f + 2 - 1 = f + 1 by omega]
  have hcomm : Commute r c := hrc
  obtain ⟨u, hu⟩ : ∃ u : G, u = r ^ 3 ^ f := ⟨_, rfl⟩
  have hu3 : u ^ 3 = r ^ 3 ^ (f + 1) := by
    rw [hu, ← pow_mul, ← pow_succ]
  have hu_order : orderOf u = 9 := by
    have hdvd : 3 ^ f ∣ orderOf r := by
      rw [hr]
      exact pow_dvd_pow 3 (by omega)
    have h9 : 3 ^ (f + 2) = 3 ^ f * 9 := by
      rw [pow_add]
      norm_num
    rw [hu, orderOf_pow_of_dvd (pow_ne_zero f (by norm_num : (3 : ℕ) ≠ 0)) hdvd, hr, h9,
      Nat.mul_div_cancel_left 9 (pow_pos (by norm_num : (0 : ℕ) < 3) f)]
  have hcu : u * c = c * u := by
    rw [hu]
    exact (Commute.pow_left hcomm (3 ^ f)).eq
  obtain ⟨j, n, hjn⟩ := Item1119Sym.exists_zpow_form hrc ha
  have hrj3 : (r ^ j) ^ 3 = 1 := by
    have h := ha3
    rw [hjn, (hcomm.zpow_zpow j n).mul_pow 3, Item1119Sym.aux_Numbers_zpow_pow_three hc3 n,
      mul_one] at h
    exact h
  have hrj3' : r ^ (j * 3) = 1 := (Item1119Sym.aux_Numbers_zpow_natpow3 r j).symm.trans hrj3
  have hdvd : ((orderOf r : ℕ) : ℤ) ∣ j * 3 := orderOf_dvd_iff_zpow_eq_one.mpr hrj3'
  rw [hr] at hdvd
  have hdvd2 : ((3 ^ (f + 1) : ℕ) : ℤ) * 3 ∣ j * 3 := by
    have he' : ((3 ^ (f + 2) : ℕ) : ℤ) = ((3 ^ (f + 1) : ℕ) : ℤ) * 3 := by
      push_cast
      ring
    rw [he'] at hdvd
    exact hdvd
  obtain ⟨m, hm⟩ := (mul_dvd_mul_iff_right (by norm_num : (3 : ℤ) ≠ 0)).mp hdvd2
  have hA : a = (u ^ 3) ^ m * c ^ n := by
    rw [hjn, hm, zpow_mul, zpow_natCast, hu3]
  have hu_mem : u ∈ Subgroup.closure ({u, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert u {c})
  have hc_mem : c ∈ Subgroup.closure ({u, c} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem u (Set.mem_singleton c))
  have ha' : a ∈ Subgroup.closure ({u, c} : Set G) := by
    rw [hA]
    exact mul_mem (Subgroup.zpow_mem _ (Subgroup.pow_mem _ hu_mem 3) m)
      (Subgroup.zpow_mem _ hc_mem n)
  have key := Item1119Sym.cube_facts_of_orderOf_nine hcu hc3 ha3 hu_order ha' hac
  rw [hu3] at key
  exact key

theorem three_pow_succ_dvd_sq_sub_one {p n e : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hn0 : n ≠ 0)
    (hn : 3 ^ e ∣ n) : 3 ^ (e + 1) ∣ (p ^ n) ^ 2 - 1 := by
  have hp3' : ¬ 3 ∣ p := fun h =>
    hp3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h).symm
  have hsq : p ^ 2 % 3 = 1 := by
    have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rw [Nat.pow_mod]
    rcases hmod with h | h <;> simp [h]
  have hdvd : 3 ∣ p ^ 2 - 1 := by omega
  have hndvd2 : ¬ 3 ∣ p ^ 2 := fun h => hp3' (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h)
  have hodd3 : Odd (3 : ℕ) := ⟨1, by norm_num⟩
  have hyx : 1 < p ^ 2 := by
    have h2 := hp.two_le
    nlinarith
  have hL : padicValNat 3 ((p ^ 2) ^ n - 1 ^ n) = padicValNat 3 (p ^ 2 - 1) + padicValNat 3 n :=
    padicValNat.pow_sub_pow hodd3 hyx hdvd hndvd2 hn0
  rw [one_pow] at hL
  have he_le : e ≤ padicValNat 3 n := (padicValNat_dvd_iff_le hn0).mp hn
  have hne1 : p ^ 2 - 1 ≠ 0 := by omega
  have h31 : 3 ^ 1 ∣ p ^ 2 - 1 := by
    rw [pow_one]
    exact hdvd
  have h1_le : 1 ≤ padicValNat 3 (p ^ 2 - 1) := (padicValNat_dvd_iff_le hne1).mp h31
  have hsum : e + 1 ≤ padicValNat 3 ((p ^ 2) ^ n - 1) := by
    rw [hL]
    omega
  have hgt : 1 < (p ^ 2) ^ n := one_lt_pow₀ hyx hn0
  have hne : (p ^ 2) ^ n - 1 ≠ 0 := by omega
  have hpow : (p ^ n) ^ 2 = (p ^ 2) ^ n := by
    rw [← pow_mul, ← pow_mul, mul_comm]
  rw [hpow]
  exact (padicValNat_dvd_iff_le hne).mpr hsum

end CFSG.RankThree.PartTwo.Sec11.Item1119NU

end
