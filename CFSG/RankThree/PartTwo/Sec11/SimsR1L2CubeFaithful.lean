module

public import CFSG.RankThree.PartTwo.Sec11.SimsR1Defs
import CFSG.RankThree.PartTwo.Sec11.SimsR1L2CubeFaithfulB
import CFSG.RankThree.PartTwo.Sec11.SimsR1L2CubeFaithfulC
import CFSG.LinearAlgebra.SL2MinimalFaithfulZsigmondy

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1

open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.RankThree.PartTwo.KFacts.KS116Proof (toProjSL uu)
open scoped MatrixGroups

namespace L2CubeFaithful

theorem dvd_of_ppd_dvd_pow_sub_one {p k j ℓ : ℕ} (hk : 0 < k) (hℓ : ℓ ∣ p ^ k - 1)
    (hprim : ∀ i : ℕ, 0 < i → i < k → ¬ ℓ ∣ p ^ i - 1) (hj : ℓ ∣ p ^ j - 1) : k ∣ j := by
  have hg : ℓ ∣ p ^ (Nat.gcd k j) - 1 := by
    rw [← Nat.pow_sub_one_gcd_pow_sub_one]
    exact Nat.dvd_gcd hℓ hj
  by_contra hkj
  have hgk : Nat.gcd k j < k :=
    lt_of_le_of_ne (Nat.gcd_le_left _ hk) (fun h => hkj (h ▸ Nat.gcd_dvd_right k j))
  exact hprim _ (Nat.gcd_pos_of_pos_left _ hk) hgk hg

theorem exists_ppd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 3 ≤ k) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ p ∧ ∀ j : ℕ, ℓ ∣ p ^ j - 1 ↔ k ∣ j := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨ℓ, hℓ, hℓd, hprim⟩ :=
    CFSG.SL2MinimalFaithful.exists_primitive_prime_dvd_pow_sub_one (a := p) hp3 (n := k) hk
  refine ⟨ℓ, hℓ, ?_, ?_, fun j => ⟨dvd_of_ppd_dvd_pow_sub_one (by omega) hℓd hprim, fun hkj => ?_⟩⟩
  · rintro rfl
    exact hprim 1 one_pos (by omega) (by simpa using (hp.even_sub_one hp2).two_dvd)
  · rintro rfl
    have h1 : ℓ ∣ ℓ ^ k := dvd_pow_self ℓ (by omega)
    have h2 := Nat.dvd_sub h1 hℓd
    rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
    exact hℓ.one_lt.ne' (Nat.dvd_one.mp h2)
  · obtain ⟨c, rfl⟩ := hkj
    rw [pow_mul]
    exact hℓd.trans (by simpa using Nat.sub_dvd_pow_sub_pow (p ^ k) 1 c)

theorem exists_ppd_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ p ∧ ℓ ∣ p ^ 3 + 1 ∧ ∀ j : ℕ, ℓ ∣ p ^ j - 1 ↔ 6 ∣ j := by
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hj⟩ := exists_ppd hp hp2 (k := 6) (by norm_num)
  refine ⟨ℓ, hℓ, hℓ2, hℓp, ?_, hj⟩
  have h6 : ℓ ∣ p ^ 6 - 1 := (hj 6).mpr dvd_rfl
  have h3 : ¬ ℓ ∣ p ^ 3 - 1 := fun h => by
    have := (hj 3).mp h
    omega
  have hfac : p ^ 6 - 1 = (p ^ 3 + 1) * (p ^ 3 - 1) := by
    have h1 : p ^ 6 = (p ^ 3) ^ 2 := by ring
    rw [h1]
    have := Nat.sq_sub_sq (p ^ 3) 1
    simpa using this
  rw [hfac] at h6
  rcases (Nat.Prime.dvd_mul hℓ).mp h6 with h | h
  · exact h
  · exact absurd h h3

theorem two_ne_zero_of_charP {R : Type*} [Ring R] {p : ℕ} [CharP R p] (hp : 3 ≤ p) :
    (2 : R) ≠ 0 := by
  intro h
  have h1 : ((2 : ℕ) : R) = 0 := by exact_mod_cast h
  have h2 := Nat.le_of_dvd (by norm_num) ((CharP.cast_eq_zero_iff R p 2).mp h1)
  omega

theorem dihedral_case {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (ρ : projSL 2 (GaloisField p (3 * 1)) →* Module.End (ZMod p) V) (hρ : Function.Injective ρ) :
    ∃ t : projSL 2 (GaloisField p (3 * 1)), orderOf t = 2 ∧
      3 ≤ Module.finrank (ZMod p) (LinearMap.ker (ρ t - 1)) := by
  have hpp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  obtain ⟨ℓ, hℓ, hℓ2, hℓp, hℓd, hppd⟩ := exists_ppd_six hpp hp2
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hcard : Nat.card (GaloisField p (3 * 1)) = p ^ 3 := by
    simpa using GaloisField.card p (3 * 1) (by norm_num)
  have h2F : (2 : GaloisField p (3 * 1)) ≠ 0 := two_ne_zero_of_charP (p := p) (by omega)
  have h2K : (2 : ZMod p) ≠ 0 := two_ne_zero_of_charP (p := p) (by omega)
  obtain ⟨h, s, hhℓ, hh1, hs2, hs1, hhs⟩ :=
    exists_dihedral_pair (F := GaloisField p (3 * 1)) h2F hℓ2 (by rw [hcard]; exact hℓd)
  have hB : ρ h ^ ℓ = 1 := by rw [← map_pow, hhℓ, map_one]
  have hB1 : ρ h ≠ 1 := fun hb => hh1 (hρ (by rw [hb, map_one]))
  have hS : ρ s * ρ s = 1 := by rw [← map_mul, hs2, map_one]
  have hBS : ρ h * ρ s * ρ h = ρ s := by rw [← map_mul, ← map_mul, hhs]
  have h1 := six_add_finrank_ker_le hℓp hppd hB hB1
  have h2 := finrank_le_two_mul_ker_add h2K (hℓ.odd_of_ne_two hℓ2) hB hS hBS
  refine ⟨s, orderOf_eq_prime (by rw [pow_two]; exact hs2) hs1, ?_⟩
  omega

theorem cross_case {p r : ℕ} [Fact p.Prime] [Fact r.Prime] (hp : 5 ≤ p) (hr : 5 ≤ r)
    (hrp : r ≠ p) {V : Type} [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V]
    (ρ : projSL 2 (GaloisField p (3 * 1)) →* Module.End (ZMod r) V) (hρ : Function.Injective ρ) :
    ∃ t : projSL 2 (GaloisField p (3 * 1)), orderOf t = 2 ∧
      3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1)) := by
  have hcard : Nat.card (GaloisField p (3 * 1)) = p ^ 3 := by
    simpa using GaloisField.card p (3 * 1) (by norm_num)
  have hpF : (p : GaloisField p (3 * 1)) = 0 := CharP.cast_eq_zero _ p
  have h2F : (2 : GaloisField p (3 * 1)) ≠ 0 := two_ne_zero_of_charP (p := p) (by omega)
  have h2K : (2 : ZMod r) ≠ 0 := two_ne_zero_of_charP (p := r) (by omega)
  have h7 : 7 ≤ Module.finrank (ZMod r) V := by
    let σ : SL(2, GaloisField p (3 * 1)) →* Module.End (ZMod r) V :=
      ρ.comp (toProjSL (GaloisField p (3 * 1)))
    have h1 : σ (uu 1) ≠ 1 := by
      intro h
      have h' : toProjSL (GaloisField p (3 * 1)) (uu 1) = 1 := hρ (by rw [map_one]; exact h)
      obtain ⟨c, -, hc⟩ := eq_scalar_of_toProjSL_eq_one h'
      have := congrFun (congrFun hc 0) 1
      simp [uu] at this
    have hrp' : ¬ r ∣ p := fun h => hrp ((Nat.prime_dvd_prime_iff_eq Fact.out Fact.out).mp h)
    have h3 := card_squares_le_finrank_zmod hpF hrp' σ h1
    have h4 := card_units_le_two_mul_card_squares (GaloisField p (3 * 1))
    rw [Nat.card_units, hcard] at h4
    have hp3 : 125 ≤ p ^ 3 := calc
      125 = 5 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp 3
    omega
  obtain ⟨x, y, hxy⟩ : ∃ x y : GaloisField p (3 * 1), x ^ 2 + y ^ 2 = -1 := by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    obtain ⟨a, b, hab⟩ := CharP.sq_add_sq (GaloisField p (3 * 1)) p (-1)
    exact ⟨a, b, by simpa using hab⟩
  obtain ⟨a, b, ha, hb, hab, ha1, hb1, hab1⟩ := exists_klein h2F ⟨x, y, hxy⟩
  exact exists_involution_of_klein ha hb hab ha1 hb1 hab1 h2K ρ h7

end L2CubeFaithful

theorem l2CubeFaithfulFix_holds : SimsR1L2CubeFaithfulFix := by
  intro p _ hp r _ hr V _ _ _ ρ hρ
  by_cases hrp : r = p
  · subst hrp
    exact L2CubeFaithful.dihedral_case hp ρ hρ
  · exact L2CubeFaithful.cross_case hp hr hrp ρ hρ

end CFSG.RankThree.PartTwo.Sec11.SimsR1
