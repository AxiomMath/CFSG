module

public import CFSG.Permutation.FiveTransitive.Degree36SmallPrimeBound
public import CFSG.Permutation.FiveTransitive.Degree36LargePrimeFree

public section

namespace CFSG

namespace FiveTransitive.Degree36FiveFixerFactors

open MulAction

private theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (hdiv : h ∣ 23118159385601280000)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 3 ∨ p = 5) :
    ∃ a ≤ 11, ∃ b ≤ 8, ∃ c ≤ 4, h = 2 ^ a * 3 ^ b * 5 ^ c := by
  let a := h.factorization 2
  let b := h.factorization 3
  let c := h.factorization 5
  have ha : 2 ^ a ∣ h := Nat.prime_two.pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hb : 3 ^ b ∣ h := (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hc : 5 ^ c ∣ h := (show Nat.Prime 5 by norm_num).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hale : a ≤ 11 := by
    by_contra hn
    have hd : 4096 ∣ h := (show 2^12 ∣ 2^a from pow_dvd_pow 2 (by omega)).trans ha
    have he := hd.trans hdiv
    norm_num at he
  have hble : b ≤ 8 := by
    by_contra hn
    have hd : 19683 ∣ h := (show 3^9 ∣ 3^b from pow_dvd_pow 3 (by omega)).trans hb
    have he := hd.trans hdiv
    norm_num at he
  have hcle : c ≤ 4 := by
    by_contra hn
    have hd : 3125 ∣ h := (show 5^5 ∣ 5^c from pow_dvd_pow 5 (by omega)).trans hc
    have he := hd.trans hdiv
    norm_num at he
  have h2 : 2 ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : 3 ^ b ≠ 0 := pow_ne_zero _ (by norm_num)
  have h5 : 5 ^ c ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨a,hale,b,hble,c,hcle,?_⟩
  apply Nat.eq_of_factorization_eq hh (mul_ne_zero (mul_ne_zero h2 h3) h5)
  intro p
  rw [Nat.factorization_mul (mul_ne_zero h2 h3) h5,Nat.factorization_mul h2 h3]
  simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst p
    norm_num [a,Nat.prime_two.factorization,(show Nat.Prime 3 by norm_num).factorization,
      (show Nat.Prime 5 by norm_num).factorization]
  by_cases hp3 : p = 3
  · subst p
    norm_num [b,Nat.prime_two.factorization,(show Nat.Prime 3 by norm_num).factorization,
      (show Nat.Prime 5 by norm_num).factorization]
  by_cases hp5 : p = 5
  · subst p
    norm_num [c,Nat.prime_two.factorization,(show Nat.Prime 3 by norm_num).factorization,
      (show Nat.Prime 5 by norm_num).factorization]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => (hprime p hp hd).elim hp2 (fun he => he.elim hp3 hp5)))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,(show Nat.Prime 3 by norm_num).factorization,
    (show Nat.Prime 5 by norm_num).factorization,hp2,hp3,hp5]

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a ≤ 11, ∃ b ≤ 8, ∃ c ≤ 4,
      Nat.card (fixingSubgroup P s) = 2 ^ a * 3 ^ b * 5 ^ c := by
  have hfix : 5 ≤ Nat.card (fixedPoints (fixingSubgroup P s) X) := by
    rw [Nat.card_coe_set_eq,← hs]
    exact Set.ncard_le_ncard (by
      intro x hx q
      exact (mem_fixingSubgroup_iff P).mp q.property x hx)
  have hd := Degree36SmallPrimeBound.card_dvd_exterior_tuples
    P hcard h5 hnotAlt (fixingSubgroup P s) 5 14 (by norm_num) hfix
  norm_num [Nat.descFactorial] at hd
  apply factor_exponents Nat.card_pos.ne' hd
  intro p hp hpdiv
  have hlt : p < 7 := by
    by_contra hn
    exact Degree36LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hpdiv
  have hp2 := hp.two_le
  have hp4 : p ≠ 4 := by intro he; rw [he] at hp; norm_num at hp
  have hp6 : p ≠ 6 := by intro he; rw [he] at hp; norm_num at hp
  omega

end FiveTransitive.Degree36FiveFixerFactors

end CFSG
