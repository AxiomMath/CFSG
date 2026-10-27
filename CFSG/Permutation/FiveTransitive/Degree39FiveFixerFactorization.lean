module

public import CFSG.Permutation.FiveTransitive.Degree39TwoPartBound
public import CFSG.Permutation.FiveTransitive.Degree39LargePrimeFree
public import CFSG.Permutation.FiveTransitive.Degree39SylowThreeOrder

public section

namespace CFSG

namespace FiveTransitive.Degree39FiveFixerFactorization

open MulAction

private theorem factor_exponents {h : ℕ} (hh : h ≠ 0)
    (htwo : ∀ a : ℕ, 2 ^ a ∣ h → a ≤ 16) (hnine : ¬ 9 ∣ h)
    (hprime : ∀ p : ℕ, p.Prime → p ∣ h → p = 2 ∨ p = 3) :
    ∃ a ≤ 16, ∃ b ≤ 1, h = 2 ^ a * 3 ^ b := by
  let a := h.factorization 2
  let b := h.factorization 3
  have ha : 2 ^ a ∣ h := Nat.prime_two.pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hb : 3 ^ b ∣ h := (show Nat.Prime 3 by norm_num).pow_dvd_iff_le_factorization hh |>.mpr le_rfl
  have hble : b ≤ 1 := by
    by_contra hn
    exact hnine ((show 3 ^ 2 ∣ 3 ^ b from pow_dvd_pow 3 (by omega)).trans hb)
  have h2 : 2 ^ a ≠ 0 := pow_ne_zero _ (by norm_num)
  have h3 : 3 ^ b ≠ 0 := pow_ne_zero _ (by norm_num)
  refine ⟨a,htwo a ha,b,hble,?_⟩
  apply Nat.eq_of_factorization_eq hh (mul_ne_zero h2 h3)
  intro p
  rw [Nat.factorization_mul h2 h3]
  simp only [Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply]
  by_cases hp2 : p = 2
  · subst p
    norm_num [a,Nat.prime_two.factorization,(show Nat.Prime 3 by norm_num).factorization]
  by_cases hp3 : p = 3
  · subst p
    norm_num [b,Nat.prime_two.factorization,(show Nat.Prime 3 by norm_num).factorization]
  have hz : h.factorization p = 0 := by
    rw [Nat.factorization_eq_zero_iff]
    by_cases hp : p.Prime
    · exact Or.inr (Or.inl (fun hd => (hprime p hp hd).elim hp2 hp3))
    · exact Or.inl hp
  simp [hz,Nat.prime_two.factorization,(show Nat.Prime 3 by norm_num).factorization,hp2,hp3]

theorem card_exponents
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ∃ a ≤ 16, ∃ b ≤ 1,
      Nat.card (fixingSubgroup P s) = 2 ^ a * 3 ^ b := by
  apply factor_exponents Nat.card_pos.ne'
    (Degree39TwoPartBound.two_pow_dvd_bound P hcard h5 hnotAlt s hs)
    (Degree39SylowThreeOrder.nine_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs)
  intro p hp hpdiv
  have hlt : p < 7 := by
    by_contra hn
    exact Degree39LargePrimeFree.not_dvd_five_fixer P hcard h5 hnotAlt s hs p hp (by omega) hpdiv
  have hp2 := hp.two_le
  have hp4 : p ≠ 4 := by intro he; rw [he] at hp; norm_num at hp
  have hp6 : p ≠ 6 := by intro he; rw [he] at hp; norm_num at hp
  have hp5 : p ≠ 5 := by
    intro he
    subst p
    exact Degree39FiveFree.five_not_dvd_five_fixer_card P hcard h5 hnotAlt s hs hpdiv
  omega

end FiveTransitive.Degree39FiveFixerFactorization

end CFSG
