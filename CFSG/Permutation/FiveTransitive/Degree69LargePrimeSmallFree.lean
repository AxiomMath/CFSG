module

public import CFSG.Permutation.FiveTransitive.Degree69LargePrimeSevenLift

public section

namespace CFSG

namespace FiveTransitive.Degree69LargePrimeSmallFree
open MulAction Subgroup SylowFixedActionCore

theorem small_not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 23 ∨ p = 29 ∨ p = 31)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 69)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (s : Set X) (hs : s.ncard = 5) :
    ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  let H := fixingSubgroup P s
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) p hd
  have hZ : IsPGroup p (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  have hSge : p ≤ Nat.card S := by
    have hh := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at hh
  have hS : Nat.card S ≠ 1 := by
    intro he
    rw [he] at hSge
    have hh := hp.two_le
    omega
  have hcases' : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 := by omega
  have h12 : Nat.card (sylowFixedPoints X P s S) ≠ 12 := by
    intro he
    have hm := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
    change Nat.card X % p = Nat.card (sylowFixedPoints X P s S) % p at hm
    rw [Nat.card_eq_fintype_card,hcard,he] at hm
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num at hm
  have h7 := Degree69LargePrimeSevenLift.seven_dvd_normalizer p hp hcases' P hcard h5 hnotAlt s hs S hS h12
  exact hseven (h7.trans (Subgroup.card_subgroup_dvd_card (sylowNormalizer X P s S)))

end FiveTransitive.Degree69LargePrimeSmallFree

end CFSG
