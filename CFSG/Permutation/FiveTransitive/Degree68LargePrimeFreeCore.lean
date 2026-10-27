module

public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeSevenLift
public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeThirtyOne
public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeLong

public section

namespace CFSG

namespace FiveTransitive.Degree68LargePrimeFreeCore
open MulAction Subgroup SylowFixedActionCore

private theorem small_not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
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
  have h7 := Degree68LargePrimeSevenLift.seven_dvd_normalizer p hp hcases P hcard h5 hnotAlt s hs S hS
  exact hseven (h7.trans (Subgroup.card_subgroup_dvd_card (sylowNormalizer X P s S)))

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hseven : ¬ 7 ∣ Nat.card P) (s : Set X) (hs : s.ncard = 5)
    (p : ℕ) (hp : p.Prime) (hlarge : 11 ≤ p) : ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  by_cases hsmall : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29
  · exact small_not_dvd_five_fixer p hp hsmall P hcard h5 hnotAlt hseven s hs
  by_cases h31 : p = 31
  · subst p
    exact Degree68LargePrimeThirtyOne.not_dvd_five_fixer P hcard h5 hnotAlt s hs
  have h32 : 32 ≤ p := by
    by_contra hn
    have hu : p ≤ 31 := by omega
    interval_cases p <;> norm_num at *
  let sf := s.toFinite.toFinset
  have he : (sf : Set X) = s := s.toFinite.coe_toFinset
  have hsf : sf.card = 5 := by rw [← Set.ncard_coe_finset,he]; exact hs
  have hh := Degree68LargePrimeLong.long_not_dvd_five_fixer P hcard h5 hnotAlt sf hsf p hp h32
  rwa [he] at hh

end FiveTransitive.Degree68LargePrimeFreeCore

end CFSG
