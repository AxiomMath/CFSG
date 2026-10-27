module

public import CFSG.Permutation.FiveTransitive.Degree58SylowPrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree67LargePrimeFiveCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree67LargePrimeFiveFree

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 13 ∨ p = 17)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  let H := fixingSubgroup P s
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) p hd
  have hZ : IsPGroup p (zpowers u) := by
    apply IsPGroup.of_card
    rw [Nat.card_zpowers,hu,pow_one]
  obtain ⟨S,hZS⟩ := hZ.exists_le_sylow
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let N := sylowNormalizer X P s S
  have hQ : IsPGroup p Q := S.isPGroup'.map _
  have hSge : p ≤ Nat.card S := by
    have h := Subgroup.card_le_of_le hZS
    rwa [Nat.card_zpowers,hu] at h
  have hS : Nat.card S ≠ 1 := by intro he; rw [he] at hSge; have := hp.two_le; omega
  have hfixeq : (F : Set X) = fixedPoints Q X := by
    ext x
    constructor
    · intro hx q
      exact hx (⟨⟨q.val,Q.le_normalizer q.property⟩,q.property⟩ : sylowInNormalizer X P s S)
    · intro hx q
      exact hx (⟨q.val.val,q.property⟩ : Q)
  obtain ⟨height,hupper,hN5⟩ := Degree67LargePrimeFixed.bounds_and_transitive
    p hp P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at height
  change Nat.card F ≤ 33 at hupper
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hmod
  rw [Nat.card_eq_fintype_card,hcard,← hfixeq] at hmod
  have htuple := Degree67LargePrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    (34 - Nat.card F) (by rw [← hfixeq]; omega)
  rw [← hfixeq] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hsmall := hcases
  have hQbound : Nat.card Q ≤ p ^ 2 := by
    have he2 : e ≤ 2 := by
      by_contra hn
      have hpow : p ^ 3 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow p (by omega : 3 ≤ e)
      have hc := hpow.trans htuple
      rcases hsmall with rfl | rfl
      · have hF : Nat.card F = 15 ∨ Nat.card F = 28 := by omega
        rcases hF with h | h <;> rw [h] at hc <;> norm_num at hc
      · have hF : Nat.card F = 16 ∨ Nat.card F = 33 := by omega
        rcases hF with h | h <;> rw [h] at hc <;> norm_num at hc
    rw [he]
    exact Nat.pow_le_pow_right hp.pos he2
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (Degree58SylowPrimeFixed.five_dvd_card hN5 height)
  exact Degree67LargePrimeFiveCentralizer.excluded P hcard h5 hnotAlt p hp
    (by rcases hsmall with h | h; exact Or.inl h; exact Or.inr (Or.inl h)) Q hQ
    (by have hp19 : p ≠ 19 := by rcases hsmall with rfl | rfl <;> decide
        simpa only [hp19,↓reduceIte] using hQbound)
    (by rw [← hfixeq]; rcases hsmall with rfl | rfl <;> omega)
    (by rw [← hfixeq]; exact hupper) z hz

end FiveTransitive.Degree67LargePrimeFiveFree

end CFSG
