module

public import CFSG.Permutation.FiveTransitive.Degree58SylowPrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree60LargePrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.Degree60LargePrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree60LargePrimeFiveCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree60LargePrimeSmallFree

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 60)
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
  obtain ⟨height,hupper,hN5⟩ := Degree60LargePrimeFixed.bounds_and_transitive
    p hp P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at height
  change Nat.card F ≤ 30 at hupper
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hmod
  rw [Nat.card_eq_fintype_card,hcard,← hfixeq] at hmod
  have htuple := Degree60LargePrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    (31 - Nat.card F) (by rw [← hfixeq]; omega)
  rw [← hfixeq] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hsmall := hcases
  have hQbound : Nat.card Q ≤ if p = 19 then 19 else p ^ 2 := by
    by_cases hp19 : p = 19
    · rcases hp19 with rfl
      have hF : Nat.card F = 22 := by omega
      have he1 : e ≤ 1 := by
        by_contra hn
        have hpow : 19 ^ 2 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 19 (by omega : 2 ≤ e)
        have hc := hpow.trans htuple
        rw [hF] at hc
        norm_num at hc
      simpa only [he,ite_true,pow_one] using Nat.pow_le_pow_right (by decide : 0 < 19) he1
    · have he2 : e ≤ 2 := by
        by_contra hn
        have hpow : p ^ 3 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow p (by omega : 3 ≤ e)
        have hc := hpow.trans htuple
        rcases hsmall with rfl | rfl | rfl | rfl
        · have hF : Nat.card F = 8 ∨ Nat.card F = 21 := by omega
          rcases hF with h | h <;> rw [h] at hc <;> norm_num at hc
        · have hF : Nat.card F = 9 ∨ Nat.card F = 26 := by omega
          rcases hF with h | h <;> rw [h] at hc <;> norm_num at hc
        · exact hp19 rfl
        · have hF : Nat.card F = 14 := by omega
          rw [hF] at hc
          norm_num at hc
      simp only [hp19,↓reduceIte,he]
      exact Nat.pow_le_pow_right hp.pos he2
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (Degree58SylowPrimeFixed.five_dvd_card hN5 height)
  exact Degree60LargePrimeFiveCentralizer.excluded P hcard h5 hnotAlt p hp hsmall Q hQ hQbound
    (by rw [← hfixeq]; rcases hsmall with rfl | rfl | rfl | rfl <;> omega) z hz

end FiveTransitive.Degree60LargePrimeSmallFree

end CFSG
