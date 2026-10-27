module

public import CFSG.Permutation.FiveTransitive.Degree58PrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.Degree58SylowPrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree58LargePrimeElevenCentralizer
public import CFSG.Permutation.FiveTransitive.Degree58LargePrimeFiveCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree58SmallPrimesFree

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 58)
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
  let instF : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  have hQ : IsPGroup p Q := S.isPGroup'.map _
  have hQcard : Nat.card Q = Nat.card S := Subgroup.card_map_of_injective H.subtype_injective
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
  obtain ⟨height,hupper,hN5⟩ := Degree58SylowPrimeFixed.bounds_and_transitive
    p hp P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at height
  change Nat.card F ≤ 29 at hupper
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hmod
  rw [Nat.card_eq_fintype_card,hcard,← hfixeq] at hmod
  have htuple := Degree58PrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    (30 - Nat.card F) (by rw [← hfixeq]; omega)
  rw [← hfixeq] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  by_cases hp11 : p = 11
  · rcases hp11 with rfl
    have hFcases : Nat.card F = 14 ∨ Nat.card F = 25 := by omega
    have he2 : e ≤ 2 := by
      by_contra hn
      have h1331 : 1331 ∣ Nat.card Q := by
        rw [he]
        exact pow_dvd_pow 11 (by omega : 3 ≤ e)
      have hc := h1331.trans htuple
      rcases hFcases with h | h <;> rw [h] at hc <;> norm_num at hc
    have hQ121 : Nat.card Q ≤ 121 := by
      rw [he]
      exact Nat.pow_le_pow_right (by decide : 0 < 11) he2
    have hAlt := Degree58SylowPrimeFixed.eleven_alternating P hcard h5 hnotAlt s hs S hS
    have hsevenImage : 7 ∣ Nat.card rho.range :=
      (odd_prime_dvd_alternating_card F (by decide : Nat.Prime 7) (by decide)
        (by rw [← Nat.card_eq_fintype_card]; omega)).trans (Subgroup.card_dvd_of_le hAlt)
    let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 7
      (hsevenImage.trans (Subgroup.card_range_dvd rho))
    exact Degree58LargePrimeElevenCentralizer.excluded P hcard h5 hnotAlt Q hQ hQ121
      (by rw [← hfixeq]; omega) z hz
  · have hsmall : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by tauto
    have hQbound : Nat.card Q ≤ if p = 19 then 19 else p ^ 2 := by
      by_cases hp19 : p = 19
      · rcases hp19 with rfl
        have hF : Nat.card F = 20 := by omega
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
          · have hF : Nat.card F = 6 ∨ Nat.card F = 19 := by omega
            rcases hF with h | h <;> rw [h] at hc <;> norm_num at hc
          · have hF : Nat.card F = 7 ∨ Nat.card F = 24 := by omega
            rcases hF with h | h <;> rw [h] at hc <;> norm_num at hc
          · exact hp19 rfl
          · have hF : Nat.card F = 12 := by omega
            rw [hF] at hc
            norm_num at hc
        simp only [hp19,↓reduceIte,he]
        exact Nat.pow_le_pow_right hp.pos he2
    let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
      (Degree58SylowPrimeFixed.five_dvd_card hN5 height)
    exact Degree58LargePrimeFiveCentralizer.excluded P hcard h5 hnotAlt p hp hsmall Q hQ hQbound
      (by rw [← hfixeq]; rcases hsmall with rfl | rfl | rfl | rfl <;> omega) z hz

end FiveTransitive.Degree58SmallPrimesFree

end CFSG
