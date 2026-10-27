module

public import CFSG.Permutation.FiveTransitive.Degree54PrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.Degree54PrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree54PrimeCyclicExclusion
public import CFSG.Permutation.FiveTransitive.Degree54ElevenCentralizer
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.Degree54SmallPrimesFree

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime) (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
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
  obtain ⟨height,hupper,hAlt⟩ := Degree54PrimeFixed.bounds_and_alternating
    p hp hcases P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at height
  change Nat.card F ≤ 27 at hupper
  change alternatingGroup F ≤ rho.range at hAlt
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hmod
  rw [Nat.card_eq_fintype_card,hcard,← hfixeq] at hmod
  have htuple := Degree54PrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    (28 - Nat.card F) (by rw [← hfixeq]; omega)
  rw [← hfixeq] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hepos : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    apply hS
    rw [← hQcard,he,he0,pow_zero]
  have hQprime : Nat.card Q = p := by
    by_cases hp11 : p = 11
    · rw [hp11] at hQ he hmod ⊢
      let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      have hFcases : Nat.card F = 10 ∨ Nat.card F = 21 := by omega
      have he2 : e ≤ 2 := by
        by_contra hn
        have h1331 : 1331 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow 11 (by omega : 3 ≤ e)
        have hc := h1331.trans htuple
        rcases hFcases with h | h <;> rw [h] at hc <;> norm_num at hc
      have hQ121 : Nat.card Q ≤ 121 := by
        rw [he]
        exact Nat.pow_le_pow_right (by norm_num : 0 < 11) he2
      have hsevenImage : 7 ∣ Nat.card rho.range :=
        (odd_prime_dvd_alternating_card F (by norm_num : Nat.Prime 7) (by norm_num)
          (by rw [← Nat.card_eq_fintype_card]; omega)).trans
          (Subgroup.card_dvd_of_le hAlt)
      have hsevenN : 7 ∣ Nat.card N := hsevenImage.trans (Subgroup.card_range_dvd rho)
      let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) 7 hsevenN
      exact False.elim (Degree54ElevenCentralizer.excluded P hcard h5 hnotAlt Q hQ
        hQ121 (by rw [← hfixeq]; omega) z hz)
    · have hsmall : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 := by tauto
      have he1 : e ≤ 1 := by
        by_contra hn
        have hp2 : p ^ 2 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow p (by omega : 2 ≤ e)
        have hc := hp2.trans htuple
        rcases hsmall with rfl | rfl | rfl | rfl
        · have hF : Nat.card F = 15 := by omega
          rw [hF] at hc
          norm_num at hc
        · have hF : Nat.card F = 20 := by omega
          rw [hF] at hc
          norm_num at hc
        · have hF : Nat.card F = 16 := by omega
          rw [hF] at hc
          norm_num at hc
        · have hF : Nat.card F = 8 := by omega
          rw [hF] at hc
          norm_num at hc
      have heq : e = 1 := by omega
      simpa only [heq,pow_one] using he
  let r : P := u
  have hr : orderOf r = p := (Subgroup.orderOf_coe u).trans hu
  have hRQ : zpowers r = Q := by
    apply Subgroup.eq_of_le_of_card_ge
    · apply zpowers_le.mpr
      exact ⟨u,hZS (mem_zpowers u),rfl⟩
    · rw [Nat.card_zpowers,hr,hQprime]
  let instR : Fintype (PrimeCyclicFixedAction.cyclicFixedPoints X P r) := Fintype.ofFinite _
  have htransport (A : Subgroup P) [iA : Fintype (FixedNormalizerAction.Fixed (X := X) A)] (hA : A = Q) :
      5 ≤ Nat.card (FixedNormalizerAction.Fixed (X := X) A) ∧
      alternatingGroup (FixedNormalizerAction.Fixed (X := X) A) ≤ FixedNormalizerAction.Image (X := X) A := by
    subst A
    cases Subsingleton.elim iA instF
    exact ⟨height,hAlt⟩
  obtain ⟨hF,hJ⟩ := @htransport (zpowers r) instR hRQ
  exact @Degree54PrimeCyclicExclusion.excluded X _ _ p hp
    (by rcases hcases with rfl | rfl | rfl | rfl | rfl <;> norm_num) P hcard h5 hnotAlt r instR hr hF hJ

end FiveTransitive.Degree54SmallPrimesFree

end CFSG
