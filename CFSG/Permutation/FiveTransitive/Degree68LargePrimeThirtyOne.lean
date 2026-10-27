module

public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeTupleDivisibility
public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeAlternating
public import CFSG.Permutation.FiveTransitive.Degree68LargePrimeCyclicExclusion

public section

namespace CFSG

namespace FiveTransitive.Degree68LargePrimeThirtyOne

open MulAction Subgroup SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 68)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) : ¬ 31 ∣ Nat.card (fixingSubgroup P s) := by
  classical
  intro hd
  let p := 31
  have hp : p.Prime := by decide
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
  obtain ⟨height,hupper,_hN5⟩ := Degree68LargePrimeFixed.bounds_and_transitive
    p hp P hcard h5 hnotAlt s hs S hS
  change 5 ≤ Nat.card F at height
  change Nat.card F ≤ 34 at hupper
  have hAlt := Degree68LargePrimeAlternating.alternating_image p hp (by decide) P hcard h5 hnotAlt s hs S hS
  change alternatingGroup F ≤ rho.range at hAlt
  have hmod := hQ.card_modEq_card_fixedPoints X
  change Nat.card X % p = Nat.card (fixedPoints Q X) % p at hmod
  rw [Nat.card_eq_fintype_card,hcard,← hfixeq] at hmod
  have htuple := Degree68LargePrimeTupleDivisibility.card_dvd_desc P hcard h5 hnotAlt Q
    (35 - Nat.card F) (by rw [← hfixeq]; omega)
  rw [← hfixeq] at htuple
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hQ
  have hepos : 1 ≤ e := by
    by_contra hn
    have he0 : e = 0 := by omega
    apply hS
    rw [← hQcard,he,he0,pow_zero]
  have hQprime : Nat.card Q = p := by
    have he1 : e ≤ 1 := by
      by_contra hn
      have hp2 : p ^ 2 ∣ Nat.card Q := by rw [he]; exact pow_dvd_pow p (by omega : 2 ≤ e)
      have hc := hp2.trans htuple
      have hF : Nat.card F = 6 := by dsimp only [p] at hmod; omega
      rw [hF] at hc
      norm_num [p] at hc
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
  exact @Degree68LargePrimeCyclicExclusion.excluded X _ _ p hp
    (by decide) P hcard h5 hnotAlt r instR hr hF hJ

end FiveTransitive.Degree68LargePrimeThirtyOne

end CFSG
