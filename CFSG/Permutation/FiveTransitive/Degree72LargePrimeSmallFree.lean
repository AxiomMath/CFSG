module

public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeCases
public import CFSG.Permutation.FiveTransitive.Degree72LargePrimeSupport

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeSmallFree
open MulAction SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (hcases : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 72)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) :
    ¬ p ∣ Nat.card (fixingSubgroup P s) := by
  classical
  intro hd
  let _ : Fact p.Prime := ⟨hp⟩
  let H := fixingSubgroup P s
  obtain ⟨u,hu⟩ := exists_prime_orderOf_dvd_card' (G := H) p hd
  have hZ : IsPGroup p (Subgroup.zpowers u) := by
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
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho := toPermHom N F
  let J := rho.range
  have hQ : IsPGroup p Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hF := Degree72LargePrimeCases.fixed_card_cases p hp (Or.inr hcases) P hcard h5 hnotAlt s hs S hS
  have hAlt := Degree72LargePrimeAlternating.alternating_image p hp (Or.inr hcases) P hcard h5 hnotAlt s hs S hS
  obtain ⟨q,hq,hql,hqp,hqpred,hqF⟩ : ∃ q : ℕ, q.Prime ∧ 7 ≤ q ∧ p.Coprime q ∧
      ¬ q ∣ p - 1 ∧ q ≤ Nat.card F := by
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨7,by decide,by decide,by decide,by decide,by dsimp only [F]; omega⟩
    · exact ⟨13,by decide,by decide,by decide,by decide,by dsimp only [F]; omega⟩
    · exact ⟨13,by decide,by decide,by decide,by decide,by dsimp only [F]; omega⟩
    · exact ⟨13,by decide,by decide,by decide,by decide,by dsimp only [F]; omega⟩
    · exact ⟨11,by decide,by decide,by decide,by decide,by dsimp only [F]; omega⟩
    · exact ⟨7,by decide,by decide,by decide,by decide,by dsimp only [F]; omega⟩
  let _ : Fact q.Prime := ⟨hq⟩
  have hdJ : q ∣ Nat.card J :=
    (odd_prime_dvd_alternating_card F hq (by omega) (by rwa [← Nat.card_eq_fintype_card])).trans
      (Subgroup.card_dvd_of_le hAlt)
  have hdN : q ∣ Nat.card N := hdJ.trans (Subgroup.card_range_dvd rho)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) q hdN
  have hzpow : z ^ q = 1 := by rw [← hz,pow_orderOf_eq_one]
  have hlo : 5 ≤ Nat.card (fixedPoints Q X) := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact (Degree72LargePrimeFixed.bounds_and_transitive p hp P hcard h5 hnotAlt s hs S hS).1
  have hhi : Nat.card (fixedPoints Q X) ≤ 26 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    change Nat.card (sylowFixedPoints X P s S) ≤ 26
    omega
  have hb := Degree72LargePrimeSupport.support_le_fixed P hcard p q hp hq
    (by omega) hql hqp hqpred Q hQ hlo z hzpow
  have hzne : z.val.val ≠ 1 := by
    intro he
    have hez : z = 1 := Subtype.ext (Subtype.ext he)
    rw [hez,orderOf_one] at hz
    have hh := hq.two_le
    omega
  have hm := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.val.property hzne
  rw [hcard] at hm
  omega

end FiveTransitive.Degree72LargePrimeSmallFree

end CFSG
