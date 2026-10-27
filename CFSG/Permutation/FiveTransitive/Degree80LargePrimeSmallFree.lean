module

public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeFixed
public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeArithmetic
public import CFSG.Permutation.FiveTransitive.Degree80LargePrimeSupport

public section

namespace CFSG

namespace FiveTransitive.Degree80LargePrimeSmallFree
open MulAction SylowFixedActionCore

theorem not_dvd_five_fixer
    {X : Type} [Fintype X] [DecidableEq X]
    (p : ℕ) (hp : p.Prime)
    (hcases : p = 11 ∨ p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23 ∨ p = 29 ∨ p = 31 ∨ p = 37)
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
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
  have hQ : IsPGroup p Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  obtain ⟨hlo,hhi,hN5⟩ := Degree80LargePrimeFixed.bounds_and_transitive
    p hp P hcard h5 hnotAlt s hs S hS
  have hmod := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % p = Nat.card F % p at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  obtain ⟨hfstrict,q,hq,hpq,hqpred,hqdvd,hgap⟩ :=
    Degree80LargePrimeArithmetic.normalizer_prime p (Nat.card F) hcases hlo hhi hmod
  let _ : Fact q.Prime := ⟨hq⟩
  have htuple : (Nat.card F).descFactorial 5 ∣ Nat.card N := by
    simpa only [Nat.card_eq_fintype_card] using
      (FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
        (by simpa only [Nat.card_eq_fintype_card] using hlo) hN5)
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) q (hqdvd.trans htuple)
  have hzpow : z ^ q = 1 := by rw [← hz,pow_orderOf_eq_one]
  have hgap' : 80 < p * q + Nat.card (fixedPoints Q X) := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hgap
  have hhi' : Nat.card (fixedPoints Q X) ≤ 39 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hfstrict
  have hb := Degree80LargePrimeSupport.support_le_fixed P hcard p q hp hq
    (by omega) hpq hqpred Q hQ hgap' z hzpow
  have hzne : z.val.val ≠ 1 := by
    intro he
    have hez : z = 1 := Subtype.ext (Subtype.ext he)
    rw [hez,orderOf_one] at hz
    have hh := hq.two_le
    omega
  have hm := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt z.val.property hzne
  rw [hcard] at hm
  omega

end FiveTransitive.Degree80LargePrimeSmallFree

end CFSG
