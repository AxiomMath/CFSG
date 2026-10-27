module

public import CFSG.Permutation.FiveTransitive.Degree80SevenOrbits
public import CFSG.Permutation.FiveTransitive.Degree80SevenArithmetic
public import CFSG.Permutation.FiveTransitive.PrimeOrbitNormalizerSupport
public import CFSG.Permutation.FiveTransitive.SmallDegreeFixedAction
public import CFSG.Permutation.FiveTransitive.NormalizerExteriorOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenFixed
open MulAction SylowFixedActionCore

theorem fixed_card_and_alternating
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    let _ : Fintype (sylowFixedPoints X P s S) := Fintype.ofFinite _
    Nat.card (sylowFixedPoints X P s S) = 10 ∧
      alternatingGroup (sylowFixedPoints X P s S) ≤
        (toPermHom (sylowNormalizer X P s S) (sylowFixedPoints X P s S)).range := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  obtain ⟨hlo,hhi,hN5⟩ := Degree80LargePrimeFixed.bounds_and_transitive
    7 (by decide) P hcard h5 hnotAlt s hs S hS
  have hmod := SylowFixedActionPrimeFree.fixed_degree_modEq X P s S
  change Nat.card X % 7 = Nat.card F % 7 at hmod
  rw [Nat.card_eq_fintype_card,hcard] at hmod
  have hF : Nat.card F = 10 := by
    by_contra hn
    obtain ⟨hstrict,q,hq,hql,hcop,hpred,hdiv⟩ :=
      Degree80SevenArithmetic.normalizer_prime (Nat.card F) hlo hhi hmod hn
    let _ : Fact q.Prime := ⟨hq⟩
    have htuple : (Nat.card F).descFactorial 5 ∣ Nat.card N := by
      simpa only [Nat.card_eq_fintype_card] using
        (FiveTransitive.descFactorial_dvd_card_of_isMultiplyPretransitive N F 5
          (by simpa only [Nat.card_eq_fintype_card] using hlo) hN5)
    obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := N) q (hdiv.trans htuple)
    have hcommonlo : 5 ≤ Nat.card (fixedPoints Q X) := by
      rw [← FixedNormalizerAction.fixed_eq Q]
      exact hlo
    have hcommonstrict : Nat.card (fixedPoints Q X) ≤ 39 := by
      rw [← FixedNormalizerAction.fixed_eq Q]
      exact hstrict
    have hfamily : Nat.card (NormalizerOrbitFamily.Family (X := X) Q 7) < q := by
      have hh := NormalizerExteriorOrbitFamily.card_mul_add_fixed_le (X := X) Q 7 (by decide)
      rw [Nat.card_eq_fintype_card (α := X),hcard] at hh
      omega
    have hb := PrimeOrbitNormalizerSupport.support_le_fixed P 7 q (by decide) hq
      hcop hpred Q hQ
      (Degree80SevenOrbits.exterior_orbit_card_seven P hcard h5 hnotAlt s hs S hS)
      hfamily z (hz ▸ pow_orderOf_eq_one z)
    have hne : z.val.val ≠ 1 := by
      intro he
      have hez : z = 1 := Subtype.ext (Subtype.ext he)
      rw [hez,orderOf_one] at hz
      have hh := hq.two_le
      omega
    have hm := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5
      hnotAlt z.val.property hne
    rw [hcard] at hm
    omega
  refine ⟨hF,?_⟩
  let J := (toPermHom N F).range
  apply SmallDegreeFixedAction.alternatingGroup_le_of_card_le_twentySeven_away_mathieu F J
  · rw [← Nat.card_eq_fintype_card,hF]; omega
  · rw [← Nat.card_eq_fintype_card,hF]; omega
  · rw [← Nat.card_eq_fintype_card,hF]; omega
  · rw [← Nat.card_eq_fintype_card,hF]; omega
  · intro a b ha hb
    obtain ⟨g,hg⟩ := hN5.exists_smul_eq (⟨a,ha⟩ : Fin 5 ↪ F) ⟨b,hb⟩
    exact ⟨⟨toPermHom N F g,⟨g,rfl⟩⟩,fun i => DFunLike.congr_fun hg i⟩

end FiveTransitive.Degree80SevenFixed

end CFSG
