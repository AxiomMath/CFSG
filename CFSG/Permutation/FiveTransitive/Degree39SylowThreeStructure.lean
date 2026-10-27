module

public import CFSG.Permutation.FiveTransitive.Degree39ThreeOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree39SylowThreeEntrance
public import CFSG.Permutation.FiveTransitive.Degree39FiveFree
public import CFSG.Permutation.FiveTransitive.Degree39ThreeOrbitSharpBound

public section

namespace CFSG

namespace FiveTransitive.Degree39SylowThreeStructure

open MulAction SylowFixedActionCore

theorem orbit_card_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1)
    (x : X) (hx : x ∉ fixedPoints (sylowImage X P s S) X) :
    Nat.card (orbit (sylowImage X P s S) x) = 3 := by
  let Q := sylowImage X P s S
  obtain ⟨hF,_,_⟩ := Degree39SylowThreeEntrance.three_entrance P hcard h5 hnotAlt s hs S hS
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← hfixeq]; exact hF
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho : N →* Equiv.Perm F := toPermHom N F
  have him := (Degree39SylowThreeEntrance.three_fixed_card_and_image
    P hcard h5 hnotAlt s hs S hS).2
  have hdiv : 5 ∣ Nat.card rho.range := by
    change 5 ∣ Nat.card (toPermHom N F).range
    rw [him,Subgroup.card_top,Nat.card_perm,hF]
    norm_num [Nat.factorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hdiv.trans (Subgroup.card_range_dvd rho))
  exact Degree39ThreeOrbitGeometry.orbit_card_three_of_fixed_bound
    (by rw [Nat.card_eq_fintype_card,hcard]) Q
    (S.isPGroup'.map (fixingSubgroup P s).subtype) hfixed g hg
    (Degree39FiveFree.fixed_card_eq_four P hcard h5 hnotAlt g.val
      (by simpa only [Subgroup.orderOf_coe] using hg)) x hx

theorem abelian_and_card_bound
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 39)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    IsMulCommutative (sylowImage X P s S) ∧ Nat.card S ≤ 81 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have ho := orbit_card_three P hcard h5 hnotAlt s hs S hS
  have hsmall : ∀ x : X, Nat.card (orbit Q x) ≤ 3 := by
    intro x
    by_cases hx : x ∈ fixedPoints Q X
    · have h := mem_fixedPoints_iff_card_orbit_eq_one.mp hx
      rw [← Nat.card_eq_fintype_card] at h
      omega
    · rw [ho x hx]
  have hF := (Degree39SylowThreeEntrance.three_entrance P hcard h5 hnotAlt s hs S hS).1
  have hfixeq : (sylowFixedPoints X P s S : Set X) = fixedPoints Q X :=
    FixedNormalizerAction.fixed_eq Q
  have hfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← hfixeq]; exact hF
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  refine ⟨SmallThreeOrbitAbelian.isMulCommutative hQ hsmall,?_⟩
  rw [← hQcard]
  exact Degree39ThreeOrbitSharpBound.card_le_eighty_one P hcard h5 hnotAlt Q hQ hfixed ho

end FiveTransitive.Degree39SylowThreeStructure

end CFSG
