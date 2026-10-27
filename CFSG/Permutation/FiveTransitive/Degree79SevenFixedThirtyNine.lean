module

public import CFSG.Permutation.FiveTransitive.Degree79SevenOrbitImage
public import CFSG.Permutation.FiveTransitive.Degree79SevenLabelFixed
public import CFSG.Permutation.FiveTransitive.A9TenQuotientFiveSupport

public section

namespace CFSG

namespace FiveTransitive.Degree79SevenFixedThirtyNine
open MulAction SylowFixedActionCore A9PrimeFreeOrbitImage

private theorem exists_normalizer_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 5 ∧
      Nat.card (Function.fixedPoints g.val.val) = 39 := by
  classical
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let E := NormalizerOrbitFamily.Family (X := X) Q 7
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype E := Fintype.ofFinite _
  let rho := toPermHom (sylowNormalizer X P s S) F
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q 7
  let B := (labelHom rho sigma).range
  obtain ⟨tau,htau,_⟩ := Degree79SevenOrbitImage.exists_surjective_factor P hcard h5 hnotAlt s hs S hS
  obtain ⟨n,hn,hnlabel⟩ := Degree79SevenOrbitImage.exists_five_with_label_order P hcard h5 hnotAlt s hs S hS
  let b : B := (labelHom rho sigma).rangeRestrict n
  have hb : orderOf b = 5 := (Subgroup.orderOf_coe b).symm.trans hnlabel
  have hF : Nat.card F = 9 :=
    (Degree79SevenFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS).1
  have hE : Nat.card E = 10 := Degree79SevenOrbits.seven_family_card P hcard h5 hnotAlt s hs S hS
  have hlabels := A9TenQuotientFiveSupport.fixed_card_five hF hE B tau htau b hb
  rw [← Nat.card_coe_set_eq] at hlabels
  have hg : orderOf n.val = 5 := (Subgroup.orderOf_coe n).trans hn
  refine ⟨n.val,hg,?_⟩
  exact Degree79SevenLabelFixed.fixed_card_eq_thirtyNine P hcard h5 hnotAlt Q
    (S.isPGroup'.map (fixingSubgroup P s).subtype) n.val hg hlabels

theorem exists_ambient_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : P, orderOf g = 5 ∧ Nat.card (Function.fixedPoints g.val) = 39 := by
  obtain ⟨g,hg,hfix⟩ := exists_normalizer_five P hcard h5 hnotAlt s hs S hS
  exact ⟨g.val,(Subgroup.orderOf_coe g).trans hg,hfix⟩

end FiveTransitive.Degree79SevenFixedThirtyNine

end CFSG
