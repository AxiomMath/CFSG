module

public import CFSG.Permutation.FiveTransitive.Degree80SevenOrbitKernel
public import CFSG.Permutation.FiveTransitive.Degree80SevenCount
public import CFSG.Permutation.FiveTransitive.A9PrimeFreeOrbitImage
public import CFSG.Permutation.FiveTransitive.TenAlternatingImageSection

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenSingleFiveLift
open MulAction SylowFixedActionCore A9PrimeFreeOrbitImage

theorem exists_five_with_fixed_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    let F := sylowFixedPoints X P s S
    ∃ g : sylowNormalizer X P s S, orderOf g = 5 ∧
      Nat.card (Function.fixedPoints (toPermHom (sylowNormalizer X P s S) F g)) = 5 ∧
      Nat.card (Function.fixedPoints
        (NormalizerOrbitFamily.toPermHom (X := X) (sylowImage X P s S) 7 g)) = 5 := by
  classical
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let E := NormalizerOrbitFamily.Family (X := X) Q 7
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype E := Fintype.ofFinite _
  let rho := toPermHom (sylowNormalizer X P s S) F
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q 7
  obtain ⟨hF,hAlt⟩ := Degree80SevenFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  have hE : Nat.card E = 10 := Degree80SevenCount.seven_family_card P hcard h5 hnotAlt s hs S hS
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 10 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hfree := Degree80SevenOrbitKernel.five_not_dvd_card_kernel P hcard h5 hnotAlt Q hQ hcommon
    (Degree80SevenOrbits.exterior_orbit_card_seven P hcard h5 hnotAlt s hs S hS)
  obtain ⟨n,hn,hlocal,hlabels⟩ := TenAlternatingImageSection.exists_single_five_lift hF hE
    (fixedHom rho) (fixedHom_surjective rho hAlt) (labelHom rho sigma)
    (five_not_dvd_kernel rho sigma hfree)
  exact ⟨n.val,(Subgroup.orderOf_coe n).trans hn,hlocal,hlabels⟩

end FiveTransitive.Degree80SevenSingleFiveLift

end CFSG
