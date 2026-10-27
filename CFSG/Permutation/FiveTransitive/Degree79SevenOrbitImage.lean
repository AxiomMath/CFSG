module

public import CFSG.Permutation.FiveTransitive.Degree79SevenOrbitKernel
public import CFSG.Permutation.FiveTransitive.A9PrimeFreeOrbitImage
public import CFSG.Permutation.FiveTransitive.Degree79SevenOrbits

public section

namespace CFSG

namespace FiveTransitive.Degree79SevenOrbitImage
open MulAction SylowFixedActionCore A9PrimeFreeOrbitImage

theorem exists_surjective_factor
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    let F := sylowFixedPoints X P s S
    let _ : Fintype F := Fintype.ofFinite _
    let rho := toPermHom (sylowNormalizer X P s S) F
    let sigma := NormalizerOrbitFamily.toPermHom (X := X) (sylowImage X P s S) 7
    ∃ r : (labelHom rho sigma).range →* alternatingGroup F,
      Function.Surjective r ∧ ∀ n : AltPreimage rho,
        r ((labelHom rho sigma).rangeRestrict n) = fixedHom rho n := by
  classical
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho := toPermHom (sylowNormalizer X P s S) F
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q 7
  obtain ⟨hF,hAlt⟩ := Degree79SevenFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 9 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hfree := Degree79SevenOrbitKernel.five_not_dvd_card_kernel P hcard h5 hnotAlt Q hQ hcommon
    (Degree79SevenOrbits.exterior_orbit_card_seven P hcard h5 hnotAlt s hs S hS)
  exact A9PrimeFreeOrbitImage.exists_surjective_factor hF rho hAlt sigma hfree

theorem exists_five_with_label_order
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    let F := sylowFixedPoints X P s S
    let _ : Fintype F := Fintype.ofFinite _
    let rho := toPermHom (sylowNormalizer X P s S) F
    let sigma := NormalizerOrbitFamily.toPermHom (X := X) (sylowImage X P s S) 7
    ∃ n : AltPreimage rho, orderOf n = 5 ∧ orderOf (labelHom rho sigma n) = 5 := by
  classical
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite _
  let rho := toPermHom (sylowNormalizer X P s S) F
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q 7
  obtain ⟨hF,hAlt⟩ := Degree79SevenFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 9 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hfree := Degree79SevenOrbitKernel.five_not_dvd_card_kernel P hcard h5 hnotAlt Q hQ hcommon
    (Degree79SevenOrbits.exterior_orbit_card_seven P hcard h5 hnotAlt s hs S hS)
  exact A9PrimeFreeOrbitImage.exists_five_with_label_order hF rho hAlt sigma hfree

end FiveTransitive.Degree79SevenOrbitImage

end CFSG
