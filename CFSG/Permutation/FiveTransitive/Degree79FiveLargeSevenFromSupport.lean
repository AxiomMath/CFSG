module

public import CFSG.Permutation.FiveTransitive.Degree79FiveOrbitKernel
public import CFSG.Permutation.FiveTransitive.Degree79FiveLabelFixed
public import CFSG.Permutation.FiveTransitive.Degree79FiveSevenLift
public import CFSG.Permutation.FiveTransitive.A9SevenFreeLargeLabels
public import CFSG.Permutation.FiveTransitive.Degree79FiveOrbits

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveLargeSevenFromSupport
open MulAction SylowFixedActionCore A9PrimeFreeOrbitImage

theorem exists_normalizer_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 79)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (hsupport : ∀ {F E : Type} [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E],
      Nat.card F = 9 → Nat.card E ≤ 14 →
      ∀ (B : Subgroup (Equiv.Perm E)) (tau : B →* alternatingGroup F),
        Function.Surjective tau → ∀ b : B, orderOf b = 7 → b.val.support.card ≤ 7)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 5 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 7 ∧
      10 ≤ Nat.card (Function.fixedPoints g.val.val) := by
  classical
  obtain ⟨g,hg⟩ := Degree79FiveSevenLift.exists_seven P hcard h5 hnotAlt s hs S hS
  by_cases hlarge : 10 ≤ Nat.card (Function.fixedPoints g.val.val)
  · exact ⟨g,hg,hlarge⟩
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  let E := NormalizerOrbitFamily.Family (X := X) Q 5
  let _ : Fintype F := Fintype.ofFinite _
  let _ : Fintype E := Fintype.ofFinite _
  let rho := toPermHom (sylowNormalizer X P s S) F
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q 5
  obtain ⟨hF,hAlt⟩ := Degree79FiveFixed.fixed_card_and_alternating P hcard h5 hnotAlt s hs S hS
  have hQ : IsPGroup 5 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hcommon : Nat.card (fixedPoints Q X) = 9 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact hF
  have hX : Nat.card X = 79 := by rw [Nat.card_eq_fintype_card,hcard]
  have hsmall : Nat.card (fixedBy X g.val) ≤ 9 := by
    change Nat.card (Function.fixedPoints g.val.val) ≤ 9
    omega
  have horbit := Degree79FiveOrbits.exterior_orbit_card_five hX.le Q hQ g
    (hg ▸ pow_orderOf_eq_one g) hsmall
  have hE : Nat.card E = 14 := Degree79FiveOrbits.five_family_card hX Q hQ hcommon g
    (hg ▸ pow_orderOf_eq_one g) hsmall
  have hfree := Degree79FiveOrbitKernel.seven_not_dvd_card_kernel P hcard h5 hnotAlt Q hQ hcommon horbit
  obtain ⟨n,hn,hnfixed⟩ := A9SevenFreeLargeLabels.exists_seven hF hE rho hAlt sigma hfree
    (fun B tau htau b hb => hsupport hF hE.le B tau htau b hb)
  have hnval : orderOf n.val = 7 := (Subgroup.orderOf_coe n).trans hn
  have hbound := Degree79FiveLabelFixed.five_mul_fixed_labels_le P Q hQ n.val
    (hnval ▸ pow_orderOf_eq_one n.val)
  refine ⟨n.val,hnval,?_⟩
  change 7 ≤ Nat.card (Function.fixedPoints (sigma n.val)) at hnfixed
  change 5 * Nat.card (Function.fixedPoints (sigma n.val)) ≤
    Nat.card (Function.fixedPoints n.val.val.val) at hbound
  omega

end FiveTransitive.Degree79FiveLargeSevenFromSupport

end CFSG
