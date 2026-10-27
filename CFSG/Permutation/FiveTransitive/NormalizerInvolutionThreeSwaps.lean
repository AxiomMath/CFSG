module

public import CFSG.Permutation.FiveTransitive.SevenInvolutionThreeSwaps
public import CFSG.Permutation.FiveTransitive.ConjugateIntoPreimageSylow
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitConjugacy
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.NormalizerInvolutionThreeSwaps

open MulAction FixedNormalizerAction

private theorem exists_conjugate
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (himage : Image (X := X) Q = ⊤) (e : Fin 6 ↪ Fixed (X := X) Q)
    (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (u : Normalizer Q) (hu : orderOf u.val = 2) :
    ∃ c : Normalizer Q,
      c * u * c⁻¹ ∈ SylowPreimageNormalizer.ambient
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P ∧
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q (c * u * c⁻¹))) =
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) ∧
      orderOf (c * u * c⁻¹).val = 2 ∧
      (u.val ∉ Q → (c * u * c⁻¹).val ∉ Q) := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hf : Function.Surjective f := MonoidHom.range_eq_top.mp himage
  have hu2 : u ^ 2 = 1 := by
    apply Subtype.ext
    change u.val ^ 2 = 1
    simpa only [hu] using pow_orderOf_eq_one u.val
  have hlocal : ∃ d : Equiv.Perm (Fixed (X := X) Q),
      d * f u * d⁻¹ ∈ ThreeSwapTwoGroup.subgroup e :=
    SevenInvolutionThreeSwaps.exists_conjugate
      (by simpa only [Nat.card_eq_fintype_card] using hseven) e (f u)
      (by rw [← map_pow, hu2, map_one])
  obtain ⟨c, hc⟩ := ConjugateIntoPreimageSylow.exists_conjugate f hf
    (ThreeSwapTwoGroup.subgroup e) P u hu2 hlocal
  have horder : orderOf (c * u * c⁻¹).val = 2 :=
    (orderOf_injective (MulAut.conj c.val).toMonoidHom (MulAut.conj c.val).injective u.val).trans hu
  exact ⟨c, hc, NormalizerOrbitConjugacy.fixed_card_conjugate Q c u,
    horder, NormalizerOrbitConjugacy.conjugate_not_mem Q c u⟩

theorem exists_element
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (himage : Image (X := X) Q = ⊤) (e : Fin 6 ↪ Fixed (X := X) Q)
    (P : Sylow 2 ((ThreeSwapTwoGroup.subgroup e).comap
      (toPermHom (Normalizer Q) (Fixed (X := X) Q))))
    (u : Normalizer Q) (hu : orderOf u.val = 2) (huQ : u.val ∉ Q) :
    ∃ v : SylowPreimageNormalizer.ambient
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)) (ThreeSwapTwoGroup.subgroup e) P,
      orderOf v.val.val = 2 ∧ v.val.val ∉ Q ∧
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q v.val)) =
      Nat.card (Function.fixedPoints
        (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) := by
  obtain ⟨c, hc, hcount, horder, hout⟩ := exists_conjugate Q hseven himage e P u hu
  exact ⟨⟨c * u * c⁻¹, hc⟩, horder, hout huQ, hcount⟩

end FiveTransitive.NormalizerInvolutionThreeSwaps

end CFSG
