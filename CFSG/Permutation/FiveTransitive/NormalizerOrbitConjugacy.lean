module

public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitHom

public section

namespace CFSG

namespace FiveTransitive.NormalizerOrbitConjugacy

open MulAction NormalizerFixedComplement

variable {G X : Type*} [Group G] [MulAction G X]

@[expose] def orbitHom (Q : Subgroup G) : Normalizer Q →*
    Equiv.Perm (orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) :=
  (NormalizerOrbitHom.toPermHom (Y := Domain (X := X) Q) (Inside Q)).comp
    { toFun := NormalizerSevenOrbitCount.lift Q
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

theorem fixed_card_conjugate [Finite X] (Q : Subgroup G) (c u : Normalizer Q) :
    Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q (c * u * c⁻¹))) =
    Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) := by
  classical
  let _ : Fintype (orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) := Fintype.ofFinite _
  change Nat.card (Function.fixedPoints (orbitHom (X := X) Q (c * u * c⁻¹))) =
    Nat.card (Function.fixedPoints (orbitHom (X := X) Q u))
  rw [map_mul, map_mul, map_inv]
  simp only [Nat.card_eq_fintype_card, Equiv.Perm.card_fixedPoints, Equiv.Perm.cycleType_conj]

theorem conjugate_not_mem (Q : Subgroup G) (c u : Normalizer Q) (hu : u.val ∉ Q) :
    (c * u * c⁻¹).val ∉ Q := by
  intro h
  exact hu ((Subgroup.mem_normalizer_iff.mp c.property u.val).mpr h)

end FiveTransitive.NormalizerOrbitConjugacy

end CFSG
