module

public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount

public section

namespace CFSG

namespace FiveTransitive.NormalizerOrbitCoset

open MulAction NormalizerFixedComplement

theorem orbitPerm_mul
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (q : Inside Q) (x : Normalizer Q) :
    NormalizerSevenOrbitCount.orbitPerm (X := X) Q ((q : Normalizer Q) * x) =
      NormalizerSevenOrbitCount.orbitPerm (X := X) Q x := by
  apply Equiv.ext
  intro O
  refine Quotient.inductionOn O ?_
  intro y
  change Quotient.mk'' (((q : Normalizer Q) * x) • y) = Quotient.mk'' (x • y)
  apply Quotient.sound
  apply mem_orbit_iff.mpr
  refine ⟨q, ?_⟩
  change (q : Normalizer Q) • (x • y) = ((q : Normalizer Q) * x) • y
  exact (mul_smul _ _ _).symm

theorem exists_fixed_representative
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (x : Normalizer Q)
    (hpos : 0 < Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x))) :
    ∃ (q : Inside Q) (z : Domain (X := X) Q), ((q : Normalizer Q) * x) • z = z := by
  obtain ⟨O⟩ := (Nat.card_pos_iff.mp hpos).1
  obtain ⟨z, hz⟩ := Quotient.exists_rep O.val
  have hfixed := O.property
  rw [← hz] at hfixed
  obtain ⟨q, hq⟩ := (NormalizerOrbitPermutation.fixed_iff_transporter
    (Inside Q) (NormalizerSevenOrbitCount.lift Q x) z).mp hfixed
  exact ⟨q, z, hq⟩

end FiveTransitive.NormalizerOrbitCoset

end CFSG
