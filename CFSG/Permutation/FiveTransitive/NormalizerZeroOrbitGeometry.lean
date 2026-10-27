module

public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount

public section

namespace CFSG

namespace FiveTransitive.NormalizerZeroOrbitGeometry

open MulAction NormalizerFixedComplement

private theorem not_mem_orbit
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (x : Normalizer Q)
    (hzero : Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 0)
    (z : Domain (X := X) Q) : x.val • z.val ∉ orbit Q z.val := by
  intro hx
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp hx
  have hf : NormalizerSevenOrbitCount.orbitPerm (X := X) Q x (Quotient.mk'' z) =
      Quotient.mk'' z := by
    change Quotient.mk'' (x • z) = Quotient.mk'' z
    apply Quotient.sound
    exact mem_orbit_iff.mpr ⟨(⟨⟨q.val, Q.le_normalizer q.property⟩, q.property⟩ : Inside Q), Subtype.ext hq⟩
  let _ : Nonempty (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) :=
    ⟨⟨Quotient.mk'' z, hf⟩⟩
  have hpos : 0 < Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) := Nat.card_pos
  omega

private theorem smul_mem_fixed_orbit
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (x y : Normalizer Q) (hcomm : Commute x.val y.val)
    (z : Domain (X := X) Q)
    (horbit : fixedBy X y.val \ fixedPoints Q X = orbit Q z.val) :
    x.val • z.val ∈ orbit Q z.val := by
  have hyz : y.val • z.val = z.val :=
    (horbit.symm ▸ mem_orbit_self (α := X) z.val).1
  rw [← horbit]
  refine ⟨?_, (x • z).property⟩
  change y.val • (x.val • z.val) = x.val • z.val
  rw [← mul_smul, ← hcomm.eq, mul_smul, hyz]

theorem not_commute
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (x y : Normalizer Q)
    (hzero : Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 0)
    (z : Domain (X := X) Q)
    (horbit : fixedBy X y.val \ fixedPoints Q X = orbit Q z.val) :
    ¬ Commute x.val y.val := by
  intro hcomm
  exact not_mem_orbit Q x hzero z (smul_mem_fixed_orbit Q x y hcomm z horbit)

theorem exists_fixed_representative
    {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (x y : Normalizer Q) (hcomm : Commute x.val y.val)
    (z : Domain (X := X) Q)
    (horbit : fixedBy X y.val \ fixedPoints Q X = orbit Q z.val) :
    ∃ q : Inside Q, (q.val * x) • z = z := by
  obtain ⟨q, hq⟩ := mem_orbit_iff.mp (smul_mem_fixed_orbit Q x y hcomm z horbit)
  refine ⟨⟨⟨q.val⁻¹, Q.le_normalizer (Q.inv_mem q.property)⟩, Q.inv_mem q.property⟩, ?_⟩
  apply Subtype.ext
  change (q.val⁻¹ * x.val) • z.val = z.val
  change q.val • z.val = x.val • z.val at hq
  rw [mul_smul, ← hq, inv_smul_smul]

end FiveTransitive.NormalizerZeroOrbitGeometry

end CFSG
