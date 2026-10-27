module

public import CFSG.Permutation.FiveTransitive.NormalizerCosetCount
public import CFSG.Permutation.FiveTransitive.NormalizerSevenCosetBound

public section

namespace CFSG

namespace FiveTransitive.NormalizerSevenOrbitCount

open MulAction NormalizerFixedComplement

@[expose] def lift {G : Type*} [Group G] (Q : Subgroup G) (x : Normalizer Q) :
    Subgroup.normalizer (Inside Q : Set (Normalizer Q)) :=
  ⟨x, Subgroup.mem_normalizer_iff.mpr (by
    intro y
    change y.val ∈ Q ↔ x.val * y.val * x.val⁻¹ ∈ Q
    exact Subgroup.mem_normalizer_iff.mp x.property y.val)⟩

@[expose] abbrev orbitPerm {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G) (x : Normalizer Q) :=
  NormalizerOrbitPermutation.orbitPerm (Y := Domain (X := X) Q) (Inside Q) (lift Q x)

theorem fixed_orbits_le_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hbound : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5) :
    Nat.card (Function.fixedPoints (orbitPerm (X := X) Q x)) ≤ 2 := by
  let _ : Fintype (Inside Q) := Fintype.ofFinite _
  exact NormalizerCosetCount.orbit_bound (Inside Q)
    (free_inside Q hfree) (lift Q x) 2
    (NormalizerSevenCosetBound.coset_fixed_le_two hbound Q A hQA hA x hx hxQ hlocal)

theorem saturated_coset_fixed_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hbound : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (horbits : Nat.card (Function.fixedPoints (orbitPerm (X := X) Q x)) = 2) :
    ∀ q : Inside Q,
      Nat.card (fixedBy (Domain (X := X) Q) ((q : Normalizer Q) * x)) = 2 := by
  let _ : Fintype (Inside Q) := Fintype.ofFinite _
  exact NormalizerCosetCount.saturated_fixed_count (Inside Q)
    (free_inside Q hfree) (lift Q x) 2
    (NormalizerSevenCosetBound.coset_fixed_le_two hbound Q A hQA hA x hx hxQ hlocal)
    horbits

end FiveTransitive.NormalizerSevenOrbitCount

end CFSG
