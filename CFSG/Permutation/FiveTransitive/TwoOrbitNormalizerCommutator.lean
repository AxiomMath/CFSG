module

public import CFSG.Permutation.FiveTransitive.TwoFixedNormalizerCommutator
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFixedJoin
public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount

public section

namespace CFSG

namespace FiveTransitive.TwoOrbitNormalizerCommutator

open MulAction NormalizerFixedComplement

theorem fixes_orbits
    {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (x : Normalizer Q)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
    ∀ (a : Subgroup.normalizer (R : Set (Normalizer Q))),
      a ∈ commutator (Subgroup.normalizer (R : Set (Normalizer Q))) →
      ∀ O : orbitRel.Quotient (Inside Q) (Domain (X := X) Q),
        NormalizerSevenOrbitCount.orbitPerm (X := X) Q x O = O →
        NormalizerSevenOrbitCount.orbitPerm (X := X) Q a.val O = O := by
  let : (Inside Q).Normal := Subgroup.normal_subgroupOf_of_le_normalizer le_rfl
  let _ := NormalizerOrbitHom.normalAction (Y := Domain (X := X) Q) (Inside Q)
  let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
  have hfix : fixedPoints R (orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) =
      Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x) :=
    NormalizerOrbitFixedJoin.fixed_join_normal (Y := Domain (X := X) Q) (Inside Q) x
  have hcard : Nat.card
      (fixedPoints R (orbitRel.Quotient (Inside Q) (Domain (X := X) Q))) ≤ 2 := by
    rw [hfix, horbits]
  dsimp only
  intro a ha O hO
  have hmem : O ∈ fixedPoints R (orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) := by
    rw [hfix]
    exact hO
  exact TwoFixedNormalizerCommutator.fixes R hcard a ha O hmem

end FiveTransitive.TwoOrbitNormalizerCommutator

end CFSG
