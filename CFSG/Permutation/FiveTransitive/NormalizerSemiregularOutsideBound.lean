module

public import CFSG.Permutation.FiveTransitive.SemiregularOutsideOrbitBound
public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount

public section

namespace CFSG

namespace FiveTransitive.NormalizerSemiregularOutsideBound

open MulAction NormalizerFixedComplement

theorem fixed_orbits_le_two
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 2)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (B : Subgroup (Normalizer Q)) (hQB : Inside Q ≤ B)
    (E : Set X) (hE : E.ncard ≤ 4)
    (hsemi : ∀ (b : B) (z : X), z ∉ fixedPoints Q X → z ∉ E →
      b.val.val • z = z → b = 1)
    (u : Normalizer Q) (huB : u ∈ B) (huQ : u.val ∉ Q) :
    Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q u)) ≤ 2 := by
  let D := Domain (X := X) Q
  let T : Set D := {z | z.val ∈ E}
  let f : T → E := fun z => ⟨z.val.val, z.property⟩
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : E => z.val) he
  have hT : T.ncard ≤ 4 := by
    have h := Nat.card_le_card_of_injective f hf
    rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at h
    exact h.trans hE
  have hI : Nat.card (Inside Q) = 2 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  apply SemiregularOutsideOrbitBound.fixed_orbits_le_two (Inside Q) B hQB hI
    (free_inside Q hfree) T hT ?_ (NormalizerSevenOrbitCount.lift Q u) huB huQ
  intro b z hz hfix
  exact hsemi b z.val z.property hz (congrArg Subtype.val hfix)

end FiveTransitive.NormalizerSemiregularOutsideBound

end CFSG
