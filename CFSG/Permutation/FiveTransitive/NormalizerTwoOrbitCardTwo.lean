module

public import CFSG.Permutation.FiveTransitive.NormalizerTwoOrbitCyclic
public import CFSG.Permutation.FiveTransitive.SevenNormalizerSecondDerivedLift
public import CFSG.Permutation.FiveTransitive.CyclicTwoOrbitSecondDerived

public section

namespace CFSG

namespace FiveTransitive.NormalizerTwoOrbitCardTwo

open MulAction FixedNormalizerAction

theorem cyclic_and_card_eq_two
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (himage : Image (X := X) Q = ⊤)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (horbits : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 2) :
    IsCyclic Q ∧ Nat.card Q = 2 := by
  have hc := NormalizerTwoOrbitCyclic.isCyclic_of_two_fixed_orbits
    heven hdegree hmax Q A hQA hA hQ hne hseven hfree x hx hxQ hlocal horbits
  let _ : IsCyclic Q := hc
  have hseven' : Nat.card (Fixed (X := X) Q) = 7 := by
    simpa only [fixed_eq Q] using hseven
  obtain ⟨y, hy, htwo, hyorder, hyfixed⟩ := SevenNormalizerSecondDerivedLift.exists_two_lift
    Q hseven' S hS A hA hQA x hx himage hlocal
  have hyQ := FixedNormalizerLocalCard.not_mem_of_local_order_two Q y.val.val hyorder
  have hyne : y.val.val.val ≠ 1 := by
    intro he
    exact hyQ (he ▸ Q.one_mem)
  have hfixed : (fixedBy X y.val.val.val ∩ fixedPoints Q X).ncard = 3 :=
    (FixedNormalizerLocalCard.fixed_card Q y.val.val).symm.trans hyfixed
  have hle := CyclicTwoOrbitSecondDerived.card_le_two hmax Q hfree x horbits
    y hy htwo hyne hfixed.ge
  have hgt : ¬ Nat.card Q ≤ 1 := fun h => hne ((Subgroup.card_le_one_iff_eq_bot Q).mp h)
  exact ⟨hc, by omega⟩

end FiveTransitive.NormalizerTwoOrbitCardTwo

end CFSG
