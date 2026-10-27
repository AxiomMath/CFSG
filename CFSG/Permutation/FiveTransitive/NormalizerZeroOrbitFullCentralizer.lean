module

public import CFSG.Permutation.FiveTransitive.NormalizerZeroOrbitCyclic
public import CFSG.Permutation.FiveTransitive.CyclicFixedNormalizerAlternating
public import CFSG.Permutation.FiveTransitive.AlternatingOddFullImage

public section

namespace CFSG

namespace FiveTransitive.NormalizerZeroOrbitFullCentralizer

open MulAction FixedNormalizerAction

theorem image_eq_top
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G)
    [Fintype (Fixed (X := X) Q)] [DecidableEq (Fixed (X := X) Q)]
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (himage : Image (X := X) Q = ⊤)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (x : Normalizer Q) (hx : x.val ∈ A)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (heven : (toPerm x.val : Equiv.Perm X).sign = 1)
    (hzero : Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 0) :
    ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
      (toPermHom (Normalizer Q) (Fixed (X := X) Q)) = ⊤ := by
  obtain ⟨hcyclic, hcomm⟩ := NormalizerZeroOrbitCyclic.cyclic_and_commute
    Q S hS A hQA hA hseven hfree x hx hlocal heven hzero
  have hseven' : Nat.card (Fixed (X := X) Q) = 7 := by
    rw [Nat.card_coe_set_eq, fixed_eq Q, ← Nat.card_coe_set_eq]
    exact hseven
  have hAlt := CyclicFixedNormalizerAlternating.seven_alternating_le_centralizer_image
    Q hcyclic hseven' himage
  have hxC : x.val ∈ Subgroup.centralizer (Q : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (hcomm ⟨q, hq⟩).symm.eq
  have hxImage : toPermHom (Normalizer Q) (Fixed (X := X) Q) x ∈
      ((Subgroup.centralizer (Q : Set G)).subgroupOf (Normalizer Q)).map
        (toPermHom (Normalizer Q) (Fixed (X := X) Q)) :=
    ⟨x, hxC, rfl⟩
  have hodd : (toPerm x : Equiv.Perm (Fixed (X := X) Q)).sign = -1 :=
    (SevenFivePermutationSquare.isSwap_and_square hseven'
      (toPerm x : Equiv.Perm (Fixed (X := X) Q))
      ((FixedNormalizerLocalCard.fixed_card Q x).trans hlocal)).1.sign_eq
  exact AlternatingOddFullImage.eq_top _ hAlt _ hxImage hodd

end FiveTransitive.NormalizerZeroOrbitFullCentralizer

end CFSG
