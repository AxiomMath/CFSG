module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitCoset
public import CFSG.Permutation.FiveTransitive.NormalizerCosetInvolutionCount
public import CFSG.Permutation.FiveTransitive.NormalizerEvenCentralizerTwo

public section

namespace CFSG

namespace FiveTransitive.NormalizerOneOrbitRepresentative

open MulAction NormalizerFixedComplement

theorem exists_involution
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (heven : ∀ g : G, Equiv.Perm.sign (toPermHom G X g) = 1)
    (hdegree : Fintype.card X % 4 = 3)
    (hmax : ∀ u : G, orderOf u = 2 → (fixedBy X u).ncard ≤ 7)
    (Q A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hQ : IsPGroup 2 Q) (hne : Q ≠ ⊥)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (z : X), z ∉ fixedPoints Q X → q • z = z → q = 1)
    (x : Normalizer Q) (hx : x.val ∈ A) (hxQ : x.val ∉ Q)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (hpos : 0 < Nat.card (Function.fixedPoints
      (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x))) :
    ∃ q : Inside Q, let v := (q : Normalizer Q) * x
      v.val ∈ A ∧ v.val ∉ Q ∧ orderOf v.val = 2 ∧
      (fixedBy X v.val ∩ fixedPoints Q X).ncard = 5 ∧
      NormalizerSevenOrbitCount.orbitPerm (X := X) Q v =
        NormalizerSevenOrbitCount.orbitPerm (X := X) Q x ∧
      Nat.card ((Subgroup.centralizer ({v.val} : Set G)).subgroupOf Q) = 2 ∧
      (fixedBy X v.val \ fixedPoints Q X).ncard = 2 ∧
      ∃ z : Domain (X := X) Q, v • z = z := by
  obtain ⟨q, z, hz⟩ := NormalizerOrbitCoset.exists_fixed_representative Q x hpos
  let v : Normalizer Q := (q : Normalizer Q) * x
  have hfixpos : Nat.card (fixedBy (Domain (X := X) Q) v) ≠ 0 := by
    let _ : Nonempty (fixedBy (Domain (X := X) Q) v) := ⟨⟨z, hz⟩⟩
    exact Nat.card_pos.ne'
  have horder := ((NormalizerCosetInvolutionCount.fixed_iff_order_two
    heven hdegree hmax Q A hQA hA hseven x hx hxQ hlocal q).1).mp hfixpos
  obtain ⟨hcent, htwo, _⟩ := NormalizerEvenCentralizerTwo.actual_coset
    heven hdegree hmax Q hQ hne hfree x hlocal q horder
  have hvQ : v.val ∉ Q := by
    intro h
    apply hxQ
    have hh := Q.mul_mem (Q.inv_mem q.property) h
    change q.val.val⁻¹ * (q.val.val * x.val) ∈ Q at hh
    simpa only [inv_mul_cancel_left] using hh
  refine ⟨q, A.mul_mem (hQA q.property) hx, hvQ, ?_, ?_,
    NormalizerOrbitCoset.orbitPerm_mul Q q x, hcent, ?_, z, hz⟩
  · exact (orderOf_injective (Normalizer Q).subtype (Normalizer Q).subtype_injective v).trans horder
  · change (fixedBy X (q.val.val * x.val) ∩ fixedPoints Q X).ncard = 5
    rw [TwoGroupCosetFixedBound.coset_fixed_inter Q ⟨q.val.val, q.property⟩ x.val]
    exact hlocal
  · rwa [NormalizerFixedComplement.fixed_card] at htwo

end FiveTransitive.NormalizerOneOrbitRepresentative

end CFSG
