module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma113Core

namespace CFSG
end CFSG
open CFSG

/-!
# Section 11, Lemma 11.3: source-boundary interfaces

This module isolates the earlier-book character-theoretic input used in
Lemma 11.3.  The implication-shaped `[Is1; 3.8, 3.9]` callback supplies only
the proper normal character kernel and centrality modulo that kernel.  It
does not contain the conclusion of Lemma 11.3.  The former `[II1; 4.7]`
numerical step is proved internally in `Section11Lemma113Arithmetic`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1

universe u

/-- The group-theoretic consequence of the character kernel constructed in
`[Is1; 3.8, 3.9]`.  The last field says that every element of the specified
involution class is central modulo `H`. -/
public structure Is1Lemma38_39Conclusion
    {X : Type u} [Group X]
    (W : Subgroup X) (Z : Set X) : Prop where
  exists_H :
    ∃ H : Subgroup X,
      H < W ∧
        (H.subgroupOf W).Normal ∧
          (∀ z : X, z ∈ Z → ∀ w : X, w ∈ W →
            rightConjugateElem z w * z⁻¹ ∈ H)

/-- Genuine implication-shaped source callback for Burnside's argument
`[Is1; 3.8, 3.9]`: a nonempty prime-power conjugacy class of involutions in
`W` has a proper normal character kernel modulo which that class is central.

The irreducible character itself is intentionally not exposed: Lemma 11.3
uses only its kernel and the displayed quotient-centrality consequence. -/
@[expose] public def Is1Lemma38_39PrimePowerInvolutionClass
    {X : Type u} [Group X] [Finite X] : Prop :=
  ∀ (W : Subgroup X) (Z : Set X) (r n : ℕ),
      r.Prime →
      Z.Nonempty →
      Z ⊆ W →
      (∀ z : X, z ∈ Z → IsInvolution z) →
      (∀ z : X, z ∈ Z → ∀ w : X, w ∈ W →
        rightConjugateElem z w ∈ Z) →
      (∀ x : X, x ∈ Z → ∀ y : X, y ∈ Z →
        ∃ w : X, w ∈ W ∧ y = rightConjugateElem x w) →
      Nat.card Z = r ^ n →
      Is1Lemma38_39Conclusion W Z

/-- The literal statement package of source Lemma 11.3. -/
public structure Lemma113Conclusion
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t) : Prop where
  mersenne_not_prime : ¬ (2 ^ d.choice.p - 1).Prime
  p_ne_three : d.choice.p ≠ 3
  p_ne_five : d.choice.p ≠ 5

/-- The two small-prime consequences in Lemma 11.3 are immediate from the
nonprimality of the associated Mersenne number. -/
public theorem lemma113Conclusion_of_mersenne_not_prime
    {X : Type u} [Group X] [Finite X]
    {M W D E : Subgroup X} {t : X}
    (d : Lemma101Conclusion M W D E (peterfalviV D t) t)
    (hnot : ¬ (2 ^ d.choice.p - 1).Prime) :
    Lemma113Conclusion d := by
  refine ⟨hnot, ?_, ?_⟩
  · intro hp
    apply hnot
    simpa [hp] using (by decide : Nat.Prime 7)
  · intro hp
    apply hnot
    simpa [hp] using (by decide : Nat.Prime 31)

end CFSG.BenderSuzuki
