module

public import CFSG.Permutation.FiveTransitive.FreeTwoGroupOddCyclic
public import CFSG.Permutation.FiveTransitive.ZeroOrbitGeneratedFree
public import CFSG.Permutation.FiveTransitive.FixedComplementSign
public import CFSG.Permutation.FiveTransitive.NormalizerLocalSquareMem
public import CFSG.Permutation.FiveTransitive.NormalizerSevenOrbitCount
public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard

public section

namespace CFSG

namespace FiveTransitive.NormalizerZeroOrbitCyclic

open MulAction NormalizerFixedComplement

theorem cyclic_and_commute
    {G X : Type*} [Group G] [Finite G] [Fintype X] [DecidableEq X] [MulAction G X]
    (Q : Subgroup G)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (A : Subgroup G) (hQA : Q ≤ A) (hA : IsPGroup 2 A)
    (hseven : Nat.card (fixedPoints Q X) = 7)
    (hfree : ∀ (q : Q) (t : X), t ∉ fixedPoints Q X → q • t = t → q = 1)
    (x : Normalizer Q) (hx : x.val ∈ A)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5)
    (heven : (toPerm x.val : Equiv.Perm X).sign = 1)
    (hzero : Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) = 0) :
    IsCyclic Q ∧ ∀ q : Q, Commute x.val q.val := by
  classical
  let _ := Fintype.ofFinite (FixedNormalizerAction.Fixed (X := X) Q)
  let _ := Fintype.ofFinite (Domain (X := X) Q)
  let I := Inside Q
  let R := I ⊔ Subgroup.zpowers x
  have hseven' : Nat.card (FixedNormalizerAction.Fixed (X := X) Q) = 7 := by
    rw [Nat.card_coe_set_eq, FixedNormalizerAction.fixed_eq Q, ← Nat.card_coe_set_eq]
    exact hseven
  have hlocalOdd : (toPerm x : Equiv.Perm (FixedNormalizerAction.Fixed (X := X) Q)).sign = -1 :=
    (SevenFivePermutationSquare.isSwap_and_square hseven'
      (toPerm x : Equiv.Perm (FixedNormalizerAction.Fixed (X := X) Q))
      ((FixedNormalizerLocalCard.fixed_card Q x).trans hlocal)).1.sign_eq
  have hodd := FixedComplementSign.complement_odd Q x heven hlocalOdd
  have hx2 : x ^ 2 ∈ I := NormalizerLocalSquareMem.square_mem Q S hS A hA hseven x hx hlocal
  have hp : IsPGroup 2 R := NormalizerLocalSquareMem.generated_pgroup Q A hQA hA x hx
  have hno : ∀ t : Domain (X := X) Q, x • t ∉ orbit I t := by
    intro t ht
    have hf : NormalizerSevenOrbitCount.orbitPerm (X := X) Q x (Quotient.mk'' t) =
        Quotient.mk'' t := by
      change Quotient.mk'' (x • t) = Quotient.mk'' t
      exact Quotient.sound ht
    let _ : Nonempty (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) :=
      ⟨⟨Quotient.mk'' t, hf⟩⟩
    have hc : 0 < Nat.card (Function.fixedPoints (NormalizerSevenOrbitCount.orbitPerm (X := X) Q x)) := Nat.card_pos
    omega
  have hRfree : ∀ (r : R) (t : Domain (X := X) Q), r • t = t → r = 1 :=
    ZeroOrbitGeneratedFree.generated_free I x hx2 (free_inside Q hfree) hno
  let xR : R := ⟨x, (le_sup_right : Subgroup.zpowers x ≤ R) (Subgroup.mem_zpowers x)⟩
  obtain ⟨_, hcyc⟩ := FreeTwoGroupOddCyclic.generates hp hRfree xR hodd
  let _ : IsCyclic R := hcyc
  let _ : IsCyclic I := Subgroup.isCyclic_of_le (show I ≤ R from le_sup_left)
  have hQcyc : IsCyclic Q := isCyclic_of_injective
    (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).symm.toMonoidHom
    (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).symm.injective
  refine ⟨hQcyc, ?_⟩
  intro q
  let _ : CommGroup R := IsCyclic.commGroup
  let qR : R := ⟨⟨q.val, Q.le_normalizer q.property⟩, (le_sup_left : I ≤ R) q.property⟩
  have he : xR * qR = qR * xR := mul_comm _ _
  exact congrArg (fun r : R => r.val.val) he

end FiveTransitive.NormalizerZeroOrbitCyclic

end CFSG
