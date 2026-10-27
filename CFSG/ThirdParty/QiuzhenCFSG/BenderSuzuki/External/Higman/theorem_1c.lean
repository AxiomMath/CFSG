module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_11

namespace CFSG
end CFSG
open CFSG

/-!
# Higman's classification theorem for Suzuki 2-groups: extracted branch
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u
/-- Theorem 1(c), including the action coordinates quoted in Peterfalvi
Appendix III. -/
public theorem theorem1_order_center_sq_typeA_coordinates
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 2) :
    ∃ (n : ℕ) (_ : n ≠ 0)
        (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
        (pairLift : BinaryGaloisField n → BinaryGaloisField n → P)
        (cocycle : BinaryGaloisField n → BinaryGaloisField n → BinaryGaloisField n)
        (eK : K ≃* (BinaryGaloisField n)ˣ)
        (eQ : (P ⧸ Subgroup.center P) ≃*
          Multiplicative (BinaryGaloisField n))
        (eZ : Subgroup.center P ≃*
          Multiplicative (BinaryGaloisField n)),
      (∃ r : ℕ, Odd r ∧ 0 < r ∧
        ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
      (∃ x : BinaryGaloisField n, theta x ≠ x) ∧
      (∀ a b c : BinaryGaloisField n,
        cocycle (a + b) c = cocycle a c + cocycle b c) ∧
      (∀ a b c : BinaryGaloisField n,
        cocycle a (b + c) = cocycle a b + cocycle a c) ∧
      (∀ a : BinaryGaloisField n, cocycle a a = a * theta a) ∧
      (∀ a z : BinaryGaloisField n, pairLift a z ∈ (⊤ : Subgroup P)) ∧
      pairLift 0 0 = 1 ∧
      (∀ x : P, ∃ a z : BinaryGaloisField n, x = pairLift a z) ∧
      (∀ a z b w : BinaryGaloisField n,
        pairLift a z = pairLift b w → a = b ∧ z = w) ∧
      (∀ a z b w : BinaryGaloisField n,
        pairLift a z * pairLift b w =
          pairLift (a + b) (z + w + cocycle a b)) ∧
      Nat.card (Subgroup.center P) = 2 ^ n ∧
      (∀ k : K, ∀ p : P,
        (eQ (QuotientGroup.mk' (Subgroup.center P) (k • p))).toAdd =
          (eK k : BinaryGaloisField n) *
            (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd) ∧
      (∀ k : K, ∀ z : BinaryGaloisField n,
        k • ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) =
          ((eZ.symm (Multiplicative.ofAdd
            ((eK k : BinaryGaloisField n) * theta (eK k : BinaryGaloisField n) * z)) :
              Subgroup.center P) : P)) ∧
      (∀ a z : BinaryGaloisField n,
        (eQ (QuotientGroup.mk' (Subgroup.center P) (pairLift a z))).toAdd = a) ∧
      ∀ z : BinaryGaloisField n,
        pairLift 0 z =
          ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) := by
  have hLen2 : OmegaLength K P 2 := by
    exact omegaLength_two_of_card_center_sq
      hP hKcyclic hKfaithful hKregular hcard
  exact lemma11_length_two_typeA_actor_coordinates
    hP hKcyclic hKfaithful hKregular hLen2
end Higman
end External
end CFSG.BenderSuzuki
