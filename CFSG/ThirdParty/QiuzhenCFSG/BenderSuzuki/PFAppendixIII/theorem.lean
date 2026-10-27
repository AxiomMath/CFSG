module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1d
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1e_isomorphic_summands
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1e_scalar_coordinates

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi Appendix III, Higman's theorem

This is the unnumbered theorem following Definitions 1-3 in Appendix III.
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixIII

open External.Higman

universe u

/-- Appendix III, Higman theorem, part (a). -/
public theorem higmanTheorem_involutions_center
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P) :
    involutions P = {z : P | z ∈ Subgroup.center P ∧ z ≠ 1} ∧
      ∀ z : Subgroup.center P, z ^ 2 = 1 :=
  theorem1_involutions_center hP

/-- Appendix III, Higman theorem, part (b). -/
public theorem higmanTheorem_center_quotient_orders_and_exponent
    {P : Type u} [Group P] (hP : IsSuzukiTwoGroup P) :
    let q := Nat.card (Subgroup.center P)
    IsMulCommutative (P ⧸ Subgroup.center P) ∧
    (∀ x : P ⧸ Subgroup.center P, x ^ 2 = 1) ∧
    (Nat.card (P ⧸ Subgroup.center P) = q ∨
      Nat.card (P ⧸ Subgroup.center P) = q ^ 2) ∧
    (Nat.card P = q ^ 2 ∨ Nat.card P = q ^ 3) ∧
    ∀ x : P, x ^ 4 = 1 :=
  theorem1_center_quotient_orders_and_exponent hP

/-- Appendix III, Higman theorem, part (c). -/
public theorem higmanTheorem_order_center_sq_typeA
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
          ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) :=
  theorem1_order_center_sq_typeA_coordinates
    hP hKcyclic hKfaithful hKregular hcard

/-- Appendix III, Higman theorem, part (d). -/
public theorem higmanTheorem_order_center_cube_two_summands
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hcard : Nat.card P = Nat.card (Subgroup.center P) ^ 3) :
    ∃ (quotientAction : MulDistribMulAction K (P ⧸ Subgroup.center P))
        (U V : Subgroup (P ⧸ Subgroup.center P)),
      (∀ k : K, ∀ p : P,
        @SMul.smul K (P ⧸ Subgroup.center P) quotientAction.toSMul k
            (QuotientGroup.mk' (Subgroup.center P) p) =
          QuotientGroup.mk' (Subgroup.center P) (k • p)) ∧
      IsXInvariantSubgroup K U ∧ IsXInvariantSubgroup K V ∧
      Nat.card U = Nat.card (Subgroup.center P) ∧
      Nat.card V = Nat.card (Subgroup.center P) ∧
      U ⊓ V = ⊥ ∧ U ⊔ V = ⊤ :=
  theorem1_order_center_cube_two_summands
    hP hKcyclic hKfaithful hKregular hcard


/-- Appendix III, Higman theorem, part (e): scalar coordinates for the
actual cyclic actor, derived from the explicit isomorphic-summand witness. -/
public theorem higmanTheorem_isomorphic_summands_scalar_coordinates
    {K P : Type u} [Group K] [Group P] [MulDistribMulAction K P]
    (hP : IsSuzukiTwoGroup P)
    (hKcyclic : IsCyclic K) (hKfaithful : FaithfulSMul K P)
    (hKregular : ActionRegularOn K P (involutions P))
    (hIso : External.Higman.Theorem1IsomorphicSummands K P) :
    ∃ (n : ℕ) (_ : n ≠ 0)
        (theta : BinaryGaloisField n ≃+* BinaryGaloisField n)
        (eK : K ≃* (BinaryGaloisField n)ˣ)
        (eQ : (P ⧸ Subgroup.center P) ≃*
          Multiplicative (BinaryGaloisField n × BinaryGaloisField n))
        (eZ : Subgroup.center P ≃*
          Multiplicative (BinaryGaloisField n)),
      (∃ r : ℕ, Odd r ∧ 0 < r ∧
        ∀ x : BinaryGaloisField n, theta^[r] x = x) ∧
      (∀ k : K, ∀ p : P,
        (eQ (QuotientGroup.mk' (Subgroup.center P) (k • p))).toAdd =
          ((eK k : BinaryGaloisField n) *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.1,
            (eK k : BinaryGaloisField n) *
              (eQ (QuotientGroup.mk' (Subgroup.center P) p)).toAdd.2)) ∧
      ∀ k : K, ∀ z : BinaryGaloisField n,
        k • ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) =
          ((eZ.symm (Multiplicative.ofAdd
            ((eK k : BinaryGaloisField n) *
              theta (eK k : BinaryGaloisField n) * z)) :
                Subgroup.center P) : P) :=
  theorem1_isomorphic_summands_scalar_coordinates
    hP hKcyclic hKfaithful hKregular hIso

end PFAppendixIII
end CFSG.BenderSuzuki
