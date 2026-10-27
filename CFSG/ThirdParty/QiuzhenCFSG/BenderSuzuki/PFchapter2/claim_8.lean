module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_10

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3

universe u v

/-!
# Peterfalvi, Part II, Chapter II, Claim (8)
-/

/-- Source interface for the fixed-field calculation in Claim (8).
The surrounding reduction to a commutative near-field is proved below. -/
private theorem chapter2_claim8_fixed_field
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hQ1 : Q1 ≠ ⊥)
    (he : Nat.card Sigma ≠ 1) :
    Nat.Prime (Nat.card Sigma) ∧
      (Nat.card (nearFieldStar Q P) + 1 = 3 ^ Nat.card Sigma ∨
        Nat.card (nearFieldStar Q P) + 1 = 5 ^ Nat.card Sigma ∨
        Nat.card (nearFieldStar Q P) + 1 = 9 ^ Nat.card Sigma) := by
  have hStarComm : IsMulCommutative ↥(nearFieldStar Q P) := by
    by_contra hnotcomm
    change ¬ IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (P : Set G)) at hnotcomm
    exact hQ1 (claim_5 H D Q K V W Q0 S Q1 P t s p hch hnotcomm).2.1
  exact
    chapter2_fixed_field_orders_of_Q1_ne_bot
      H D Q K V W Q0 S Q1 P Sigma t s p hch hind hSigma hStarComm he

public theorem claim_8
    {G : Type u} {Ω : Type v} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hind :
      ∀ (L : Type u) [Group L] [Finite L],
        ∀ (ΩL : Type v) [MulAction L ΩL] [Finite ΩL]
          (HL DL QL : Subgroup L) (tL : L),
          Nat.card L < Nat.card G →
            HypothesisA L ΩL HL DL QL tL →
              suzukiConclusion L ΩL)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hQ1 : Q1 ≠ ⊥)
    (he : Nat.card Sigma ≠ 1) :
    IsMulCommutative ↥(nearFieldStar Q P) ∧ Nat.Prime (Nat.card Sigma) ∧
      ∃ e : ℕ, e = Nat.card Sigma ∧
        (Nat.card (nearFieldStar Q P) + 1 = 3 ^ e ∨
          Nat.card (nearFieldStar Q P) + 1 = 5 ^ e ∨
          Nat.card (nearFieldStar Q P) + 1 = 9 ^ e) := by
  have hStarComm : IsMulCommutative ↥(nearFieldStar Q P) := by
    by_contra hnotcomm
    change ¬ IsMulCommutative ↥(Q ⊓ Subgroup.centralizer (P : Set G)) at hnotcomm
    exact hQ1 (claim_5 H D Q K V W Q0 S Q1 P t s p hch hnotcomm).2.1
  rcases
    chapter2_claim8_fixed_field
      H D Q K V W Q0 S Q1 P Sigma t s p hch hind hSigma hQ1 he with
    ⟨hSigma_prime, hfield_orders⟩
  exact ⟨hStarComm, hSigma_prime, ⟨Nat.card Sigma, rfl, hfield_orders⟩⟩

end PFchapter2
end CFSG.BenderSuzuki


