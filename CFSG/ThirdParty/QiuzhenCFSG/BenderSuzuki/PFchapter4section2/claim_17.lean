module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_17_shift

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (17) -/

public theorem claim_17
    {G Ω E : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω] [Field E] [CharP E 2]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
    (m n : ℕ) (zeta alpha beta : E) (theta sigma tau : E → E)
    (omega : E → G) (coordConj : G → E → G) (u v d : ℕ → E)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
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
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r))
    (hC1 : HypothesisC1 G V) (hC2 : HypothesisC2 G S W t s)
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Ω 2)
    (hpoint_stabilizer : ∃ x : Ω, H = MulAction.stabilizer G x)
    (ht_involution : IsInvolution t) (ht_not_mem_H : t ∉ H)
    (hD_eq : D = H ⊓ rightConjugate H t)
    (hQ_normal_in_H : (Q.subgroupOf H).Normal)
    (hQ_disjoint_D : Disjoint Q D) (hQ_sup_D : Q ⊔ D = H)
    (hf_mem : ∀ x : G, x ∈ Q → x ≠ 1 → f x ∈ Q ∧ f x ≠ 1)
    (hg_mem : ∀ x : G, x ∈ Q → x ≠ 1 → g x ∈ Q ∧ g x ≠ 1)
    (hh_mem : ∀ x : G, x ∈ Q → x ≠ 1 → h x ∈ D)
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x)
    (hcoord_zeta_ne_one : zeta ≠ 1) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_v : ∀ i : ℕ, u i ≠ alpha →
      v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hcoord_initial : u 1 = 0 ∧ v 1 = alpha ∧ d 1 = zeta)
    (hseq_zeta_ne_one : zeta ≠ 1) (hseq_alpha_ne_zero : alpha ≠ 0)
    (hseq_beta_ne_zero : beta ≠ 0) (hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hcoord_tau_one : tau 1 = 1)
    (hcoord_tau_mul : ∀ x y : E, tau (x * y) = tau x * tau y)
    (hcoord_denominator_nonzero : ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      beta ^ i + (beta⁻¹) ^ i ≠ 0)
    (hdprod :
      ∀ i : ℕ, 1 ≤ i → i < m - 1 →
        d i * sigma (d i) = ((beta ^ i + (beta⁻¹) ^ i) / alpha) ^ 2)
    (hformula :
      ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
        f (omega (u i)) = coordConj (omega (v i)) (d i)) :
    ∀ i : ℕ, 1 ≤ i → i ≤ m - 1 →
      f (omega (u i)) = coordConj (omega (u i + alpha)) (d i) := by
  have _ := hsection3
  have _ := hC1
  have _ := hC2
  have _ := htwo_transitive
  have _ := hpoint_stabilizer
  have _ := ht_involution
  have _ := ht_not_mem_H
  have _ := hD_eq
  have _ := hQ_normal_in_H
  have _ := hQ_disjoint_D
  have _ := hQ_sup_D
  have _ := hf_mem
  have _ := hg_mem
  have _ := hh_mem
  have _ := hcanonical_eq
  have hseq_closed :
      Section2SequenceClosedData E m zeta alpha beta tau u d :=
    section2SequenceClosedData E m zeta alpha beta tau u d
      hcoord_beta_ne_zero hcoord_recurrence_u hcoord_recurrence_d
      hcoord_beta_characteristic_root
      ⟨hcoord_initial.1, hcoord_initial.2.2⟩ hseq_alpha_ne_zero
      hcoord_tau_one hcoord_tau_mul hcoord_denominator_nonzero
  intro i hi him
  rw [hformula i hi him,
    claim_17_v_eq_shift m n zeta alpha beta theta sigma tau u v d
      hcoord_zeta_ne_one hcoord_beta_ne_zero hcoord_recurrence_u
      hcoord_recurrence_v hcoord_recurrence_d hcoord_beta_characteristic_root
      hcoord_initial hseq_zeta_ne_one hseq_alpha_ne_zero hseq_beta_ne_zero
      hseq_tau_nonzero hseq_zeta_order hseq_recurrence_u hseq_recurrence_d
      hseq_beta_characteristic_root hseq_closed hdprod i hi him]

end PFchapter4section2
end CFSG.BenderSuzuki
