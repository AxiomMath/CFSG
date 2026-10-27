module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_1_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (1)(b) -/

public theorem claim_1_b
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G) (f g h : G → G)
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
    (hcanonical_eq : ∀ x : G, x ∈ Q → x ≠ 1 → t * x * t = g x * h x * t * f x) :
    ∀ a : G, a ∈ K → h (rightConjugateElem s a) = a ^ 2 := by
  intro a ha
  have _ := hC1
  have hsec2 := hsection3.1
  have hs_involution := hsection3.s_involution
  have hsQ : s ∈ Q :=
    hsec2.Q0_le_Q ((hsec2.Q0_def s).2 (Or.inr ⟨hsection3.s_mem_H, hs_involution⟩))
  have hbase := claim_1_base_values H D Q t s f g h hsQ hs_involution
    hC2.st_order_three ht_involution hD_eq hQ_disjoint_D hQ_sup_D
    hf_mem hg_mem hh_mem hcanonical_eq
  have haD : a ∈ D := hsec2.K_le_D ha
  have hat : rightConjugateElem a t = a⁻¹ := ((hsec2.K_def a).mp ha).2
  have hcompare :=
    PFchapter4section1.canonical_compare_rightConjugate_D H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
      hsQ hs_involution.ne_one haD
  calc
    h (rightConjugateElem s a) =
        (rightConjugateElem a t)⁻¹ * h s * a := hcompare.2.1
    _ = a ^ 2 := by rw [hat, hbase.2.1]; simp [pow_two]

end PFchapter4section2
end CFSG.BenderSuzuki

