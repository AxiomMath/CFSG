module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_1_b
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H6_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (2) -/

public theorem claim_2
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
    ∀ omega a : G, omega ∈ Q → omega ∉ Q0 → a ∈ K →
      f (omega * rightConjugateElem s a) =
        rightConjugateElem (f (f omega * rightConjugateElem s a⁻¹)) (a⁻¹ ^ 2) *
          rightConjugateElem s a⁻¹ := by
  intro omega a homega homega0 ha
  have hsec2 := hsection3.1
  have hs_involution := hsection3.s_involution
  have hsQ : s ∈ Q :=
    hsec2.Q0_le_Q ((hsec2.Q0_def s).2 (Or.inr ⟨hsection3.s_mem_H, hs_involution⟩))
  have haD : a ∈ D := hsec2.K_le_D ha
  have haH : a ∈ H := PFchapter4section1.rankOneSplit_D_le_M hD_eq haD
  have hyQ : rightConjugateElem s a ∈ Q :=
    PFchapter4section1.h6_rightConjugateElem_mem_Q_of_mem_M
      (PFchapter4section1.rankOneSplit_Q_le_M hQ_sup_D) hQ_normal_in_H hsQ haH
  have hy_involution : IsInvolution (rightConjugateElem s a) :=
    isInvolution_rightConjugateElem hs_involution
  have hyH : rightConjugateElem s a ∈ H := by
    exact H.mul_mem (H.mul_mem (H.inv_mem haH) hsection3.s_mem_H) haH
  have hyQ0 : rightConjugateElem s a ∈ Q0 :=
    (hsec2.Q0_def _).2 (Or.inr ⟨hyH, hy_involution⟩)
  have homega_ne_one : omega ≠ 1 := fun homega_one => homega0 (homega_one ▸ Q0.one_mem)
  have hprod_ne_one : omega * rightConjugateElem s a ≠ 1 := by
    intro hprod
    apply homega0
    have homega_eq : omega = (rightConjugateElem s a)⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    rw [homega_eq, hy_involution.inv_eq_self]
    exact hyQ0
  have hfg := claim_1_a H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
    hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq a ha
  have hh := claim_1_b H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
    hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq a ha
  have hat : rightConjugateElem a t = a⁻¹ := ((hsec2.K_def a).mp ha).2
  have hconj_pow : rightConjugateElem (a ^ 2) t = a⁻¹ ^ 2 := by
    calc
      rightConjugateElem (a ^ 2) t = (rightConjugateElem a t) ^ 2 := by
        simp [rightConjugateElem, pow_two, mul_assoc]
      _ = a⁻¹ ^ 2 := by rw [hat]
  have hH6 := PFchapter4section1.claim_H6_b H Q D t f g h
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
    hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq omega
    (rightConjugateElem s a) homega hyQ homega_ne_one hy_involution.ne_one hprod_ne_one
  calc
    f (omega * rightConjugateElem s a) =
        rightConjugateElem
            (f (f omega * g (rightConjugateElem s a)))
            (rightConjugateElem (h (rightConjugateElem s a)) t) *
          f (rightConjugateElem s a) := hH6
    _ = rightConjugateElem (f (f omega * rightConjugateElem s a⁻¹)) (a⁻¹ ^ 2) *
          rightConjugateElem s a⁻¹ := by rw [hfg.2, hh, hconj_pow, hfg.1]

end PFchapter4section2
end CFSG.BenderSuzuki

