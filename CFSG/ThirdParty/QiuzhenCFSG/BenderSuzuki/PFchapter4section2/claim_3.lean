module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_2
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section2.corollary

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section2

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (3) -/

/-- Every element of `Q0` commutes with `Q`. -/
public theorem Q0_commutes_Q
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s : G)
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
    (hC2 : HypothesisC2 G S W t s) :
    ∀ x : G, x ∈ Q0 → ∀ q : G, q ∈ Q → x * q = q * x := by
  intro x hxQ0 q hqQ
  rcases (hsection3.1.Q0_def x).1 hxQ0 with rfl | ⟨hxH, hxI⟩
  · simp
  have hxS : x ∈ S :=
    PFchapter1section2.corollary_H_involution_mem_S
      H D Q K V W Q0 S Q1 t x hsection3.1 hxH hxI
  have hS_le : S ≤ Subgroup.centralizer ({x} : Set G) := by
    intro z hzS
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwx : w = x := by simpa using hw
    subst w
    exact hC2.S_type_B.commute_of_isInvolution hxS hxI hzS
  have hQ1_le : Q1 ≤ Subgroup.centralizer ({x} : Set G) := by
    intro z hzQ1
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hwx : w = x := by simpa using hw
    subst w
    exact hsection3.1.S_commutes_Q1 x hxS z hzQ1
  have hQ_le : Q ≤ Subgroup.centralizer ({x} : Set G) := by
    have hsup := sup_le hS_le hQ1_le
    rwa [hsection3.1.Q_decomp] at hsup
  exact Subgroup.mem_centralizer_iff.mp (hQ_le hqQ) x (by simp)

public theorem claim_3
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
        rightConjugateElem (f (g omega * rightConjugateElem s a⁻¹))
          (rightConjugateElem (h omega) t) * f omega := by
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
  have hyH : rightConjugateElem s a ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem haH) hsection3.s_mem_H) haH
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
  have hy_comm_omega : rightConjugateElem s a * omega =
      omega * rightConjugateElem s a :=
    Q0_commutes_Q H D Q K V W Q0 S Q1 t s hsection3 hC2 _ hyQ0 omega homega
  have hprod_swap_ne_one : rightConjugateElem s a * omega ≠ 1 := by
    rw [hy_comm_omega]
    exact hprod_ne_one
  have hfg := claim_1_a H D Q K V W Q0 S Q1 t s f g h hsection3 hC1 hC2
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
    hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq a ha
  have ha_invH : a⁻¹ ∈ H := H.inv_mem haH
  have hy_invH : rightConjugateElem s a⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem ha_invH) hsection3.s_mem_H) ha_invH
  have hy_inv_involution : IsInvolution (rightConjugateElem s a⁻¹) :=
    isInvolution_rightConjugateElem hs_involution
  have hy_invQ0 : rightConjugateElem s a⁻¹ ∈ Q0 :=
    (hsec2.Q0_def _).2 (Or.inr ⟨hy_invH, hy_inv_involution⟩)
  have hgomegaQ : g omega ∈ Q := (hg_mem omega homega homega_ne_one).1
  have hy_inv_comm_gomega : rightConjugateElem s a⁻¹ * g omega =
      g omega * rightConjugateElem s a⁻¹ :=
    Q0_commutes_Q H D Q K V W Q0 S Q1 t s hsection3 hC2 _ hy_invQ0
      (g omega) hgomegaQ
  have hH6 := PFchapter4section1.claim_H6_b H Q D t f g h
    htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq hQ_normal_in_H
    hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem hcanonical_eq
    (rightConjugateElem s a) omega hyQ homega hy_involution.ne_one homega_ne_one
    hprod_swap_ne_one
  calc
    f (omega * rightConjugateElem s a) =
        f (rightConjugateElem s a * omega) := by rw [hy_comm_omega]
    _ = rightConjugateElem
          (f (f (rightConjugateElem s a) * g omega))
          (rightConjugateElem (h omega) t) * f omega := hH6
    _ = rightConjugateElem (f (g omega * rightConjugateElem s a⁻¹))
          (rightConjugateElem (h omega) t) * f omega := by
      rw [hfg.1, hy_inv_comm_gomega]

end PFchapter4section2
end CFSG.BenderSuzuki
