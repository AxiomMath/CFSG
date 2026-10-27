module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section3.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H6_a

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section3

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 3, Claim (2) -/

private theorem claim_2_coordinate_projection
    {G E : Type*} [Group G] [Field E] [CharP E 2]
    (Q Q0 KW : Subgroup G) (bar kcoord : G → E)
    (A omega sa zeta a : G)
    (hA_mem : A ∈ Q) (homega_mem : omega ∈ Q) (homega_not_Q0 : omega ∉ Q0)
    (hsa_mem : sa ∈ Q) (hsa_Q0 : sa ∈ Q0)
    (hzeta_mem : zeta ∈ KW) (ha_mem : a ∈ KW)
    (hQ_conj : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ KW → rightConjugateElem x d ∈ Q)
    (hbar_mul : ∀ x : G, x ∈ Q → ∀ y : G, y ∈ Q →
      bar (x * y) = bar x + bar y)
    (hbar_Q0 : ∀ x : G, x ∈ Q → (bar x = 0 ↔ x ∈ Q0))
    (hbar_conj : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ KW →
      bar (rightConjugateElem x d) = kcoord d * bar x)
    (hkcoord_mul : ∀ x : G, x ∈ KW → ∀ y : G, y ∈ KW →
      kcoord (x * y) = kcoord x * kcoord y)
    (hkcoord_inv : ∀ x : G, x ∈ KW → kcoord x⁻¹ = (kcoord x)⁻¹)
    (hkcoord_pow : ∀ x : G, x ∈ KW → ∀ n : ℕ, kcoord (x ^ n) = kcoord x ^ n)
    (hkcoord_ne_zero : ∀ x : G, x ∈ KW → kcoord x ≠ 0)
    (hidentity :
      rightConjugateElem A (zeta⁻¹ * a ^ 2) * sa =
        rightConjugateElem A (zeta⁻¹ ^ 2) * rightConjugateElem omega zeta⁻¹) :
    bar A = bar omega / (kcoord a ^ 2 + (kcoord zeta)⁻¹) := by
  have hzeta_inv_mem : zeta⁻¹ ∈ KW := KW.inv_mem hzeta_mem
  have ha_sq_mem : a ^ 2 ∈ KW := KW.pow_mem ha_mem 2
  have hleft_actor_mem : zeta⁻¹ * a ^ 2 ∈ KW :=
    KW.mul_mem hzeta_inv_mem ha_sq_mem
  have hright_actor_mem : zeta⁻¹ ^ 2 ∈ KW := KW.pow_mem hzeta_inv_mem 2
  have hleft_conj_mem : rightConjugateElem A (zeta⁻¹ * a ^ 2) ∈ Q :=
    hQ_conj A hA_mem _ hleft_actor_mem
  have hright_conj_mem : rightConjugateElem A (zeta⁻¹ ^ 2) ∈ Q :=
    hQ_conj A hA_mem _ hright_actor_mem
  have homega_conj_mem : rightConjugateElem omega zeta⁻¹ ∈ Q :=
    hQ_conj omega homega_mem _ hzeta_inv_mem
  have hbar_sa : bar sa = 0 := (hbar_Q0 sa hsa_mem).2 hsa_Q0
  have hscalar :
      kcoord (zeta⁻¹ * a ^ 2) * bar A =
        kcoord (zeta⁻¹ ^ 2) * bar A + kcoord zeta⁻¹ * bar omega := by
    calc
      kcoord (zeta⁻¹ * a ^ 2) * bar A =
          bar (rightConjugateElem A (zeta⁻¹ * a ^ 2)) := by
        rw [hbar_conj A hA_mem _ hleft_actor_mem]
      _ = bar (rightConjugateElem A (zeta⁻¹ * a ^ 2)) + bar sa := by
        rw [hbar_sa, add_zero]
      _ = bar (rightConjugateElem A (zeta⁻¹ * a ^ 2) * sa) := by
        rw [hbar_mul _ hleft_conj_mem sa hsa_mem]
      _ = bar (rightConjugateElem A (zeta⁻¹ ^ 2) *
          rightConjugateElem omega zeta⁻¹) := by rw [hidentity]
      _ = bar (rightConjugateElem A (zeta⁻¹ ^ 2)) +
          bar (rightConjugateElem omega zeta⁻¹) :=
        hbar_mul _ hright_conj_mem _ homega_conj_mem
      _ = kcoord (zeta⁻¹ ^ 2) * bar A + kcoord zeta⁻¹ * bar omega := by
        rw [hbar_conj A hA_mem _ hright_actor_mem,
          hbar_conj omega homega_mem _ hzeta_inv_mem]
  rw [hkcoord_mul zeta⁻¹ hzeta_inv_mem (a ^ 2) ha_sq_mem,
    hkcoord_inv zeta hzeta_mem, hkcoord_pow a ha_mem 2,
    hkcoord_pow zeta⁻¹ hzeta_inv_mem 2,
    hkcoord_inv zeta hzeta_mem] at hscalar
  have hzeta_coord_ne : kcoord zeta ≠ 0 := hkcoord_ne_zero zeta hzeta_mem
  have hproduct :
      (kcoord a ^ 2 + (kcoord zeta)⁻¹) * bar A = bar omega := by
    field_simp [hzeta_coord_ne] at hscalar ⊢
    calc
      bar A * (kcoord zeta * kcoord a ^ 2 + 1) =
          kcoord zeta * kcoord a ^ 2 * bar A + bar A := by ring
      _ = (bar A + kcoord zeta * bar omega) + bar A := by rw [hscalar]
      _ = (bar A + bar A) + kcoord zeta * bar omega := by ring
      _ = kcoord zeta * bar omega := by
        rw [CharTwo.add_self_eq_zero, zero_add]
  have hdenom_ne : kcoord a ^ 2 + (kcoord zeta)⁻¹ ≠ 0 := by
    intro hdenom
    have homega_zero : bar omega = 0 := by
      rw [← hproduct, hdenom, zero_mul]
    exact homega_not_Q0 ((hbar_Q0 omega homega_mem).1 homega_zero)
  apply (eq_div_iff hdenom_ne).2
  rw [mul_comm]
  exact hproduct

public theorem claim_2
    {G Ω E : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    [Field E] [CharP E 2]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s omega zeta : G)
    (bar kcoord : G → E) (f g h : G → G)
    (hsection3 : ((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ rightConjugateElem x t = x⁻¹) ∧
      V = PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ IsInvolution s ∧
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
    (homega_mem_Q : omega ∈ Q) (homega_not_mem_Q0 : omega ∉ Q0)
    (hzeta_mem_W : zeta ∈ W) (hzeta_ne_one : zeta ≠ 1)
    (hf_omega_eq : f omega = rightConjugateElem omega⁻¹ zeta)
    (hh_omega_mem_W : h omega ∈ W)
    (hW_fixed_point_free : ∀ d : G, d ∈ W → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0)
    (hbar_mul : ∀ x : G, x ∈ Q → ∀ y : G, y ∈ Q →
      bar (x * y) = bar x + bar y)
    (hbar_Q0 : ∀ x : G, x ∈ Q → (bar x = 0 ↔ x ∈ Q0))
    (hbar_conj : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ K ⊔ W →
      bar (rightConjugateElem x d) = kcoord d * bar x)
    (hkcoord_mul : ∀ x : G, x ∈ K ⊔ W → ∀ y : G, y ∈ K ⊔ W →
      kcoord (x * y) = kcoord x * kcoord y)
    (hkcoord_inv : ∀ x : G, x ∈ K ⊔ W → kcoord x⁻¹ = (kcoord x)⁻¹)
    (hkcoord_pow : ∀ x : G, x ∈ K ⊔ W → ∀ n : ℕ,
      kcoord (x ^ n) = kcoord x ^ n)
    (hkcoord_ne_zero : ∀ x : G, x ∈ K ⊔ W → kcoord x ≠ 0) :
    ∀ a : G, a ∈ K →
      bar (f (omega * rightConjugateElem s a)) =
        bar omega / (kcoord a ^ 2 + (kcoord zeta)⁻¹) := by
  intro a ha
  have hsec := hsection3.section2
  have hs_mem_Q : s ∈ Q :=
    hsec.Q0_le_Q ((hsec.Q0_def s).2
      (Or.inr ⟨hsection3.s_mem_H, hsection3.s_involution⟩))
  have ha_mem_D : a ∈ D := hsec.K_le_D ha
  have ha_mem_H : a ∈ H :=
    PFchapter4section1.rankOneSplit_D_le_M hD_eq ha_mem_D
  have hsa_mem_Q : rightConjugateElem s a ∈ Q :=
    PFchapter4section1.h6_rightConjugateElem_mem_Q_of_mem_M
      (PFchapter4section1.rankOneSplit_Q_le_M hQ_sup_D) hQ_normal_in_H
      hs_mem_Q ha_mem_H
  have hsa_involution : IsInvolution (rightConjugateElem s a) :=
    isInvolution_rightConjugateElem hsection3.s_involution
  have hsa_mem_H : rightConjugateElem s a ∈ H :=
    H.mul_mem (H.mul_mem (H.inv_mem ha_mem_H) hsection3.s_mem_H) ha_mem_H
  have hsa_mem_Q0 : rightConjugateElem s a ∈ Q0 :=
    (hsec.Q0_def _).2 (Or.inr ⟨hsa_mem_H, hsa_involution⟩)
  have hprod_mem_Q : omega * rightConjugateElem s a ∈ Q :=
    Q.mul_mem homega_mem_Q hsa_mem_Q
  have hprod_ne_one : omega * rightConjugateElem s a ≠ 1 := by
    intro hprod
    apply homega_not_mem_Q0
    have homega_eq : omega = (rightConjugateElem s a)⁻¹ :=
      eq_inv_of_mul_eq_one_left hprod
    rw [homega_eq, hsa_involution.inv_eq_self]
    exact hsa_mem_Q0
  have hfprod_mem_Q : f (omega * rightConjugateElem s a) ∈ Q :=
    (hf_mem _ hprod_mem_Q hprod_ne_one).1
  have hW_le_D : W ≤ D := by
    intro w hw
    have hwV : w ∈ V := hsec.W_le_V hw
    rw [hsec.V_eq] at hwV
    exact hwV.1
  have hKW_le_D : K ⊔ W ≤ D := sup_le hsec.K_le_D hW_le_D
  have hKW_le_H : K ⊔ W ≤ H :=
    hKW_le_D.trans (PFchapter4section1.rankOneSplit_D_le_M hD_eq)
  have hQ_conj : ∀ x : G, x ∈ Q → ∀ d : G, d ∈ K ⊔ W →
      rightConjugateElem x d ∈ Q := by
    intro x hx d hd
    exact PFchapter4section1.h6_rightConjugateElem_mem_Q_of_mem_M
      (PFchapter4section1.rankOneSplit_Q_le_M hQ_sup_D) hQ_normal_in_H
      hx (hKW_le_H hd)
  have hidentity := claim_1 H D Q K V W Q0 S Q1 t s omega zeta f g h a
    hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution
    ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem
    hg_mem hh_mem hcanonical_eq homega_mem_Q homega_not_mem_Q0
    hzeta_mem_W hzeta_ne_one hf_omega_eq hh_omega_mem_W ha
    hW_fixed_point_free
  exact claim_2_coordinate_projection Q Q0 (K ⊔ W) bar kcoord
    (f (omega * rightConjugateElem s a)) omega (rightConjugateElem s a)
    zeta a hfprod_mem_Q homega_mem_Q homega_not_mem_Q0 hsa_mem_Q
    hsa_mem_Q0 (Subgroup.mem_sup_right hzeta_mem_W) (Subgroup.mem_sup_left ha)
    hQ_conj hbar_mul hbar_Q0 hbar_conj hkcoord_mul hkcoord_inv
    hkcoord_pow hkcoord_ne_zero hidentity

end PFchapter4section3
end CFSG.BenderSuzuki
