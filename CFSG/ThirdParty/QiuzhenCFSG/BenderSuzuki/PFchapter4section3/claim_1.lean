module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H4_b
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section1.claim_H5
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_2
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter4section2.claim_3

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter4section3

open PFchapter1section1 PFAppendixIII PFchapter3section1 PFchapter3section3

/-! # Peterfalvi, Part II, Chapter IV, Section 3, Claim (1) -/

public theorem claim_1
{G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 : Subgroup G) (t s omega zeta : G) (f g h : G → G)
    (a : G)
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
    (homega_mem_Q : omega ∈ Q) (homega_not_mem_Q0 : omega ∉ Q0)
    (hzeta_mem_W : zeta ∈ W) (hzeta_ne_one : zeta ≠ 1)
    (hf_omega_eq : f omega = rightConjugateElem omega⁻¹ zeta)
    (hh_omega_mem_W : h omega ∈ W) (ha : a ∈ K)
    (hW_fixed_point_free : ∀ d : G, d ∈ W → d ≠ 1 →
      ∀ x : G, x ∈ Q → x ∉ Q0 →
        rightConjugateElem x d * x⁻¹ ∉ Q0) :
    rightConjugateElem (f (omega * rightConjugateElem s a))
        (zeta⁻¹ * a ^ 2) * rightConjugateElem s a =
      rightConjugateElem (f (omega * rightConjugateElem s a)) (zeta⁻¹ ^ 2) *
        rightConjugateElem omega zeta⁻¹ := by
  have _ := hzeta_ne_one
  have hsec := hsection3.section2
  have hA1 := hsec.hA.A1
  have homega_ne_one : omega ≠ 1 := by
    intro homega
    exact homega_not_mem_Q0 (homega ▸ Q0.one_mem)
  have homega_inv_mem_Q : omega⁻¹ ∈ Q := Q.inv_mem homega_mem_Q
  have homega_inv_ne_one : omega⁻¹ ≠ 1 := by
    simpa using homega_ne_one
  have homega_inv_not_mem_Q0 : omega⁻¹ ∉ Q0 := by
    intro homega_inv_mem
    exact homega_not_mem_Q0 (by simpa using Q0.inv_mem homega_inv_mem)
  have hzeta_mem_V : zeta ∈ V := hsec.W_le_V hzeta_mem_W
  have hzeta_mem_peterfalviV : zeta ∈ peterfalviV D t := by
    rw [← hsec.V_eq]
    exact hzeta_mem_V
  have hzeta_mem_D : zeta ∈ D := hzeta_mem_peterfalviV.1
  have hzeta_fixed_t : rightConjugateElem zeta t = zeta := by
    have hcomm : Commute zeta t :=
      Subgroup.mem_centralizer_singleton_iff.mp hzeta_mem_peterfalviV.2
    simp [rightConjugateElem, hcomm.eq, mul_assoc]
  have hzeta_inv_fixed_t : rightConjugateElem zeta⁻¹ t = zeta⁻¹ := by
    calc
      rightConjugateElem zeta⁻¹ t = (rightConjugateElem zeta t)⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = zeta⁻¹ := by rw [hzeta_fixed_t]
  have hzeta_pow_fixed_t (n : ℕ) : rightConjugateElem (zeta ^ n) t = zeta ^ n := by
    induction n with
    | zero => simp [rightConjugateElem]
    | succ n ih =>
        calc
          rightConjugateElem (zeta ^ (n + 1)) t =
              rightConjugateElem (zeta ^ n * zeta) t := by rw [pow_succ]
          _ =
              rightConjugateElem (zeta ^ n) t * rightConjugateElem zeta t := by
            simp [rightConjugateElem, mul_assoc]
          _ = zeta ^ n * zeta := by rw [ih, hzeta_fixed_t]
          _ = zeta ^ (n + 1) := by rw [pow_succ]
  have hf_omega_inv : f omega⁻¹ = rightConjugateElem omega zeta⁻¹ := by
    have hffomega := PFchapter4section1.claim_H2 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq omega homega_mem_Q homega_ne_one
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq omega⁻¹ zeta homega_inv_mem_Q homega_inv_ne_one
      hzeta_mem_D
    have hconj : rightConjugateElem (f omega⁻¹) zeta = omega := by
      calc
        rightConjugateElem (f omega⁻¹) zeta =
            rightConjugateElem (f omega⁻¹) (rightConjugateElem zeta t) := by
          rw [hzeta_fixed_t]
        _ = f (rightConjugateElem omega⁻¹ zeta) := htransport.symm
        _ = f (f omega) := by rw [hf_omega_eq]
        _ = omega := hffomega
    have hback := congrArg (fun x : G ↦ rightConjugateElem x zeta⁻¹) hconj
    simpa [rightConjugateElem, mul_assoc] using hback
  have hg_omega_inv : g omega⁻¹ = rightConjugateElem omega zeta := by
    have hH1 := PFchapter4section1.claim_H1 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq omega⁻¹ homega_inv_mem_Q homega_inv_ne_one
    have hH1' : f omega = (g omega⁻¹)⁻¹ := by simpa using hH1
    calc
      g omega⁻¹ = ((g omega⁻¹)⁻¹)⁻¹ := by simp
      _ = (f omega)⁻¹ := by rw [hH1']
      _ = (rightConjugateElem omega⁻¹ zeta)⁻¹ := by rw [hf_omega_eq]
      _ = rightConjugateElem omega zeta := by
        simp [rightConjugateElem, mul_assoc]
  have hh_omega_inv_mem_W : h omega⁻¹ ∈ W := by
    have hhomega_mem_V : h omega ∈ V := hsec.W_le_V hh_omega_mem_W
    have hhomega_mem_peterfalviV : h omega ∈ peterfalviV D t := by
      rw [← hsec.V_eq]
      exact hhomega_mem_V
    have hhomega_fixed_t : rightConjugateElem (h omega) t = h omega := by
      have hcomm : Commute (h omega) t :=
        Subgroup.mem_centralizer_singleton_iff.mp hhomega_mem_peterfalviV.2
      simp [rightConjugateElem, hcomm.eq, mul_assoc]
    have hH4b := PFchapter4section1.claim_H4_b H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq omega homega_mem_Q homega_ne_one
    rw [hH4b, hhomega_fixed_t]
    exact W.inv_mem hh_omega_mem_W
  have hh_omega_inv : h omega⁻¹ = zeta⁻¹ ^ 3 := by
    have hstep1 : (f omega)⁻¹ = rightConjugateElem omega zeta := by
      rw [hf_omega_eq]
      simp [rightConjugateElem, mul_assoc]
    have htransport_zeta := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq omega zeta homega_mem_Q homega_ne_one hzeta_mem_D
    have hstep2 :
        f ((f omega)⁻¹) = rightConjugateElem omega⁻¹ (zeta ^ 2) := by
      calc
        f ((f omega)⁻¹) = f (rightConjugateElem omega zeta) := by rw [hstep1]
        _ = rightConjugateElem (f omega) (rightConjugateElem zeta t) :=
          htransport_zeta
        _ = rightConjugateElem (rightConjugateElem omega⁻¹ zeta) zeta := by
          rw [hzeta_fixed_t, hf_omega_eq]
        _ = rightConjugateElem omega⁻¹ (zeta ^ 2) := by
          simp [rightConjugateElem, pow_two, mul_assoc]
    have hstep2_inv :
        (f ((f omega)⁻¹))⁻¹ = rightConjugateElem omega (zeta ^ 2) := by
      rw [hstep2]
      simp [rightConjugateElem, mul_assoc]
    have hzeta_sq_mem_D : zeta ^ 2 ∈ D := D.pow_mem hzeta_mem_D 2
    have htransport_zeta_sq := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq omega (zeta ^ 2) homega_mem_Q homega_ne_one
      hzeta_sq_mem_D
    have hfj3 :
        f ((f ((f omega)⁻¹))⁻¹) =
          rightConjugateElem omega⁻¹ (zeta ^ 3) := by
      calc
        f ((f ((f omega)⁻¹))⁻¹) =
            f (rightConjugateElem omega (zeta ^ 2)) := by rw [hstep2_inv]
        _ = rightConjugateElem (f omega)
            (rightConjugateElem (zeta ^ 2) t) := htransport_zeta_sq
        _ = rightConjugateElem (rightConjugateElem omega⁻¹ zeta)
            (zeta ^ 2) := by rw [hzeta_pow_fixed_t, hf_omega_eq]
        _ = rightConjugateElem omega⁻¹ (zeta ^ 3) := by
          simp [rightConjugateElem, pow_succ, mul_assoc]
    have hH5 := PFchapter4section1.claim_H5 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq omega⁻¹ homega_inv_mem_Q homega_inv_ne_one
    have hH5' :
        f ((f ((f omega)⁻¹))⁻¹) =
          rightConjugateElem omega⁻¹ (h omega⁻¹)⁻¹ := by
      simpa using hH5
    have hconj_eq :
        rightConjugateElem omega⁻¹ (h omega⁻¹)⁻¹ =
          rightConjugateElem omega⁻¹ (zeta ^ 3) :=
      hH5'.symm.trans hfj3
    let d : G := (h omega⁻¹)⁻¹ * (zeta ^ 3)⁻¹
    have hd_mem_W : d ∈ W := by
      exact W.mul_mem (W.inv_mem hh_omega_inv_mem_W)
        (W.inv_mem (W.pow_mem hzeta_mem_W 3))
    have hfix : rightConjugateElem omega⁻¹ d = omega⁻¹ := by
      have hback := congrArg
        (fun x : G ↦ rightConjugateElem x (zeta ^ 3)⁻¹) hconj_eq
      simpa [d, rightConjugateElem, mul_assoc] using hback
    have hd_one : d = 1 := by
      by_contra hd_ne
      have hnot := hW_fixed_point_free d hd_mem_W hd_ne omega⁻¹
        homega_inv_mem_Q homega_inv_not_mem_Q0
      apply hnot
      rw [hfix]
      simp
    have hactor : (h omega⁻¹)⁻¹ = zeta ^ 3 := by
      exact eq_of_mul_inv_eq_one hd_one
    calc
      h omega⁻¹ = ((h omega⁻¹)⁻¹)⁻¹ := by simp
      _ = (zeta ^ 3)⁻¹ := by rw [hactor]
      _ = zeta⁻¹ ^ 3 := by group
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
  have hzeta_mem_peterfalviW : zeta ∈ peterfalviW V (K : Set G) := by
    rw [← hsec.W_eq]
    exact hzeta_mem_W
  have ha_comm_zeta : Commute a zeta :=
    Subgroup.mem_centralizer_iff.mp hzeta_mem_peterfalviW.2 a ha
  have hV_eq_s :
      peterfalviV D t = D ⊓ Subgroup.centralizer ({s} : Set G) :=
    (PFchapter1section1.proposition_5 H D Q t s hA1 hsection3.s_mem_H
      hsection3.s_involution hsection3.s_conjugate).1
  have hs_comm_zeta : Commute s zeta := by
    have hzeta_mem_Cs : zeta ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [hV_eq_s] at hzeta_mem_peterfalviV
      exact hzeta_mem_peterfalviV.2
    exact (Subgroup.mem_centralizer_singleton_iff.mp hzeta_mem_Cs).symm
  have hsa_comm_zeta : Commute (rightConjugateElem s a) zeta := by
    have hcomm : Commute (a⁻¹ * s * a) zeta :=
      (ha_comm_zeta.inv_left.mul_left hs_comm_zeta).mul_left ha_comm_zeta
    simpa [rightConjugateElem, mul_assoc] using hcomm
  have hsa_fixed_zeta :
      rightConjugateElem (rightConjugateElem s a) zeta =
        rightConjugateElem s a := by
    exact hsa_comm_zeta.symm.inv_mul_cancel
  have hsa_fixed_zeta_inv :
      rightConjugateElem (rightConjugateElem s a) zeta⁻¹ =
        rightConjugateElem s a := by
    exact hsa_comm_zeta.inv_right.symm.inv_mul_cancel
  have hprod_conj_zeta :
      rightConjugateElem (omega * rightConjugateElem s a) zeta =
        rightConjugateElem omega zeta * rightConjugateElem s a := by
    calc
      rightConjugateElem (omega * rightConjugateElem s a) zeta =
          rightConjugateElem omega zeta *
            rightConjugateElem (rightConjugateElem s a) zeta := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem omega zeta * rightConjugateElem s a := by
        rw [hsa_fixed_zeta]
  have hprod_conj_zeta_inv :
      rightConjugateElem (omega * rightConjugateElem s a) zeta⁻¹ =
        rightConjugateElem omega zeta⁻¹ * rightConjugateElem s a := by
    calc
      rightConjugateElem (omega * rightConjugateElem s a) zeta⁻¹ =
          rightConjugateElem omega zeta⁻¹ *
            rightConjugateElem (rightConjugateElem s a) zeta⁻¹ := by
        simp [rightConjugateElem, mul_assoc]
      _ = rightConjugateElem omega zeta⁻¹ * rightConjugateElem s a := by
        rw [hsa_fixed_zeta_inv]
  have hf_prod_zeta :
      f (rightConjugateElem omega zeta * rightConjugateElem s a) =
        rightConjugateElem (f (omega * rightConjugateElem s a)) zeta := by
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq (omega * rightConjugateElem s a) zeta hprod_mem_Q
      hprod_ne_one hzeta_mem_D
    rw [hprod_conj_zeta] at htransport
    simpa [hzeta_fixed_t] using htransport
  have hf_prod_zeta_inv :
      f (rightConjugateElem omega zeta⁻¹ * rightConjugateElem s a) =
        rightConjugateElem (f (omega * rightConjugateElem s a)) zeta⁻¹ := by
    have htransport := PFchapter4section1.claim_H3 H Q D t f g h
      htwo_transitive hpoint_stabilizer ht_involution ht_not_mem_H hD_eq
      hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem hg_mem hh_mem
      hcanonical_eq (omega * rightConjugateElem s a) zeta⁻¹ hprod_mem_Q
      hprod_ne_one (D.inv_mem hzeta_mem_D)
    rw [hprod_conj_zeta_inv] at htransport
    simpa [hzeta_inv_fixed_t] using htransport
  have hclaim2 := PFchapter4section2.claim_2 H D Q K V W Q0 S Q1 t s f g h
    hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution
    ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem
    hg_mem hh_mem hcanonical_eq omega⁻¹ a⁻¹ homega_inv_mem_Q
    homega_inv_not_mem_Q0 (K.inv_mem ha)
  have hclaim3 := PFchapter4section2.claim_3 H D Q K V W Q0 S Q1 t s f g h
    hsection3 hC1 hC2 htwo_transitive hpoint_stabilizer ht_involution
    ht_not_mem_H hD_eq hQ_normal_in_H hQ_disjoint_D hQ_sup_D hf_mem
    hg_mem hh_mem hcanonical_eq omega⁻¹ a⁻¹ homega_inv_mem_Q
    homega_inv_not_mem_Q0 (K.inv_mem ha)
  have hfirst :
      f (omega⁻¹ * rightConjugateElem s a⁻¹) =
        rightConjugateElem (f (omega * rightConjugateElem s a))
            (zeta⁻¹ * a ^ 2) * rightConjugateElem s a := by
    calc
      f (omega⁻¹ * rightConjugateElem s a⁻¹) =
          rightConjugateElem
              (f (f omega⁻¹ * rightConjugateElem s (a⁻¹)⁻¹))
              ((a⁻¹)⁻¹ ^ 2) * rightConjugateElem s (a⁻¹)⁻¹ :=
        hclaim2
      _ = rightConjugateElem
            (rightConjugateElem (f (omega * rightConjugateElem s a)) zeta⁻¹)
            (a ^ 2) * rightConjugateElem s a := by
        rw [inv_inv, hf_omega_inv, hf_prod_zeta_inv]
      _ = rightConjugateElem (f (omega * rightConjugateElem s a))
            (zeta⁻¹ * a ^ 2) * rightConjugateElem s a := by
        simp [rightConjugateElem, mul_assoc]
  have hsecond :
      f (omega⁻¹ * rightConjugateElem s a⁻¹) =
        rightConjugateElem (f (omega * rightConjugateElem s a))
            (zeta⁻¹ ^ 2) * rightConjugateElem omega zeta⁻¹ := by
    have hzeta_inv_cube_fixed_t :
        rightConjugateElem (zeta⁻¹ ^ 3) t = zeta⁻¹ ^ 3 := by
      calc
        rightConjugateElem (zeta⁻¹ ^ 3) t =
            rightConjugateElem (zeta ^ 3)⁻¹ t := by
          congr 1
          group
        _ = (rightConjugateElem (zeta ^ 3) t)⁻¹ := by
          simp [rightConjugateElem, mul_assoc]
        _ = (zeta ^ 3)⁻¹ := by rw [hzeta_pow_fixed_t]
        _ = zeta⁻¹ ^ 3 := by group
    calc
      f (omega⁻¹ * rightConjugateElem s a⁻¹) =
          rightConjugateElem
              (f (g omega⁻¹ * rightConjugateElem s (a⁻¹)⁻¹))
              (rightConjugateElem (h omega⁻¹) t) * f omega⁻¹ :=
        hclaim3
      _ = rightConjugateElem
            (rightConjugateElem (f (omega * rightConjugateElem s a)) zeta)
            (zeta⁻¹ ^ 3) * rightConjugateElem omega zeta⁻¹ := by
        rw [inv_inv, hg_omega_inv, hf_prod_zeta, hh_omega_inv,
          hzeta_inv_cube_fixed_t, hf_omega_inv]
      _ = rightConjugateElem (f (omega * rightConjugateElem s a))
            (zeta⁻¹ ^ 2) * rightConjugateElem omega zeta⁻¹ := by
        congr 1
        simp only [rightConjugateElem]
        group
  exact hfirst.symm.trans hsecond

end PFchapter4section3
end CFSG.BenderSuzuki
