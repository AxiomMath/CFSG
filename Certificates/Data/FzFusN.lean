module

public import Certificates.Data.FzFusK3

public section

namespace Certificates.FzFus

open Certificates.FzJ36

instance isInvMDecidable (m : Model) : Decidable (IsInvM m) := by
  unfold IsInvM
  infer_instance

instance d5mDecidable (u a b : Model) : Decidable (D5M u a b) := by
  unfold D5M
  infer_instance

@[expose] def z2M : Model := mkE 1 (QuaternionGroup.a 2) 1

theorem central_of_inv (n : N3) (hn : IsInvM ⟨n, 1⟩)
    (h : ¬ (lett n.1 ≠ 0 ∧ lett n.2.1 ≠ 0 ∧ lett n.2.2 ≠ 0)) :
    KEq ⟨n, 1⟩ z1M ∨ KEq ⟨n, 1⟩ z2M ∨ KEq ⟨n, 1⟩ z3M := by
  revert n
  decide +kernel

theorem rz_rep_facts : ∀ c ∈ rzList, IsInvM (rep c) ∧ ¬ KEq (rep c) z1M ∧ ¬ KEq (rep c) z3M ∧
    ¬ KEq (rep c) (z1M * z3M) ∧ ∃ n : N3, rep c = ⟨n, 1⟩ := by
  decide +kernel

theorem pairR_fact (q1 q2 q3 : Q8) (h1 : lett q1 ≠ 0) (h2 : lett q2 ≠ 0) (h3 : lett q3 ≠ 0) :
    KEq (mkE q1 1 1 * mkE q1 q2 q3) (mkE q1 q2 q3 * mkE q1 1 1) ∧
    KEq (mkE 1 q2 1 * mkE q1 q2 q3) (mkE q1 q2 q3 * mkE 1 q2 1) ∧
    D5M (mkE q1 q2 q3) (mkE q1 1 1) (mkE 1 q2 1) := by
  revert q1 q2 q3
  decide +kernel

theorem x1M_eq : x1M = mkE (qL 1) 1 1 * tM := by
  decide +kernel

theorem x2M_eq : x2M = mkE 1 (qL 1) 1 * tM := by
  decide +kernel

theorem tM_eq : tM = mkE (qL 1) 1 1 * mkE 1 (qL 1) 1 * mkE 1 1 (qL 1) := by
  decide +kernel

theorem z1M_keq : KEq z1M (x1M * x1M) := by
  decide +kernel

theorem z2M_keq : KEq z2M (x2M * x2M) := by
  decide +kernel

theorem z3M_keq : KEq z3M (x1M * x2M * (x1M * x2M)) := by
  decide +kernel

theorem rep_oI_eq : rep .oI = tM * lamM := by
  decide +kernel

theorem label_facts : IsInvM lamM ∧ IsInvM z1M ∧ IsInvM z3M ∧ IsInvM (tM * lamM) ∧
    IsInvM (rep .oJ) ∧ IsInvM (rep .oK) ∧ KEq (rep .oJ * tM) (tM * rep .oJ) ∧
    KEq (rep .oK * tM) (tM * rep .oK) := by
  decide +kernel

theorem phi_zeta (u v : Fin 4) : phi u v zeta = 1 := by
  revert u v
  decide +kernel

theorem phiQ_facts : phi 0 1 tM = 1 ∧ phi 0 1 x1M = 1 ∧ phi 0 1 x2M = 1 ∧ phi 0 1 lamM = 1 ∧
    phi 0 1 (rep .oJ) ≠ 1 ∧ phi 0 1 (rep .oK) ≠ 1 := by
  decide +kernel

end Certificates.FzFus
