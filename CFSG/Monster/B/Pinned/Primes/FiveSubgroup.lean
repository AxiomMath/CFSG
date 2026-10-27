module

public import CFSG.Monster.B.Pinned.Primes.FiveRelations
public import Certificates.Certificate16027

public section

namespace CFSG.Monster.B.Pinned

open CFSG.Blueprint

theorem MFive_mul_inv :
    MFive * rowsMat 5 4 fiveCommInvRows = 1 :=
  Certificates.certificate16027.1

theorem isUnit_det_MFive : IsUnit MFive.det := by
  have h := congrArg Matrix.det MFive_mul_inv
  rw [Matrix.det_mul, Matrix.det_one] at h
  exact IsUnit.of_mul_eq_one _ h

theorem qFive_mem
    (i : Fin 4) : qFive i ∈ QFive := Subgroup.subset_closure ⟨i, rfl⟩

theorem zFive_mem : zFive ∈ QFive := by
  unfold zFive bcomm
  exact mul_mem (mul_mem (mul_mem (inv_mem (qFive_mem 0)) (inv_mem (qFive_mem 1)))
    (qFive_mem 0)) (qFive_mem 1)

theorem commData_five :
    CommData 5 qFive zFive MFive where
  pow_q i := by rw [← orderOf_qFive i]; exact pow_orderOf_eq_one _
  orderOf_z := orderOf_zFive
  comm_z := comm_qFive_zFive
  bcomm_q := bcomm_qFive
  isUnit_det := isUnit_det_MFive
  mem_z := zFive_mem

theorem conj_qFive_mem
    (i : Fin 4) : xFive⁻¹ * qFive i * xFive ∈ QFive := by
  rw [conj_qFive]
  refine mul_mem (Subgroup.list_prod_mem _ fun g hg => ?_) (pow_mem zFive_mem _)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
  exact pow_mem (qFive_mem j) _

theorem xFive_conj_mem :
    ∀ g ∈ QFive, xFive⁻¹ * g * xFive ∈ QFive :=
  fun _ hg => CommData.conj_mem conj_qFive_mem hg

theorem xFive_not_mem :
    xFive ∉ QFive := by
  have h := pinned_B_five_primary_exact_relations.2.2.2.2.2.2.2.2.2.1
  exact commData_five.not_mem_of_conj (i := 0) (j := 2) h (by exact Certificates.certificate16027.2)

theorem pinned_B_five_power_six_subgroup :
    Nat.card QFive = 5 ^ 5 ∧ (5 : ℕ) ^ 5 = 3125 ∧
      Subgroup.center QFive = (Subgroup.zpowers zFive).subgroupOf QFive ∧
      commutator QFive = (Subgroup.zpowers zFive).subgroupOf QFive ∧
      Nat.card (Subgroup.zpowers zFive) = 5 ∧
      (∃ _ : ((Subgroup.zpowers zFive).subgroupOf QFive).Normal,
        ∃ e : QFive ⧸ (Subgroup.zpowers zFive).subgroupOf QFive ≃*
          Multiplicative (Fin 4 → ZMod 5),
          ∀ i, e (QuotientGroup.mk ⟨qFive i, qFive_mem i⟩) = Multiplicative.ofAdd (Pi.single i 1)) ∧
      xFive ∈ Subgroup.normalizer (QFive : Set NativeSporadic.B) ∧ xFive ∉ QFive ∧
      Nat.card PFive = 5 ^ 6 ∧ (5 : ℕ) ^ 6 = 15625 ∧ 5 ^ 6 ∣ Nat.card NativeSporadic.B := by
  have := finite_B
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hD := commData_five
  have hQ : Nat.card QFive = 5 ^ 5 := hD.card_eq
  have hP : Nat.card PFive = 5 ^ 6 := by
    rw [PFive, card_sup_zpowers orderOf_xFive xFive_not_mem xFive_conj_mem, hQ]
    norm_num
  obtain ⟨hn, e, he, -⟩ := hD.quotient_equiv
  refine ⟨hQ, by norm_num, hD.center_eq, hD.commutator_eq (i₀ := 0) (j₀ := 1) rfl,
    by rw [Nat.card_zpowers, orderOf_zFive], ⟨hn, e, he⟩,
    mem_normalizer_of_conj xFive_conj_mem, xFive_not_mem, hP, by norm_num, ?_⟩
  rw [← hP]
  exact Subgroup.card_subgroup_dvd_card PFive

end CFSG.Monster.B.Pinned
