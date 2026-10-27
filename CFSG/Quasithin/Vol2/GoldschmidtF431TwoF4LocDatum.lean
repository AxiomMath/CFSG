module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4LocFusion
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Iso
public import Certificates.Kernel.J4Count.FixC
public import Certificates.Certificate7050Base

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru
  CFSG.Sporadic.Schreier.Tits CFSG.RuF45 CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem comm_zM_tM : Commute zM tM := by
  have h : tM ∈ twoF4M1 := twoF4_F431LieI.T_le₁ twoF4_F431LieI.t_mem
  rw [← cent_z_model] at h
  exact (Subgroup.mem_centralizer_singleton_iff.1 h).symm

theorem comm_cM_tM : Commute cM tM := Subtype.ext cEl_comm

theorem V_le_model : VM ≤ Subgroup.centralizer ({tM} : Set ↥twoF4M) := by
  intro v hv
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hz1 : Commute z1M tM := (comm_cM_tM.mul_left comm_zM_tM).mul_left comm_cM_tM.inv_left
  have hz2 : Commute z2M tM := (comm_cM_tM.inv_left.mul_left comm_zM_tM).mul_left comm_cM_tM
  rcases mem_VM.1 hv with rfl | rfl | rfl | rfl
  · exact (Commute.one_left tM).eq
  · exact comm_zM_tM.eq
  · exact hz1.eq
  · exact hz2.eq

theorem comm_qM_zM : Commute qM zM := by
  have h := q_rels.1
  show qM * zM = zM * qM
  rw [← h]
  exact (mul_assoc _ _ _).symm

theorem comm_qM_VM : ∀ v ∈ VM, qM * v = v * qM := by
  intro v hv
  have hz1 : Commute qM z1M := q_rels.2.2
  rcases mem_VM.1 hv with rfl | rfl | rfl | rfl
  · simp
  · exact comm_qM_zM.eq
  · exact hz1.eq
  · rw [← V_rels.1]
    exact (comm_qM_zM.mul_right hz1).eq

theorem qM_sq : qM ^ 2 = zM := by
  rw [pow_two]
  exact q_rels.1

theorem card_twoF4M2 : Nat.card twoF4M2 = 12288 := by
  have e : Nat.card twoF4M2 = Nat.card twoF4N := card_subgroupOf_eq twoF4N_le_M
  rw [e, card_twoF4N]

theorem twoF4_Loc442Datum : Loc442Datum twoF4M1 twoF4M2 twoF4TT zM tM VM qM where
  lie := twoF4_F431LieI
  V_le := V_le_model
  V_card := card_VM
  V_comm := kleinFour_comm
  V_sq := kleinFour_sq
  V_norm := V_norm_model
  V_conj := V_conj_model
  q_mem := Subgroup.mem_centralizer_singleton_iff.2 q_rels.2.1
  q_comm := comm_qM_VM
  q_sq := by
    rw [qM_sq]
    exact mem_VM.2 (Or.inr (Or.inl rfl))
  q_sq_ne := by
    rw [qM_sq]
    exact zM_ne_one
  M2_card := by
    rw [card_twoF4M2]
  fusion := fusion_model

end CFSG.Quasithin.H13.F431.TwoF4
