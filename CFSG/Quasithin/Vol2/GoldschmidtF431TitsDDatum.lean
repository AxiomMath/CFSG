module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDLocFusion
public import Certificates.Kernel.J4Count.FixC

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.J47 CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits CFSG.RuF45
  CFSG.TwoF4Lie CFSG.TwoF4Loc CFSG.TitsLoc CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


theorem comm_qD_zD : Commute qD zD := by
  have h := qD_rels.1
  show qD * zD = zD * qD
  rw [← h]
  exact (mul_assoc _ _ _).symm

theorem comm_qD_VD : ∀ v ∈ VD, qD * v = v * qD := by
  intro v hv
  have hz1 : Commute qD z1D := qD_rels.2.2
  rcases mem_VD.1 hv with rfl | rfl | rfl | rfl
  · simp
  · exact comm_qD_zD.eq
  · exact hz1.eq
  · rw [← zD_mul_z1D]
    exact (comm_qD_zD.mul_right hz1).eq

theorem qD_sq : qD ^ 2 = zD := by
  rw [pow_two]
  exact qD_rels.1

theorem titsD_Loc442Datum : Loc442Datum titsHD titsND titsSD zD tD VD qD where
  lie := titsD_F431LieI
  V_le := V_le_D
  V_card := card_VD
  V_comm := kleinFour_comm
  V_sq := kleinFour_sq
  V_norm := V_norm_D
  V_conj := V_conj_D
  q_mem := Subgroup.mem_centralizer_singleton_iff.2 qD_rels.2.1
  q_comm := comm_qD_VD
  q_sq := by
    rw [qD_sq]
    exact mem_VD.2 (Or.inr (Or.inl rfl))
  q_sq_ne := by
    rw [qD_sq]
    exact zD_ne_one
  M2_card := by
    rw [card_titsND]
    norm_num
  fusion := fusion_D

end CFSG.Quasithin.H13.F431.TitsD
