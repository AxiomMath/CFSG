module

public import CFSG.Monster.Existence.Assembly
public import CFSG.Monster.Existence.DLevelRank
public import CFSG.Monster.Existence.InvolutionClasses
public import CFSG.Monster.Existence.Census.TwoClasses
public import CFSG.Monster.Existence.TwoPointTwoB
public import CFSG.Monster.AxisCount.HSCount
public import CFSG.Monster.GMS.BabyCover
public import CFSG.Monster.B.TwoA.Sp8.QuadData
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6006
public import Certificates.Certificate6007
public import Certificates.Certificate6009
public import Certificates.Certificate6010
public import Certificates.Certificate6011
public import Certificates.Certificate6012
public import Certificates.Certificate6013
public import Certificates.Certificate6014
public import Certificates.Certificate6015
public import Certificates.Certificate6016
public import Certificates.Certificate6017
public import Certificates.Certificate6018
public import Certificates.Certificate16018
public import Certificates.Certificate16026
public import Certificates.Certificate3027
public import CFSG.Monster.AxisCount.BabyCoverSpec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.GMS

theorem Gmat_eq_AutO
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder) : Gmat = AutO := by
  have h1 : Nat.card Gmat = CFSG.Open.monsterOrder := by
    rw [AxisCount.HS.natCard_Gmat, natCard_Cgen_eq, AxisCount.Baby.natCard_Cbar]
    norm_num [CFSG.Open.monsterOrder]
  exact Subgroup.eq_of_le_of_card_ge Gmat_le_AutO (by rw [h1]; exact hcard.le)

theorem Cfull_eq_CfullA (hG : Gmat = AutO) : Cfull = CfullA := by
  rw [Cfull, CfullA, hG]

theorem Cfull_le_Cgen :
    Cfull ≤ Cgen := fun g hg =>
  AxisCount.HS.centralizer_tStar_le_Cgen g hg.1 (Subgroup.mem_centralizer_singleton_iff.1 hg.2)

theorem Shat_eq_top :
    Shat = ⊤ := by
  rw [← Subgroup.index_eq_one, index_Shat, Subgroup.index_eq_one, Subgroup.subgroupOf_eq_top]
  exact Cfull_le_Cgen

@[expose] noncomputable def centEquivCfull (hG : Gmat = AutO) : cent tGriess ≃* Cfull :=
  ((cent tGriess).equivMapOfInjective AutO.subtype AutO.subtype_injective).trans
    (MulEquiv.subgroupCongr (map_cent_tGriess.trans (Cfull_eq_CfullA hG).symm))

theorem centEquivCfull_self (hG : Gmat = AutO) :
    centEquivCfull hG ⟨tGriess, self_mem_cent tGriess⟩ = tStarF := rfl

@[expose] noncomputable def centToShat
    (hG : Gmat = AutO) : cent tGriess →* Shat :=
  (piD.comp (centEquivCfull hG).toMonoidHom).codRestrict Shat fun _ =>
    Shat_eq_top ▸ Subgroup.mem_top _

theorem coe_centToShat
    (hG : Gmat = AutO) (g : cent tGriess) :
    ((centToShat hG g : Shat) : Dfull) = piD (centEquivCfull hG g) := rfl

theorem centToShat_eq_one_iff
    (hG : Gmat = AutO) (g : cent tGriess) :
    centToShat hG g = 1 ↔ (g : MGriess) = 1 ∨ (g : MGriess) = tGriess := by
  have h1 : centToShat hG g = 1 ↔ piD (centEquivCfull hG g) = 1 := by
    rw [← Subtype.coe_inj, coe_centToShat]
    rfl
  rw [h1, piD_eq_one_iff]
  constructor
  · rintro (h | h)
    · left
      rw [(centEquivCfull hG).injective (h.trans (map_one _).symm)]
      rfl
    · right
      rw [← centEquivCfull_self hG] at h
      rw [(centEquivCfull hG).injective h]
  · rintro (h | h)
    · left
      rw [show g = 1 from Subtype.ext h, map_one]
    · right
      rw [show g = ⟨tGriess, self_mem_cent tGriess⟩ from Subtype.ext h, centEquivCfull_self]

theorem centToShat_surjective
    (hG : Gmat = AutO) : Function.Surjective (centToShat hG) := by
  intro s
  obtain ⟨c, hc⟩ := piD_surjective (s : Dfull)
  refine ⟨(centEquivCfull hG).symm c, Subtype.ext ?_⟩
  rw [coe_centToShat, MulEquiv.apply_symm_apply, hc]

@[expose] noncomputable def phiShat :
    Shat ≃* CFSG.Blueprint.NativeSporadic.B :=
  (MonoidHom.ofInjective iotaD_injective).symm.trans phiB

theorem phiShat_one :
    phiShat (1 : Shat) = 1 :=
  @MulEquiv.map_one Shat CFSG.Blueprint.NativeSporadic.B _ Units.instMulOneClass phiShat

theorem orderOf_phiShat
    (a : Shat) : orderOf (phiShat a) = orderOf a :=
  @MulEquiv.orderOf_eq _ _ _ Units.instMonoid phiShat a

theorem phiShat_eq_one_iff
    (a : Shat) : phiShat a = 1 ↔ a = 1 :=
  ⟨fun h => phiShat.injective (h.trans phiShat_one.symm), fun h => h ▸ phiShat_one⟩

@[expose] noncomputable def phiShatHom :
    Shat →* CFSG.Blueprint.NativeSporadic.B :=
  @MulEquiv.toMonoidHom Shat CFSG.Blueprint.NativeSporadic.B _ Units.instMulOneClass phiShat

@[expose] noncomputable def natCover
    (hG : Gmat = AutO) :
    cent tGriess →* CFSG.Blueprint.NativeSporadic.B :=
  @MonoidHom.comp (cent tGriess) Shat CFSG.Blueprint.NativeSporadic.B _ _ _ phiShatHom
    (centToShat hG)

theorem natCover_apply
    (hG : Gmat = AutO) (g : cent tGriess) :
    natCover hG g = phiShat (centToShat hG g) := rfl

theorem natCover_eq_one_iff
    (hG : Gmat = AutO) (g : cent tGriess) :
    natCover hG g = 1 ↔ (g : MGriess) = 1 ∨ (g : MGriess) = tGriess := by
  rw [natCover_apply, phiShat_eq_one_iff, centToShat_eq_one_iff]

theorem isBabyCover_natCover
    (hG : Gmat = AutO) : IsBabyCover tGriess (natCover hG) := by
  refine ⟨orderOf_tGriess, ?_, ?_⟩
  · exact phiShat.surjective.comp (centToShat_surjective hG)
  · ext y
    rw [mem_zpowers_iff_of_orderOf_eq_two orderOf_tGriess]
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (natCover_eq_one_iff hG g).1 hg
    · intro hy
      have hyc : y ∈ cent tGriess := by
        rcases hy with rfl | rfl
        · exact Subgroup.one_mem _
        · exact self_mem_cent tGriess
      exact ⟨⟨y, hyc⟩, (natCover_eq_one_iff hG ⟨y, hyc⟩).2 hy, rfl⟩

theorem exists_isBabyCover_tGriess
    (hcard : Nat.card MGriess = CFSG.Open.monsterOrder) :
    ∃ φ : ↥(cent tGriess) →* CFSG.Blueprint.NativeSporadic.B, IsBabyCover tGriess φ :=
  ⟨natCover (Gmat_eq_AutO hcard), isBabyCover_natCover (Gmat_eq_AutO hcard)⟩

end CFSG.Monster.Existence
