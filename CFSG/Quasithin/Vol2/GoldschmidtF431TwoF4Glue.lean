module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Zid
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsEnd
public import CFSG.Quasithin.Vol2.GoldschmidtF45RuMain
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Vol2.GoldschmidtF431TwoF4Iso

public section

namespace CFSG.Quasithin.H13.F431.TwoF4

open CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.H13.F45Ru CFSG.Sporadic.Schreier.Tits

local notation "TA" => CFSG.Sporadic.Schreier.Tits.titsA

set_option linter.unusedSectionVars false


@[expose] noncomputable def thetaM : ↥twoF4M ≃* twoF4Setting.ι.G0 :=
  (MulEquiv.subgroupCongr twoF4M_eq_titsA).trans
    (MulEquiv.ofBijective phiA ⟨phiA_injective, phiA_surjective⟩)

theorem toPerm_thetaM (y : ↥twoF4M) : toPerm (thetaM y) = y.1 := rfl

theorem toPerm_thetaM_symm (k : twoF4Setting.ι.G0) : (thetaM.symm k).1 = toPerm k := by
  rw [← toPerm_thetaM, MulEquiv.apply_symm_apply]

theorem mem_Mb1_iff (k : twoF4Setting.ι.G0) : k ∈ twoF4Setting.Mb1 ↔ toPerm k ∈ twoF4H := by
  rw [← mem_range_φ1_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem mem_Mb2_iff (k : twoF4Setting.ι.G0) : k ∈ twoF4Setting.Mb2 ↔ toPerm k ∈ twoF4N := by
  rw [← mem_range_φ2_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem Mb1_eq : twoF4Setting.Mb1 = twoF4M1.map thetaM.toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, mem_Mb1_iff]
  change _ ↔ (thetaM.symm k).1 ∈ twoF4H
  rw [toPerm_thetaM_symm]

theorem Mb2_eq : twoF4Setting.Mb2 = twoF4M2.map thetaM.toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, mem_Mb2_iff]
  change _ ↔ (thetaM.symm k).1 ∈ twoF4N
  rw [toPerm_thetaM_symm]

theorem twoF4_F431LieI_G0 : F431LieI (twoF4TT.map thetaM.toMonoidHom) twoF4Setting.Mb1
    twoF4Setting.Mb2 (thetaM zM) (thetaM tM) := by
  rw [Mb1_eq, Mb2_eq]
  exact F431LieI.map thetaM twoF4_F431LieI

end CFSG.Quasithin.H13.F431.TwoF4
