module

public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDZid
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDDatum
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442Map
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsGeoDAct
public import CFSG.Quasithin.Vol2.GoldschmidtF431TitsDIso

public section

namespace CFSG.Quasithin.H13.F431.TitsD

open CFSG.Quasithin CFSG.Quasithin.TitsGeo CFSG.Sporadic.Schreier.Tits

set_option linter.unusedSectionVars false


@[expose] noncomputable def thetaD : ↥titsD ≃* titsSetting.ι.G0 :=
  MulEquiv.ofBijective phiD ⟨phiD_injective, phiD_surjective⟩

theorem toPermD_thetaD (y : ↥titsD) : toPermD (thetaD y) = y.1 := rfl

theorem toPermD_thetaD_symm (k : titsSetting.ι.G0) : (thetaD.symm k).1 = toPermD k := by
  rw [← toPermD_thetaD, MulEquiv.apply_symm_apply]

theorem mem_Mb1_iff_D (k : titsSetting.ι.G0) : k ∈ titsSetting.Mb1 ↔ toPermD k ∈ titsH := by
  rw [← TitsGeo.mem_range_φ1_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem mem_Mb2_iff_D (k : titsSetting.ι.G0) : k ∈ titsSetting.Mb2 ↔ toPermD k ∈ titsN := by
  rw [← TitsGeo.mem_range_φ2_iff]
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩

theorem Mb1_eq_D : titsSetting.Mb1 = titsHD.map thetaD.toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, mem_Mb1_iff_D, Subgroup.mem_subgroupOf, toPermD_thetaD_symm]

theorem Mb2_eq_D : titsSetting.Mb2 = titsND.map thetaD.toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, mem_Mb2_iff_D, Subgroup.mem_subgroupOf, toPermD_thetaD_symm]

theorem titsD_F431LieI_G0 : F431LieI (titsSD.map thetaD.toMonoidHom) titsSetting.Mb1
    titsSetting.Mb2 (thetaD zD) (thetaD tD) := by
  rw [Mb1_eq_D, Mb2_eq_D]
  exact F431LieI.map thetaD titsD_F431LieI

theorem titsD_Loc442Datum_G0 : Loc442Datum titsSetting.Mb1 titsSetting.Mb2
    (titsSD.map thetaD.toMonoidHom) (thetaD zD) (thetaD tD) (VD.map thetaD.toMonoidHom)
    (thetaD qD) := by
  rw [Mb1_eq_D, Mb2_eq_D]
  exact Loc442Datum.map thetaD titsD_Loc442Datum

end CFSG.Quasithin.H13.F431.TitsD
