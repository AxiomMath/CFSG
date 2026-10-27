module

public import CFSG.Quasithin.Background.F7TwoInvSQTK
public import CFSG.Quasithin.Background.F7TwoInvL3Main
public import CFSG.Quasithin.Background.F7TwoInvU3OddMain
public import CFSG.Quasithin.Background.F7TwoInvL3TwoMain
public import CFSG.Quasithin.Background.F7TwoInvU3Two
public import CFSG.Quasithin.Background.F7TwoInvSp4Main
public import CFSG.Quasithin.Background.F7TwoInvG2
public import CFSG.Quasithin.Background.F7TwoInvD4
public import CFSG.Quasithin.Background.F7TwoInv2F4
public import CFSG.Quasithin.Background.F7TwoInvTits
public import CFSG.Quasithin.Background.F7TwoInvL5TwoMain
public import CFSG.Quasithin.Background.F7TwoInvSporFam
public import CFSG.Quasithin.Background.F7TwoInvSporM11
public import CFSG.Quasithin.Background.F7TwoInvSporM12
public import CFSG.Quasithin.Background.F7TwoInvSporM22
public import CFSG.Quasithin.Background.F7TwoInvSporM23
public import CFSG.Quasithin.Background.F7TwoInvSporM24
public import CFSG.Quasithin.Background.F7TwoInvSporJ1
public import CFSG.Quasithin.Background.F7TwoInvSporJ2
public import CFSG.Quasithin.Background.F7TwoInvSporHS
public import CFSG.Quasithin.Background.F7TwoInvSporHe
public import CFSG.Quasithin.Background.F7TwoInvSporRu
public import CFSG.Quasithin.Background.F7TwoInvSporJ4

public section

namespace CFSG.Quasithin.F7Two

theorem invAutGenFamL3Odd_proved :
    InvAutGenFamL3Odd := fun p _ _ _ hp hp2 h => by
  have : Fact p.Prime := ⟨hp⟩
  exact invAutGen_of_statedPSL3 hp2 h

theorem invAutGenFamU3Odd_proved : InvAutGenFamU3Odd := fun _ _ _ _ _ hp2 h =>
  invAutGen_of_statedPSU3 hp2 h

theorem invAutGenFamU3Even_proved : InvAutGenFamU3Even :=
  fun _ _ _ _ hf h => invAutGen_of_statedPSU_two hf h

theorem invAutGenFamSz_proved : InvAutGenFamSz :=
  fun _ _ _ _ _ _ h => invAutGen_of_suzukiModel h

theorem invAutGenSQTK_of_J4
    (hJ4 : InvAutGenCarrier .J4) : InvAutGenSQTK :=
  invAutGenSQTK_of_families invAutGenFamL3Odd_proved invAutGenFamU3Odd_proved invAutGenFamL3Even
    invAutGenFamU3Even_proved invAutGenFamSp4Even_proved G2Ev.invAutGenFamG2Even
    invAutGenFam3D4Even invAutGenFam2F4 invAutGenFamSz_proved invAutGenFamTits invAutGenFamL5Two
    (invAutGenFamSporadic_of_eleven invAutGen_carrier_M11 invAutGen_carrier_M12
      invAutGen_carrier_M22 invAutGen_carrier_M23 invAutGen_carrier_M24 invAutGen_carrier_J1
      invAutGen_carrier_J2 hJ4 invAutGen_carrier_HS invAutGen_carrier_He invAutGen_carrier_Ru)

theorem invAutGenSQTK_proved :
    InvAutGenSQTK :=
  invAutGenSQTK_of_J4 invAutGen_carrier_J4

end CFSG.Quasithin.F7Two
