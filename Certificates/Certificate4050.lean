module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1J2CheckInputs
import CFSG.Certificates.Kernel.LocalQTPipeSound
import Certificates.Kernel.LocalQT.Pipe.C4050a
import Certificates.Kernel.LocalQT.Pipe.C4050s
import Certificates.Kernel.LocalQT.Pipe.C4050m
import Certificates.Kernel.LocalQT.Pipe.C4050e
import Certificates.Kernel.LocalQT.Pipe.C4050r
import Certificates.Kernel.LocalQT.Pipe.C4050b
import Certificates.Kernel.LocalQT.Pipe.C4050p
import Certificates.Kernel.LocalQT.Pipe.F4050
import CFSG.Certificates.Kernel.Common.Harness
public import Std.Data.HashMap

set_option maxRecDepth 100000

public section

namespace CFSG.QuasithinUnique.Setup.X1
open CFSG.QuasithinUnique.K1.SporadicPerm CFSG.KC.LQT.PP CFSG.KD.LQT.C4050

private theorem j2_treeValid : treeValid 4725 j2Data.par j2Data.gen := tree_sound 4725 parC genC hT

private theorem j2_invValid : invValid 315 j2Data.ta j2Data.tb j2Data.tai j2Data.tbi :=
  inv_sound (by decide) taC tbC taiC tbiC hI

private theorem j2_slpValid : slpValidAux j2Data.prog 2 = true := slpOKK_spec j2Data.prog 2 hso

private theorem j2_enum :
    qpOK 315 j2NT j2Data.qp ∧
    BaseEnumOK 315 (List.range 315) j2RG j2RGi j2Enum.1 j2Enum.2.1 j2Enum.2.2 ∧
    j2Enum.1.size = 2 ^ 7 :=
  enum_sound (n := 315) (w := 9) (by decide) taC tbC j2Data.prog j2Data.qp 7 100000 dR RL hE

private theorem j2_edgeOK :
    edgeOK 315 4725 (ptsOf (List.range 315) j2RG) j2Enum.1 j2Keys j2Data.ta
        j2Data.tb j2Data.Aa j2Data.Ab j2T j2U = true :=
  edge_sound (n := 315) (w := 9) (W := 13) (N := 4725) (by decide) (by decide) taC tbC taiC tbiC
    AaC AbC parC genC j2Data.prog j2Data.qp 7 100000 dR RL RF (TF 0) (TF 1) PRK GNK 15 315 hI hT
    hpt hgt hat hbt hE h0 h1 hPK hGK (by decide) E.all

private theorem j2_coset :
    blocksClosed j2ROm 4725 j2Data.Aa j2Data.Ab j2Data.par j2Data.gen j2Data.xs j2Blocks ∧
    repsOK j2ROm 4725 j2Data.repR j2Reps j2Orbs ∧
    closureOK j2ROm 4725 j2Data.Aa j2Data.Ab j2Data.par j2Data.gen j2Data.xs j2Blocks j2Reps ∧
    shapeOK 4725 j2Blocks :=
  coset_sound (N := 4725) (W := 13) (by decide) (by decide) AaC AbC parC genC repC j2Data.prog
    j2Data.qp j2Data.xs TF MF SL ML REPS OML BM BWL PWL PRK GNK RPK RIK QPK QGK DPK SH1 SH2 170 224
    5 945 6 432 hPa hPb h0 h1 hT hpt hgt hrt hPK hGK hRK hso hsn hq rfl S.all hid hM rfl M.all hRM
    hXM hrs (by decide) R.all rfl rfl B.all rfl P.all hsh

private theorem j2_xsOK : xsOK 4725 j2Data.xs := xs_sound 4725 j2Data.xs hX

private theorem j2_aszOK : aszOK 4725 j2Data.Aa j2Data.Ab := asz_sound 4725 AaC AbC hA

end CFSG.QuasithinUnique.Setup.X1

namespace Certificates

open CFSG.QuasithinUnique.Setup.X1 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.QuasithinUnique.K1.SporadicPerm in
theorem certificate4050 : (treeValid 4725 j2Data.par j2Data.gen)
    ∧ (invValid 315 j2Data.ta j2Data.tb j2Data.tai j2Data.tbi)
    ∧ (slpValidAux j2Data.prog 2 = true)
    ∧ (BaseEnumOK 315 (List.range 315) j2RG j2RGi j2Enum.1 j2Enum.2.1 j2Enum.2.2)
    ∧ (j2Enum.1.size = 128)
    ∧ (edgeOK 315 4725 (ptsOf (List.range 315) j2RG) j2Enum.1 j2Keys j2Data.ta
          j2Data.tb j2Data.Aa j2Data.Ab j2T j2U = true)
    ∧ (blocksClosed j2ROm 4725 j2Data.Aa j2Data.Ab j2Data.par j2Data.gen
          j2Data.xs j2Blocks)
    ∧ (CFSG.QuasithinUnique.Setup.X1.repsOK j2ROm 4725 j2Data.repR j2Reps j2Orbs)
    ∧ (CFSG.QuasithinUnique.Setup.X1.closureOK j2ROm 4725 j2Data.Aa j2Data.Ab j2Data.par j2Data.gen j2Data.xs
          j2Blocks j2Reps)
    ∧ (CFSG.QuasithinUnique.Setup.X1.shapeOK 4725 j2Blocks)
    ∧ (xsOK 4725 j2Data.xs)
    ∧ (qpOK 315 j2NT j2Data.qp)
    ∧ (aszOK 4725 j2Data.Aa j2Data.Ab) :=
  ⟨j2_treeValid, j2_invValid, j2_slpValid, j2_enum.2.1, j2_enum.2.2, j2_edgeOK, j2_coset.1,
    j2_coset.2.1, j2_coset.2.2.1, j2_coset.2.2.2, j2_xsOK, j2_enum.1, j2_aszOK⟩

end Certificates
