module

public import Certificates.Data.CFSGNative.Filter.HNData
import CFSG.Certificates.Kernel.OpsLayKSoundP
import Certificates.Kernel.LocalComp.Fp.HN
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic
public import CFSG.GH74.Filter.Witness

public section

namespace Certificates

open CFSG.SectionRank.Native CFSG.KD.LC.Fp

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Filter in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5030 : (opsP 5 133).secCheck hnSec = true :=
  CFSG.KC.OpsLayK.secKP_sound HN.lay_ok rfl rfl HN.decA HN.decB
    ((rfl : hnSec.seedA = CFSG.Blueprint.NativeSporadic.HNSeed1).trans HN.LA_eq)
    ((rfl : hnSec.seedB = CFSG.Blueprint.NativeSporadic.HNSeed2).trans HN.LB_eq) HN.sec_K

end Certificates
