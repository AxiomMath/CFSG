module

public import Certificates.Data.CFSGNative.Filter.HeData
import CFSG.Certificates.Kernel.OpsLayKSoundP
import Certificates.Kernel.LocalComp.Fp.He
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
theorem certificate5032 : (opsP 7 50).secCheck heSec = true :=
  CFSG.KC.OpsLayK.secKP_sound He.lay_ok rfl rfl He.decA He.decB
    ((rfl : heSec.seedA = CFSG.Blueprint.NativeSporadic.HeSeed1).trans He.LA_eq)
    ((rfl : heSec.seedB = CFSG.Blueprint.NativeSporadic.HeSeed2).trans He.LB_eq) He.sec_K

end Certificates
