module

public import CFSG.GH74.E2.CompCertsJ2Inputs
import CFSG.Certificates.Kernel.OpsLayKSoundP
import Certificates.Kernel.LocalComp.Fp.J2K
import Certificates.Kernel.LocalComp.Fp.J2Glue
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.KD.LC.Fp

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.E2 in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native CFSG.GH74.Generic in
theorem certificate5006 : (opsP 5 14).secCheck j2Sec = true := by
  rw [← J2D.j2SecK_eq]
  exact CFSG.KC.OpsLayK.secKP_sound J2K.lay_ok rfl rfl J2K.decA J2K.decB
    ((rfl : J2D.j2SecK.seedA = CFSG.Blueprint.NativeSporadic.J2Seed1).trans J2K.LA_eq)
    ((rfl : J2D.j2SecK.seedB = CFSG.Blueprint.NativeSporadic.J2Seed2).trans J2K.LB_eq) J2K.sec_K

end Certificates
