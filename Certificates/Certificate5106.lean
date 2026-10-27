module

public import CFSG.GH74.Generic.NativeCertsInputs
import CFSG.Certificates.Kernel.OpsLayKSound
import CFSG.Certificates.Kernel.OpsLayKSoundP
import Certificates.Kernel.LocalComp.F3.McLSec
import Certificates.Kernel.LocalComp.Fp.Ly
public import CFSG.Blueprint.NativeSporadic
import all CFSG.Blueprint.NativeSporadic

public section

namespace Certificates

open CFSG.GH74.Generic CFSG.KD.LC

open CFSG in
open CFSG.GH74 in
open CFSG.GH74.Generic in
open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native in
theorem certificate5106 : ((ops3 21).secCheck mclSec = true)
    ∧ ((opsP 5 111).secCheck lySec = true) :=
  ⟨CFSG.KC.OpsLayK.secK_sound F3.McLSec.lay_ok rfl rfl F3.McLSec.decA F3.McLSec.decB
      ((rfl : mclSec.seedA = CFSG.Blueprint.NativeSporadic.McLSeed1).trans F3.McLSec.LA_eq)
      ((rfl : mclSec.seedB = CFSG.Blueprint.NativeSporadic.McLSeed2).trans F3.McLSec.LB_eq)
      F3.McLSec.sec_K,
    CFSG.KC.OpsLayK.secKP_sound Fp.Ly.lay_ok rfl rfl Fp.Ly.decA Fp.Ly.decB
      ((rfl : lySec.seedA = CFSG.Blueprint.NativeSporadic.LySeed1).trans Fp.Ly.LA_eq)
      ((rfl : lySec.seedB = CFSG.Blueprint.NativeSporadic.LySeed2).trans Fp.Ly.LB_eq)
      Fp.Ly.sec_K⟩

end Certificates
