module

public import Certificates.Kernel.CF23L34.SuzData
public import Certificates.Kernel.Sporadic.OddCore.Suz2302
public import Certificates.Data.Kernel.CF23L34.Word
public import CFSG.Certificates.Kernel.Common.EachTrue
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000
set_option Elab.async false

namespace CertificateChecks.KernelLC.CF23Suz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.CF23L34
open CFSG.LieType.Multipliers.L34 CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore

@[expose] def suzWs : List (List (Fin 2 × Bool)) := coverWs ++ [zOne, zTwo, zThree]

@[expose] noncomputable def suzEv (x : List (Fin 2 × Bool)) : Nat :=
  evK 1782 11 SuzFus.F SuzFusI x

@[expose] noncomputable def genK (i : Nat) : Bool :=
  bAnd(Nat.beq (pinvS 1782 11 (mask 11) (SuzFus.F i)) (SuzFusI i),
    bAnd(permOK 1782 11 (mask 11) (1782 * 11) (SuzFus.F i) (SuzFusI i), msift (SuzFus.F i)))

@[expose] noncomputable def wordK (i : Nat) : Bool :=
  Nat.beq (suzEv (suzWs.getD i [])) (pidn 1782 11)

@[expose] noncomputable def restK : Bool :=
  bAnd(permOK 1782 11 (mask 11) (1782 * 11) (SuzTP 0) (pinvS 1782 11 (mask 11) (SuzTP 0)),
  bAnd(commK 1782 11 (mask 11) (1782 * 11) (SuzFus.F 0) (SuzTP 0),
  bAnd(commK 1782 11 (mask 11) (1782 * 11) (SuzFus.F 1) (SuzTP 0),
  bAnd(Nat.beq (pcomp 1782 11 (mask 11) (pcomp 1782 11 (mask 11) (SuzFus.F 2) (SuzTP 0))
      (SuzFusI 2)) (pcomp 1782 11 (mask 11) (SuzTP 0) (SuzFus.F 0)),
    bIf(Nat.beq (SuzFus.F 0) (pidn 1782 11), false, true)))))

theorem ch22223_gen : allN 3 genK = true := by quickRfl

theorem ch22223_rest : restK = true := by quickRfl

theorem ch22223_len : suzWs.length = 23 := by decide +kernel

end CertificateChecks.KernelLC.CF23Suz

#kc_each CertificateChecks.KernelLC.CF23Suz ch22223w_ CertificateChecks.KernelLC.CF23Suz.wordK 0 23

namespace CertificateChecks.KernelLC.CF23Suz

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KC.CF23L34
open CertificateChecks.KernelSpor CertificateChecks.KernelSpor.OddCore CFSG.LieType.Multipliers.L34

theorem ch22223n_inv :
    bIf(Nat.beq (pinvS 1782 11 (mask 11) (SuzFus.F 0)) (SuzFusI 1), false, true) = true := by
  quickRfl

theorem ch22223n_comm :
    bIf(commK 1782 11 (mask 11) (1782 * 11) (SuzFus.F 2) (SuzTP 0), false, true) = true := by
  quickRfl

theorem ch22223n_word : bIf(Nat.beq (suzEv (zOne.drop 1)) (pidn 1782 11), false, true) = true := by
  quickRfl

end CertificateChecks.KernelLC.CF23Suz

end
