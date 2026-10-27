module

public import Certificates.Kernel.Sporadic.OddCore.MulHCmd
public import Certificates.Kernel.Sporadic.McLC.SylData
public meta import Certificates.Kernel.Sporadic.McLC.SylData
public meta import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch54SporMcLInputs
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CertificateChecks.KernelSpor.McLAsch

open CFSG.Sporadic.SmallOddCore.Native CFSG.PSL3Four.Native

meta def idM : Array Nat := idTab 275

meta def hM : Array (Array Nat) :=
  CFSG.LocalAnalysis.WeakClosure81.SporMcL.hgens.toArray.map natArr

meta def ids2 : Array (Array Nat) := Array.replicate 2 idM

meta def eM : Array (Array Nat) := hM.extract 0 2

meta def eiM : Array (Array Nat) := eM.map (CFSG.Monster.B.Co2.Native.invCand 275)

meta def recE : Array (Array Nat) := (bfs (fun j t => conjTab 275 idM eM[j]! t) 2 idM 50000).tabs

meta def clE : Array (Array Nat) := (recE.map fun x => (eM ++ eiM).map fun g => comp 275 x g).flatten

meta def kM : Array (Array Nat) := CFSG.ClassicalInvolution.McLData.kgens.toArray.map natArr

meta def kiM : Array (Array Nat) := kM.map (CFSG.Monster.B.Co2.Native.invCand 275)

meta def uM : Array Nat := natArr CFSG.LocalAnalysis.WeakClosure81.SporMcL.uTbl

meta def vM : Array (Array Nat) :=
  #[natArr CFSG.ClassicalInvolution.McLData.Ta, uM,
    comp 275 (natArr CFSG.ClassicalInvolution.McLData.Ta) uM]

end CertificateChecks.KernelSpor.McLAsch

#kmisc_packarrs CertificateChecks.KernelSpor.McLAHG CertificateChecks.KernelSpor.McLAsch.hM 9
#kmulh CertificateChecks.KernelSpor.McLAE 275 9 CertificateChecks.KernelSpor.McLAsch.ids2
  CertificateChecks.KernelSpor.McLAsch.eM CertificateChecks.KernelSpor.McLAsch.idM 50000
#kmisc_packarrs CertificateChecks.KernelSpor.McLAEI CertificateChecks.KernelSpor.McLAsch.eiM 9
#kfind CertificateChecks.KernelSpor.McLAECl CertificateChecks.KernelSpor.McLAsch.recE
  CertificateChecks.KernelSpor.McLAsch.clE
#kmulh CertificateChecks.KernelSpor.McLAU 275 9 CertificateChecks.KernelSpor.McLAsch.kM
  CertificateChecks.KernelSpor.McLAsch.kiM CertificateChecks.KernelSpor.McLAsch.uM 50000
#kfind CertificateChecks.KernelSpor.McLAV CertificateChecks.KernelSpor.McLCSyl.recM
  CertificateChecks.KernelSpor.McLAsch.vM

end
