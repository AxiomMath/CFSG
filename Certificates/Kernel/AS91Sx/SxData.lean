module

public import Certificates.Kernel.SporSch.Mathieu.Gen
public import CFSG.Quasithin.H13.AS91Sec8V1AutData
public meta import CFSG.Quasithin.H13.AS91Sec8V1AutData
public import CFSG.Monster.B.Mathieu.Order
public meta import CFSG.Monster.B.Mathieu.Order
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAS91Sx.Sx664OC

open CFSG.KS.SporSch.MOCG

meta def tAM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList CFSG.Quasithin.H13.AS91.M24G.sxAT).toArray

meta def tBM : Array Nat :=
  (CFSG.Monster.B.Mathieu.imageList CFSG.Quasithin.H13.AS91.M24G.sxBT).toArray

meta def SM : Array (Array Nat) :=
  strongOf 24 #[tAM, tBM] CFSG.Quasithin.H13.AS91.M24G.sxChainWords

meta def baseM : Array Nat := #[0, 4, 5, 8, 1, 2]

meta def repsM : Array (Array Nat) := #[tAM]

meta def oneM : Array Nat := idA 24

end CertificateChecks.KernelAS91Sx.Sx664OC

#kss_list CertificateChecks.KernelAS91Sx.Sx664OC.tA CertificateChecks.KernelAS91Sx.Sx664OC.tAM

#kss_list CertificateChecks.KernelAS91Sx.Sx664OC.tB CertificateChecks.KernelAS91Sx.Sx664OC.tBM

#ks_rawchain CertificateChecks.KernelAS91Sx.Sx664Q 24 5 16 CertificateChecks.KernelAS91Sx.Sx664OC.SM
  CertificateChecks.KernelAS91Sx.Sx664OC.baseM 2 CFSG.Quasithin.H13.AS91.M24G.sxChainWords

namespace CertificateChecks.KernelAS91Sx.Sx664OC

@[expose] noncomputable def One : Nat := CFSG.KC.Enum.pidn 24 5

@[expose] noncomputable def R0 : Nat := CertificateChecks.KernelAS91Sx.Sx664Q.S 0

end CertificateChecks.KernelAS91Sx.Sx664OC

end
