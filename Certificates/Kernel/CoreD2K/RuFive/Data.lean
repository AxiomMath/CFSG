module

public import CFSG.Certificates.Kernel.Common.Loop
public import Certificates.Data.CoreD2RuFiveOne
import Certificates.Kernel.Sporadic.OddCore.PEnumCmd
import Certificates.Kernel.Misc.Perm.HexCmd
import CFSG.Certificates.Kernel.Common.IntWords
meta import Certificates.Data.CoreD2RuFiveOne

namespace CertificateChecks.KernelCoreD2K.RuFive

open Certificates.CoreD2Perm

meta def gpM : Array (Array Nat) := gsT ruFiveLinesData.base
meta def gpiM : Array (Array Nat) := giT ruFiveLinesData.base
meta def gtM : Array (Array Nat) := gT ruFiveLinesData.base
meta def gtiM : Array (Array Nat) := gTi ruFiveLinesData.base
meta def egM : Array (Array Nat) := eGens ruFiveLinesData.base
meta def idT : Array Nat := CFSG.PSL3Four.Native.idTab 4060
meta def ewM : List (List Int) := ruFiveLinesData.base.eW
meta def gwM : List (List Int) := ruFiveLinesData.base.gWs
meta def waM : List (List Int) := ruFiveLinesData.wAs
meta def wbM : List (List Int) := ruFiveLinesData.wBs

end CertificateChecks.KernelCoreD2K.RuFive

public section

#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.GP CertificateChecks.KernelCoreD2K.RuFive.gpM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.GPI CertificateChecks.KernelCoreD2K.RuFive.gpiM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.GT CertificateChecks.KernelCoreD2K.RuFive.gtM 12
#kmisc_packarrs CertificateChecks.KernelCoreD2K.RuFive.GTI CertificateChecks.KernelCoreD2K.RuFive.gtiM 12

#kpenum CertificateChecks.KernelCoreD2K.RuFive.RE 4060 12 false
  CertificateChecks.KernelCoreD2K.RuFive.egM CertificateChecks.KernelCoreD2K.RuFive.egM
  CertificateChecks.KernelCoreD2K.RuFive.idT 125

#kc_intwords_list CertificateChecks.KernelCoreD2K.RuFive.EW CertificateChecks.KernelCoreD2K.RuFive.ewM
#kc_intwords_list CertificateChecks.KernelCoreD2K.RuFive.GW CertificateChecks.KernelCoreD2K.RuFive.gwM
#kc_intwords_list CertificateChecks.KernelCoreD2K.RuFive.WA CertificateChecks.KernelCoreD2K.RuFive.waM
#kc_intwords_list CertificateChecks.KernelCoreD2K.RuFive.WB CertificateChecks.KernelCoreD2K.RuFive.wbM

namespace CertificateChecks.KernelCoreD2K.RuFive

open Certificates.CoreD2Perm

@[expose] noncomputable def V : VData :=
  { ruFiveLinesData with
    base := { ruFiveLinesData.base with eW := EW, gWs := GW }
    wAs := WA
    wBs := WB }

end CertificateChecks.KernelCoreD2K.RuFive

end
