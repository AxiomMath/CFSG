
module

public import Certificates.Certificate8077Base1
import all Certificates.Certificate8077Base
import all Certificates.Certificate8077Base1

public import CFSG.Quasithin.Recognition.CertTitsBase
public import CFSG.Quasithin.Recognition.CertPermSimple
public import CFSG.Quasithin.Recognition.CertDataTitsSimple
public import Certificates.Data.CFSGNative.YGroups.ExactCheck
public import Certificates.Data.CFSGNative.Schreier.Check
public import CFSG.Quasithin.Recognition.CertTitsSimpleInputs
import CFSG.Sporadic.Schreier.TitsOuter
import CFSG.Quasithin.Recognition.CertTitsSimpleMainBase
import CFSG.Blueprint.Catalog
import Certificates.Kernel.Misc.Tits.Prim8077
import Certificates.Kernel.Misc.Tits.Strong8077
import Certificates.Kernel.TitsW.Alg
import Certificates.Kernel.Sporadic.Tits.GroupT2264
import Certificates.Kernel.Sporadic.OddCore.ChainCheckGlue
import CFSG.Certificates.Kernel.Misc.TitsPrimSound
import CFSG.Certificates.Kernel.Spor.RawOrbSound
import CFSG.Certificates.Kernel.Spor.StrongOfSound
import CFSG.Certificates.Kernel.Spor.Co2ChainSound
import CFSG.Certificates.Kernel.Spor.DecLinesRead
import CFSG.Certificates.Kernel.Spor.PresCardPG
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.YModel.Sound
import Certificates.Kernel.YModel.Basic
import CFSG.Certificates.Kernel.Common.Harness
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.TitsPrim
open CertificateChecks.KernelMisc CertificateChecks.KernelTitsW CertificateChecks.KernelSpor.Tits2264
open CertificateChecks.KernelMisc.TitsPrim8077 CertificateChecks.TitsStrong8077

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates
  CFSG.Certificates.Native in
theorem certificate8077 : (

    isInvA 1755 titsA (invCand 1755 titsA) = true ∧
    isInvA 1755 titsB (invCand 1755 titsB) = true ∧
    lettersOK titsGens.size (titsAbWords.getD 0 []) = true ∧
    lettersOK titsGens.size (titsAbWords.getD 1 []) = true ∧
    titsPairO.size ≤ titsPairStrong.size ∧
    (∀ i < titsPairO.size, titsPairStrong[i]! = titsPairO[i]!) ∧
    rawChainOK 1755 (titsPairStrong.extract 0 titsPairO.size) titsPairStrong
      (titsPairBase.map Fin.val).toArray titsPairRawWords 4 = true ∧
    rawOrbitSizes 1755 titsPairStrong (titsPairBase.map Fin.val).toArray =
      [1755, 10, 8, 2, 8, 4, 2] ∧
    primCheck 1755 titsPairStrong 0 titsLabels titsRoots 5 titsTw titsHw = true ∧
    eqA 1755 (powA 1755 titsA 2) (idA 1755) = true ∧ eqA 1755 titsA (idA 1755) = false ∧
    eqA 1755 (powA 1755 titsB 3) (idA 1755) = true ∧ eqA 1755 titsB (idA 1755) = false ∧
    eqA 1755 (powA 1755 (compA 1755 titsA titsB) 13) (idA 1755) = true ∧
    eqA 1755 (compA 1755 titsA titsB) (idA 1755) = false
)
    ∧ (LabelsDivisorOK 1755 5 (by norm_num) titsLabels ⟨0, by norm_num⟩) :=
  ⟨CertificateChecks.Batch8077.titsPair_check_0, CertificateChecks.Batch8077.labels_div⟩

end Certificates

end
