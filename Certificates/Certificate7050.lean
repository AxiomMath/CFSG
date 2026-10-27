
module

public import Certificates.Certificate7050Base
import all Certificates.Certificate7050Base

public import CFSG.Quasithin.Recognition.RuRank3TitsClsInputs
public import CFSG.Quasithin.Recognition.RuRank3Tits13Base
import CFSG.Sporadic.Schreier.TitsCertCheckInputs
import Certificates.Kernel.EvenBN.CNtEq
import Certificates.Kernel.Misc.Tits.Cls7050S0
import Certificates.Kernel.Misc.Tits.Cls7050S1
import Certificates.Kernel.Misc.Tits.Cls7050S2
import Certificates.Kernel.Misc.Tits.Cls7050S3
import Certificates.Kernel.Misc.Tits.Cls7050S4
import Certificates.Kernel.Misc.Tits.Cls7050S5
import Certificates.Kernel.Misc.Tits.Cls7050S6
import Certificates.Kernel.Misc.Tits.Cls7050S7
import Certificates.Kernel.Misc.Tits.Cls7050S8
import Certificates.Kernel.Misc.Tits.Cls7050S9
import Certificates.Kernel.Misc.Tits.Cls7050S10
import Certificates.Kernel.Misc.Tits.Cls7050S11
import Mathlib.Tactic.IntervalCases
import Certificates.Kernel.Misc.Tits.Bad7050
import Certificates.Kernel.Misc.Tits.K0Use7050
import Certificates.Kernel.Sporadic.Tits.Order2264
import Certificates.Kernel.Misc.Tits.Pi7092
import CFSG.Certificates.Kernel.Spor.PackFld
import CFSG.Certificates.Kernel.Spor.RawOrbEval
import CFSG.Certificates.Kernel.Spor.RawSiftKConv
import CFSG.Certificates.Kernel.Spor.SiftRSound
import CFSG.Certificates.Kernel.Spor.RawSound
import CFSG.Certificates.Kernel.Spor.PackWord
import CFSG.Certificates.Kernel.Spor.PrimSound
import CFSG.Certificates.Kernel.BfsPinAlg
import CFSG.Sporadic.Schreier.TitsCert
import CFSG.Sporadic.Schreier.TitsCertCheck
import CFSG.Sporadic.Schreier.TitsChain

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped MatrixGroups
open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim
open CertificateChecks.KernelMisc CertificateChecks.KernelMisc.Tits7050
open CertificateChecks.KernelSpor.Tits2264 CertificateChecks.KernelSporSch
open CFSG.KS.Raw.Orb (bIf_eq unpack_get)

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
open scoped MatrixGroups in
theorem certificate7050 :
    isInvA 1755 titsAuxArr (invCand 1755 titsAuxArr) = true ∧ inTitsA titsAuxArr = true ∧
      inTitsD titsAuxArr = false ∧
      eqA 1755 (compA 1755 titsAuxArr titsTArr) (compA 1755 titsTArr titsAuxArr) = true ∧
      isInvA 1755 titsY12Arr (invCand 1755 titsY12Arr) = true ∧ inTitsA titsY12Arr = true ∧
      eqA 1755 (compA 1755 titsY12Arr titsTArr) (compA 1755 titsTArr titsY12Arr) = true ∧
      eqA 1755 (compA 1755 titsY12Arr titsX13Arr)
        (compA 1755 (powArr 1755 titsX13Arr 11) titsY12Arr) = true ∧
      (allLt 12 fun k => isInvA 1755 (powArr 1755 titsY12Arr k)
        (invCand 1755 (powArr 1755 titsY12Arr k))) = true ∧
      (titsCNt.all fun c => classOK c && classOK (compA 1755 titsAuxArr c)) = true ∧
      (allLt 30 fun i => isInvA 1755 (titsRepArr i) (invCand 1755 (titsRepArr i))) = true ∧
      titsRepGood.length = 30 ∧ titsBadWords.length = 30 ∧
      (allLt 30 fun i => if titsRepGood.getD i false then inTitsK0 (titsRepArr i) else
        badOK i) = true ∧
      ruChainOK 1755 titsK0Strong 3 5 [0, 12, 1] titsK0Words = true ∧
      rawOrbitSizes 1755 titsK0Strong (ruBaseArr 1755 [0, 12, 1]) = [975, 4, 2] ∧
      eqA 1755 titsK0Strong[0]! titsX13Arr = true ∧ eqA 1755 titsK0Strong[1]! titsTArr = true ∧
      inTitsA titsK0Strong[2]! = true ∧
      isInvA 1755 titsTArr (invCand 1755 titsTArr) = true ∧
      eqA 1755 (compA 1755 (compA 1755 (compA 1755 titsTArr titsX13Arr) titsTArr) titsX13Arr)
        (idA 1755) = true := by
  exact CertificateChecks.Batch7050.titsCls_check_0

end Certificates

end
