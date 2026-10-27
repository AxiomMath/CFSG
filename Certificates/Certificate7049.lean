
module

public import CFSG.Quasithin.Recognition.RuRank3Tits13Inputs
import Certificates.Kernel.Misc.Tits.E07049

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuRank3 CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier in
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native in
open scoped Pointwise in
theorem certificate7049 :
    isInvA 1755 titsX13Arr (invCand 1755 titsX13Arr) = true ∧ inTitsA titsX13Arr = true ∧
      eqA 1755 (powArr 1755 titsX13Arr 13) (idA 1755) = true ∧
      eqA 1755 titsX13Arr (idA 1755) = false ∧ ptFixCount titsX13Arr = 0 ∧
      lineFixCount titsX13Arr = 0 ∧
      ruChainOK 1755 titsP3Gens 3 3 [0] [] = true ∧
      rawOrbitSizes 1755 titsP3Gens (ruBaseArr 1755 [0]) = [27] ∧
      ruChainOK 1755 titsP5Gens 2 2 [0] [] = true ∧
      rawOrbitSizes 1755 titsP5Gens (ruBaseArr 1755 [0]) = [25] ∧
      (allLt 3 fun k => inTitsA titsP3Gens[k]! &&
        isInvA 1755 titsP3Gens[k]! (invCand 1755 titsP3Gens[k]!)) = true ∧
      (allLt 2 fun k => inTitsA titsP5Gens[k]! &&
        isInvA 1755 titsP5Gens[k]! (invCand 1755 titsP5Gens[k]!)) = true ∧
      listClosedA 1755 titsP3Gens (closureList 1755 titsP3Gens 30) = true ∧
      listClosedA 1755 titsP5Gens (closureList 1755 titsP5Gens 30) = true ∧
      ((closureList 1755 titsP3Gens 30).all fun e =>
        eqA 1755 e (idA 1755) || lineFixCount e == 9) = true ∧
      ((closureList 1755 titsP5Gens 30).all fun e =>
        eqA 1755 e (idA 1755) || ptFixCount e == 5) = true ∧
      lineFixCount titsZArr = 45 ∧ lineFixCount titsTArr = 61 := KernelMisc.T7049.c7049

end Certificates
