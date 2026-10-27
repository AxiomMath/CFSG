module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsFactsInputs
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs
import Certificates.Kernel.SporSch.Tits.Pairs4098

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Vol2Native CFSG.QuasithinUnique.Vol2Native.L239 CFSG.QuasithinUnique.Vol2Native.L239.Lie CFSG.QuasithinUnique.Vol2Native.L239.Lie.TitsPairs in
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
open CFSG.Sporadic.Schreier.Tits in
theorem certificate4098 : (isInvA 1755 aJ0 (invCand 1755 aJ0) = true ∧ isInvA 1755 aJ1 (invCand 1755 aJ1) = true ∧
          isInvA 1755 aJ2 (invCand 1755 aJ2) = true ∧ isInvA 1755 aK0 (invCand 1755 aK0) = true ∧
          isInvA 1755 aJy (invCand 1755 aJy) = true ∧ isInvA 1755 aKy1 (invCand 1755 aKy1) = true ∧
          isInvA 1755 aKy2 (invCand 1755 aKy2) = true ∧ isInvA 1755 aKy3 (invCand 1755 aKy3) = true ∧
          eqA 1755 (compA 1755 aJ0 aJ1) (compA 1755 aJ1 aJ0) = false ∧
          eqA 1755 (compA 1755 aK0 aJ0) (compA 1755 aJ0 aK0) = false ∧
          (titsCHJ.all fun c => eqA 1755 c (idA 1755) || eqA 1755 c aJc) = true ∧
          (titsCNK.all fun c => eqA 1755 c (idA 1755) || eqA 1755 c aKc1 || eqA 1755 c aKc2 ||
            eqA 1755 c aKc3) = true) := KernelSporSch.TitsPairs.facts

end Certificates
