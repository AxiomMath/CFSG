module

import Certificates.Kernel.Sporadic.ON.Seven
public import CFSG.RankThree.Native.ONSevenArrays
public import CFSG.RankThree.Native.ONTripleTheory
public import CFSG.Sporadic.Schreier.ONVectorData

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple CFSG.ONSchreier
  CFSG.ONSchreier.Native Subgroup in
open scoped commutatorElement Pointwise in
theorem certificate8139 : (onSevenArr [6])[0]! = 0 ∧ (onSevenGood (onSevenArr [6]) []).length = 90 ∧
    onSevenCount (onSevenArr [6]) = 36 ∧
    peq N (pcomp N (onSevenArr [6]) (pcomp N (onSevenArr [6]) (onSevenArr [6]))) (pid N) = true ∧
    peq N (onSevenArr [6]) (pid N) = false :=
  KernelSpor.ON.seven_facts

end Certificates
