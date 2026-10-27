module

public import CFSG.Sporadic.Schreier.PairMcLTotal2Inputs
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
import Certificates.Kernel.SporSch.PairBT.McLSylFactsK

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairMcL in
open CFSG.Sporadic.Schreier.PairNative in
theorem certificate2246 : (ordB bs (patW wA wB [false, true, true]) 12 = true ∧
      ordB bs (patW wA wB [false, true, false, true, true]) 14 = true ∧
      ordB bs (patW wA wB pat10) 10 = true
    )
    ∧ ((cl.map fun c => c.2.1.size * countPair bs 5 c.1 conds2 blocks).sum = 1796256000) := KernelSporSch.McLSylK.facts2246

end Certificates
