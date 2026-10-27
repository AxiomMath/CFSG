module

public import CFSG.Sporadic.SmallOddCore.McLWords
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import CFSG.Sporadic.SmallOddCore.McLWords
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
import Certificates.Kernel.SporSch.PairBT.McL2285K

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier in
open CFSG.Sporadic.Schreier.PairNative in
theorem certificate2285 : countPair PairMcL.bs 5 PairMcL.wA mclWConds PairMcL.blocks = 80640 := KernelSporSch.McL2285K.facts2285

end Certificates
