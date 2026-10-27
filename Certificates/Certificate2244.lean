module

public import CFSG.Sporadic.Schreier.PairMcLFaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import Certificates.Data.CFSGNative.J1.Vec
public meta import Certificates.Data.CFSGNative.F3.Sep
public meta import Certificates.Data.CFSGNative.McL.Certificate
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import Certificates.Kernel.SporSch.Pair.McLFaith

public section

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Monster.B.Co2
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1
open CFSG.Sporadic.J1.Native Matrix CFSG.F3.Native

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 in
open CFSG.Sporadic.J1.Native Matrix CFSG.F3.Native in
theorem certificate2244 : mclFaithfulWith mclVectors mclStrongArrs CFSG.Sporadic.McL.Native.matA
    CFSG.Sporadic.McL.Native.matB = true := KernelSporSch.PMcLFaith.facts

end Certificates
