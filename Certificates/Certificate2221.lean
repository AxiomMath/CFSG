module

public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
import Certificates.Kernel.SporSch.Pair.HSFaith

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Certificates CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.PairNative CFSG.Sporadic.J1 in
open CFSG.Sporadic.J1.Native Matrix CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native in
open CFSG.Sporadic.Schreier.PairF2 in
theorem certificate2221 : hsFaithfulWith hsVectors hsStrongArrs CFSG.Sporadic.HS.Native.hsData.rowsA
    CFSG.Sporadic.HS.Native.hsData.rowsB = true := KernelSporSch.PHSFaith.facts

end Certificates
