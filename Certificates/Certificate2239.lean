module

public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
import Certificates.Kernel.SporSch.PairJ3.F2239Facts

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairJ3 in
open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native in
theorem certificate2239 : (formsCheckWith j3FormsHex.toUTF8 j3StrongArrs rowsA1 rowsA2 = true)
    ∧ (PairNative.strictInc (sortedWords j3FormsHex.toUTF8) = true)
    ∧ (pullOKZ 80 rowsA1 j3InvWord j3InvWord = true ∧ pullOKZ 80 rowsA2 j3InvWord j3InvWord = true ∧
      mulRows 80 CFSG.Sporadic.Schreier.PairJ3.BInv BRows = idRows 80
    )
    ∧ (sepCheckWith TRows = true) := KernelSporSch.F2239.facts

end Certificates
