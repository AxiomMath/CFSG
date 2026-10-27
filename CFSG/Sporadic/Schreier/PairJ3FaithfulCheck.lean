module

public import CFSG.Sporadic.Schreier.PairJ3Cert
public import CFSG.Sporadic.Schreier.PairF2Sep
public import Certificates.Data.CFSGNative.J3.Data
public meta import CFSG.Sporadic.Schreier.PairJ3Cert
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.J3.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairJ3FaithfulCheckInputs
public import Certificates.Certificate2239

public section

namespace CFSG.Sporadic.Schreier.PairJ3

open CFSG.Sporadic.Schreier.PairF2 CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

theorem forms_check : formsCheckWith j3FormsHex.toUTF8 j3StrongArrs rowsA1 rowsA2 = true :=
  Certificates.certificate2239.1

theorem distinct_check : PairNative.strictInc (sortedWords j3FormsHex.toUTF8) = true :=
  Certificates.certificate2239.2.1

theorem inv_check :
    pullOKZ 80 rowsA1 j3InvWord j3InvWord = true ∧ pullOKZ 80 rowsA2 j3InvWord j3InvWord = true ∧
      mulRows 80 BInv BRows = idRows 80 :=
  Certificates.certificate2239.2.2.1

theorem sep_check : sepCheckWith TRows = true :=
  Certificates.certificate2239.2.2.2

end CFSG.Sporadic.Schreier.PairJ3
