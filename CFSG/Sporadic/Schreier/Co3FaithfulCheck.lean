module

public import CFSG.Sporadic.Schreier.Co3Cert
public import CFSG.Sporadic.Schreier.Co3FaithfulData
public import Certificates.Data.CFSGNative.Co3.Data
public meta import CFSG.Sporadic.Schreier.Co3Cert
public meta import CFSG.Sporadic.Schreier.Co3FaithfulData
public meta import Certificates.Data.CFSGNative.Co3.Data
public import CFSG.Sporadic.Schreier.Co3FaithfulCheckInputs
public import Certificates.Certificate2153

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Co3.Native CFSG.Sporadic.SmallF2.Native

theorem co3Faithful_check :
    (∀ r < 276, ∀ r' < r, co3FormWord r ≠ co3FormWord r') ∧
    (∀ r < 276, offDiagOK (co3FormWord r) (co3FormWord 0) = true) ∧
    (∀ r < 276, (co3ChainArrs[0]!)[r]! < 276 ∧
      pullOK CFSG.Sporadic.Co3.Native.co3Data.rowsA (co3FormWord r)
        (co3FormWord (co3ChainArrs[0]!)[r]!) = true) ∧
    (∀ r < 276, (co3ChainArrs[1]!)[r]! < 276 ∧
      pullOK CFSG.Sporadic.Co3.Native.co3Data.rowsB (co3FormWord r)
        (co3FormWord (co3ChainArrs[1]!)[r]!) = true) ∧
    mulRows 22 co3SpanCoeffs co3DiffRows = idRows 22 :=
  Certificates.certificate2153.1

theorem co3Seed_check :
    powRows 22 CFSG.Sporadic.Co3.Native.co3Data.rowsA 3 = idRows 22 ∧
    powRows 22 CFSG.Sporadic.Co3.Native.co3Data.rowsB 4 = idRows 22 :=
  Certificates.certificate2153.2

end CFSG.Sporadic.Schreier.Co3
