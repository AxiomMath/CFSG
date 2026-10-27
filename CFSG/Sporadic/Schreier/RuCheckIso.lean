module

public import CFSG.Sporadic.Schreier.RuArrays
public import Certificates.Data.CFSGNative.Ru.Data
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import Certificates.Data.CFSGNative.Ru.Data
public import CFSG.Sporadic.Schreier.RuCheckIsoInputs
public import Certificates.Certificate2251

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.SmallF2.Native

theorem ruIso_check :
    isInvA 4060 ruSigmaA (invCand 4060 ruSigmaA) = true ∧
    (∀ i < 4060, ruSigmaA[ruA0A[i]!]! =
        ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).alpha ruSigmaA[i]! ∧
      ruSigmaA[ruA1A[i]!]! = ap (CFSG.Sporadic.Ru.Native.ruData.orbit ()).beta ruSigmaA[i]!) :=
  Certificates.certificate2251

end CFSG.Sporadic.RuSchreier
