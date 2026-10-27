module

public import Certificates.Data.J4Ov.Fam
public import Certificates.Data.J4Ov.WordsE

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def eConj (ℓ : Nat) : Array (Array V2) :=
  uBasis.map fun U => conjBy (uR ℓ) U (kR ℓ)

@[expose] def eMats (ℓ : Nat) : Array (Array V2) := uBasis ++ eConj ℓ

@[expose] def eOK (ℓ i : Nat) : Bool :=
  let e := eData.getD (3 * (ℓ - 1) + i) ("", 0)
  decide (e.2 < 2048) &&
    eqRows (mulRows (wordRows (eMats ℓ) (eMats ℓ) (decodeWord e.1)) ((locInvs ())[i]?.getD idRows))
      (etaRows uBasis 11 e.2)

end CFSG.Quasithin.J4Ov
