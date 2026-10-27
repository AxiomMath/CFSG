module

public import Certificates.Data.J4Ov.Fam
public import Certificates.Data.J4Ov.WordsMax

public section

namespace CFSG.Quasithin.J4Ov

open CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2

@[expose] def maxMats (ℓ : Nat) : Array (Array V2) := locMats () ++ #[uR ℓ]

@[expose] def maxInvs (ℓ : Nat) : Array (Array V2) := locInvs () ++ #[kR ℓ]

@[expose] def maxOK (ℓ k : Nat) (w : String) : Bool :=
  (frApply (frTable (wordRows (maxMats ℓ) (maxInvs ℓ) (decodeWord w))) (rV k)).beq rootV

end CFSG.Quasithin.J4Ov
