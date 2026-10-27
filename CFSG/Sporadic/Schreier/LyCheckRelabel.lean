module

public import CFSG.Sporadic.Schreier.LyCheckSep
public import Certificates.Data.CFSGNative.LySchreier.Check

public section

namespace CFSG.Sporadic.LySchreier.Native

open CFSG.Sporadic.Ly.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def scaledOK (K K' : ByteArray) : Bool :=
  allIn 0 777 (fun p => keyDigit K' p == keyDigit K p) &&
    allIn 777 826 (fun p => keyDigit K' p == 4 * keyDigit K p % 5)

@[expose] def bpRootKeyF : ByteArray :=
  encodeDigits fun p => if p < 777 then bpRootArr[p]! else if p < 826 then 4 * bpRootArr[p]! else 0

@[expose] def bpStart (O : KOrbit) : Nat := O.index.getD bpRootKeyF O.keys.size

@[noinline, expose] def relChecks (O : KOrbit) : Bool :=
  let r := bpStart O
  let R := relabel nPts O.alpha O.beta r
  let bi := invT nPts R.beta
  let tab := seedTab R.alpha R.beta bi
  decide (r < nPts) && scaledOK bpRootKey O.keys[r]! && relabelOK nPts O.alpha O.beta r R &&
    relOrderOK nPts R && invOK nPts R.beta bi && fixedOK nPts R.alpha fixedIdx &&
    seedPermOK tab fixedIdx fixedPerm seedWord && transOK () &&
    wordAp tab transporterWord 0 == fixedIndex && ap R.alpha fixedIndex == fixedIndex &&
    sepKeys.size == 16 && allIn 0 16 (fun h => scaledOK sepKeys[h]! O.keys[ap R.pts sepIdx[h]!]!)

@[expose] def relCertificate (_ : Unit) : Bool := relChecks (orbitData ())

end CFSG.Sporadic.LySchreier.Native
