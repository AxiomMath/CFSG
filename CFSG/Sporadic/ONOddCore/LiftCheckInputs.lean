module

public import CFSG.Sporadic.ONOddCore.LiftPayload
public import CFSG.Sporadic.ONOddCore.QuotOuterCheck
public import CFSG.Sporadic.Schreier.ONCheckAux
public meta import CFSG.Sporadic.ONOddCore.LiftPayload
public meta import CFSG.Sporadic.ONOddCore.QuotOuterCheck
public meta import CFSG.Sporadic.Schreier.ONCheckAux

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native

@[expose] def piWords : Array (List Nat) := #[[], [1], [2]]

@[expose] def piArr (g : Array Nat) : Array Nat :=
  pcomp 120 Data.quotientConjugator (pcomp 120 (bTab g) (pinvCand 120 Data.quotientConjugator))

@[expose] def base3Arr : Array Nat := #[0, 227759, 100817]

@[expose] def candImgs (lw : Array (Array Nat)) (a : Nat) : Array (Array Nat) :=
  #[pcomp nPts lw[0]! (qPowArr (a / 16)), pcomp nPts lw[1]! (qPowArr (a / 4 % 4)),
    pcomp nPts lw[2]! (qPowArr (a % 4))]

@[expose] def candOK (hA lw : Array (Array Nat)) (r : QuotRecord) (a : Nat) : Cand → Bool
  | .lift i => decide (i < r.lifts.length) &&
      allBelowN 3 fun j => peq nPts (posArr nPts hA ((r.lifts.getD i default).words.getD j []))
        (candImgs lw a)[j]!
  | .rel w w' => (w.all fun l => 1 ≤ l && l ≤ 3) && (w'.all fun l => 1 ≤ l && l ≤ 3) &&
      base3Arr.all (fun p => posPt hA w p == posPt hA w' p) &&
      base3Arr.any (fun p => posPt (candImgs lw a) w p != posPt (candImgs lw a) w' p)

@[expose] def candCheck (hA : Array (Array Nat)) (r : QuotRecord) (lwr : List (List Nat))
    (cs : List Cand) : Bool :=
  let lw := (lwr.map (posArr nPts hA)).toArray
  lwr.length == 3 && lwr.all (fun w => w.all fun l => 1 ≤ l && l ≤ 3) &&
    allBelowN 3 (fun i => blockImgOK lw[i]! Data.quotientBlocks (bTab lw[i]!) &&
      peq 120 (piArr lw[i]!) (posArr 120 #[qiArr r 0, qiArr r 1] piWords[i]!)) &&
    cs.length == 64 && (List.range 64).all fun a => candOK hA lw r a (cs.getD a default)

@[noinline, expose] def candidatesCheck (hA : Array (Array Nat)) : Bool :=
  liftData.qWord.all (fun l => 1 ≤ l && l ≤ 3) &&
    peq nPts (posArr nPts hA liftData.qWord) qArr && hA.size == 3 &&
    allBelowN 3 (fun i => blockImgOK hA[i]! Data.quotientBlocks (bTab hA[i]!) &&
      peq 120 (piArr hA[i]!) (posArr 120 #[qgArr 0, qgArr 1] piWords[i]!)) &&
    liftData.lw.length == 12 && liftData.cands.length == 12 &&
    (List.range 12).all fun k => candCheck hA (localCert.records.getD k default)
      (liftData.lw.getD k []) (liftData.cands.getD k [])

end CFSG.Sporadic.ONOddCore
