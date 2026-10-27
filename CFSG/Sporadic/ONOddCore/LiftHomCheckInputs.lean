module

public import CFSG.Sporadic.ONOddCore.LiftCheck
public meta import CFSG.Sporadic.ONOddCore.LiftCheck

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.PSL3Four.Native CFSG.Sporadic.ON.Native

@[expose] def liftArrs (hA : Array (Array Nat)) (e : LiftEntry) : Array (Array Nat) :=
  (e.words.map (posArr nPts hA)).toArray

@[expose] def liftPairGens (hA : Array (Array Nat)) (e : LiftEntry) : Array Tab :=
  #[dbl nPts hA[0]! (liftArrs hA e)[0]!, dbl nPts hA[1]! (liftArrs hA e)[1]!,
    dbl nPts hA[2]! (liftArrs hA e)[2]!]

@[expose] def liftRoot : Tab := dblBase nPts base3Arr

@[noinline, expose] def liftHomOK (hA : Array (Array Nat)) (e : LiftEntry) : Bool :=
  let gg := liftPairGens hA e
  let E := bfs (leftStep 6 gg) 3 liftRoot 200000
  treeOK (leftStep 6 gg) 3 liftRoot E && E.tabs.size == 161280 &&
    peq nPts (posArr nPts (liftArrs hA e) liftData.qWord) (qPowArr e.power)

end CFSG.Sporadic.ONOddCore
