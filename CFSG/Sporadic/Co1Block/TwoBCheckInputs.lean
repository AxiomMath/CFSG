module

public import CFSG.Sporadic.Co1Block.TwoBData
public import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co1Block.TwoBData
public meta import CFSG.Sporadic.Co1Block.TwoBCheckDefs
public meta import CFSG.Sporadic.Co1Block.CentCheck
public meta import CFSG.Sporadic.Schreier.TitsBasic
public meta import CFSG.Sporadic.Co2Schreier.ThirdCheck
public meta import CFSG.Sporadic.Schreier.Co1ChainCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.Co1.Involutions
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.Schreier.Merge
public meta import Certificates.Data.CFSGNative.ONSchreier.Compact
public import CFSG.Sporadic.Co1Block.CentCheck
public import CFSG.Sporadic.Co2Schreier.ThirdCheck
public import CFSG.Sporadic.Schreier.Co1ThreeLocal
public import Certificates.Data.CFSGNative.Schreier.Merge

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.ONSchreier.Native CFSG.Sporadic.Co1Block.Native

@[expose] def twoBXYRows : Rows × Rows :=
  let D₂ := dag (brayElts (brayRows aR twoBD1) twoBBray) twoBD2
  (D₂.1.getD twoBXY.1 one, D₂.1.getD twoBXY.2 one)

@[expose] def twoBStrong : Array (Array Nat) :=
  let tab := triTable twoBTris
  extendTri (triPerm tab twoBTris twoBXYRows.1) (triPerm tab twoBTris twoBXYRows.2) twoBChainWords

@[noinline, expose] def twoBTriCheckOf (T : List (Nat × Nat)) (S : Array (Array Nat))
    (Bm : List Rows) (Rx Ry : Rows) (base : Array Nat) (W : Array (List Int)) : Bool :=
  let tab := triTable T
  let X := triPerm tab T Rx
  let Y := triPerm tab T Ry
  let L := rawLevels 1365 S base
  trisOK T aR && tableOK tab T && Bm.all (triOK tab T) && triOK tab T Rx && triOK tab T Ry &&
    S.size == 6 && eqA 1365 S[0]! X && eqA 1365 S[1]! Y &&
    rawChainOK 1365 (S.extract 0 2) S base W 4 && rawOrbitSizes 1365 S base == [1365, 1024, 180] &&
    isPrimeOrderA 1365 X 2 && isPrimeOrderA 1365 Y 5 && isPrimeOrderA 1365 (compA 1365 X Y) 13 &&
    Bm.all fun g =>
      let σ := triPerm tab T g
      let σi := invCand 1365 σ
      isInvA 1365 σ σi && siftA 1365 L base 0 (compA 1365 (compA 1365 σ X) σi) &&
        siftA 1365 L base 0 (compA 1365 (compA 1365 σ Y) σi)

@[expose] def twoBHSteps : Array (Array Nat) :=
  ((levelIdx twoBStrong twoBChainBase.toArray 1).map fun j => twoBStrong[j]!).toArray

@[expose] def twoBHTrees : List CLevel := (0 :: twoBSubReps).map fun r => cbfs 1365 r twoBHSteps

@[noinline, expose] def twoBPrimCheckOf (S : Array (Array Nat)) (H : Array (Array Nat))
    (Ts : List CLevel) (reps : List Nat) : Bool :=
  twoBChainBase == [0, 1, 2] &&
    reps.all (fun x => decide (x < 1365) && x != 0 &&
      mergeOK 1365 (S.extract 0 2) 0 x (mergeSearch 1365 (S.extract 0 2) 0 x)) &&
    H.all (fun h => h[0]! == 0) &&
    ((0 :: reps).zip Ts).all (fun p => clevelOK 1365 p.1 H p.2) &&
    allLt 1365 fun z => Ts.any fun L => decide (L.pos[z]! < L.pts.size)

end CFSG.Sporadic.Co1Block
