module

public import CFSG.Sporadic.Co1Block.PermData
public import CFSG.Sporadic.Schreier.Co1StabFix
public import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import CFSG.Sporadic.Schreier.Co1StabFix
public meta import CFSG.Sporadic.Schreier.Co1StabCheck
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocal
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Data
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain

public section

namespace CFSG.Sporadic.Co1Block

open CFSG.Sporadic.SmallF2.Native CFSG.Monster.B.Co2.Native

@[expose] def certBasisRows (V : Array Nat) : Array Nat := (certBasisIdx.map fun i => V[i]!).toArray

@[noinline, expose] def permCheckOf (V T₀ T₁ RA RB : Array Nat) : Bool :=
  let pos := posTable 24 V
  let ca := transposeRows 24 RA
  let cb := transposeRows 24 RB
  V.size == 98280 && T₀.size == 98280 && T₁.size == 98280 &&
    V[0]! == CFSG.Sporadic.Co1Schreier.Native.stabVec 0 &&
    mulRows 24 (CFSG.Sporadic.Co1Schreier.Native.inv (certBasisRows V)) (certBasisRows V) ==
      idRows 24 &&
    allLt 98280 (fun i => decide (V[i]! < 2 ^ 24) && V[i]! != 0 && (pos[V[i]!]!).toNat == i &&
      vecMulN 24 ca V[i]! == V[T₀[i]!]! && vecMulN 24 cb V[i]! == V[T₁[i]!]!) &&
    isInvA 98280 T₀ (invCand 98280 T₀) && isInvA 98280 T₁ (invCand 98280 T₁)

end CFSG.Sporadic.Co1Block
