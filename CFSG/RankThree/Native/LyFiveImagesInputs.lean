module

public import CFSG.RankThree.Native.LyFiveArrays
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.RankThree.Native.LyFiveArrays
public meta import CFSG.RankThree.Native.LyFiveData
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.LinearAlgebra.SelfAdjointRankFactorization
public import CFSG.LinearAlgebra.SelfAdjointRankFactorization
public meta import CFSG.RankThree.Native.LyFaithful
public import CFSG.RankThree.Native.LyFaithful
public import CFSG.RankThree.Native.LyFiveData
public meta import CFSG.RankThree.Native.LyFiveDataBase
public import CFSG.RankThree.Native.LyFiveDataBase
public meta import CFSG.RankThree.Native.LySeedCheckBase
public import CFSG.RankThree.Native.LySeedCheckBase
public meta import CFSG.RankThree.Native.LySeedOperatorBase
public import CFSG.RankThree.Native.LySeedOperatorBase
public import CFSG.Sporadic.Bridge.LyData
public meta import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public meta import CFSG.Sporadic.Bridge.TableSurj
public meta import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public meta import CFSG.Sporadic.Presentation.Ly
public meta import Certificates.Certificate3085Base
public import Certificates.Certificate3085Base

public section

namespace CFSG.RankThree.Native

@[expose] def fiveArr4 (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) : Array (ZMod 5) :=
  Array.ofFn fun t : Fin 16 => M ⟨t.val / 4, by omega⟩ ⟨t.val % 4, by omega⟩

@[expose] def fiveMul4 (X Y : Array (ZMod 5)) : Array (ZMod 5) :=
  Array.ofFn fun t : Fin 16 =>
    ∑ l : Fin 4, X[4 * (t.val / 4) + l.val]! * Y[4 * l.val + t.val % 4]!

@[expose] def lyFiveTbStep (k : ℕ) (acc : Array (Array (ZMod 5))) : Array (ZMod 5) :=
  if k = 0 then fiveArr4 1 else
    fiveMul4 (fiveArr4 (if lyFiveGenArr[k]! = 1 then lyFiveBbar else lyFiveAbar))
      acc[lyFiveParArr[k]!]!

@[expose] def lyFiveTbArr : Array (Array (ZMod 5)) :=
  Nat.fold 2880 (fun k _ acc => acc.push (lyFiveTbStep k acc)) #[]

end CFSG.RankThree.Native
