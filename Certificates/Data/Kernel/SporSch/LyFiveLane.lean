module

public import Certificates.Data.Kernel.SporSch.LyMat
public import CFSG.RankThree.Native.LyFiveData
public import CFSG.Certificates.CosetTableShort
public import CFSG.LinearAlgebra.SelfAdjointRankFactorization
public import CFSG.RankThree.Native.LyFaithful
public import CFSG.RankThree.Native.LyFiveDataBase
public import CFSG.RankThree.Native.LySeedCheckBase
public import CFSG.RankThree.Native.LySeedOperatorBase
public import CFSG.Sporadic.Bridge.LyData
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Presentation.Ly
public import Certificates.Certificate3085Base

public section

namespace CFSG.KC.LyFiveLane

open CFSG.RankThree.Native

@[expose] noncomputable def forceL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def stepL (mul pw : Nat → Nat → Nat) (r : List Nat) (ins : FiveIns) :
    List Nat :=
  FiveIns.casesOn (motive := fun _ => List Nat) ins
    (fun i j k => forceL (mul (r.getD i 0) (r.getD j 0)) (fun v => r.set k v))
    (fun e i k => forceL (pw (r.getD i 0) e) (fun v => r.set k v))

@[expose] noncomputable def runL (mul pw : Nat → Nat → Nat) (prog : List FiveIns) (r : List Nat) :
    List Nat :=
  prog.foldl (stepL mul pw) r

@[expose] def insIdxOK (n : Nat) : FiveIns → Bool
  | .mu i j k => decide (i < n) && decide (j < n) && decide (k < n)
  | .pwr _ i k => decide (i < n) && decide (k < n)

@[expose] def insOK (n : Nat) (prog : List FiveIns) : Bool := prog.all (insIdxOK n)

end CFSG.KC.LyFiveLane

end
