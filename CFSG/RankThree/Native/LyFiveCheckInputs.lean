module

public import CFSG.RankThree.Native.LyFiveArrays
public import CFSG.RankThree.Native.LySeedCheck
public meta import Certificates.Data.CFSGNative.Ly.Certificate
public meta import CFSG.Monster.B.Fischer.InducedData
public meta import CFSG.RankThree.Native.LyFiveArrays
public meta import CFSG.RankThree.Native.LyFiveData
public meta import CFSG.RankThree.Native.LySeedCheck
public meta import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.CosetTableShort
public meta import CFSG.LinearAlgebra.SelfAdjointRankFactorization
public import CFSG.LinearAlgebra.SelfAdjointRankFactorization
public meta import CFSG.RankThree.Native.LyFaithful
public import CFSG.RankThree.Native.LyFaithful
public import CFSG.RankThree.Native.LyFiveData
public meta import CFSG.RankThree.Native.LyFiveDataBase
public import CFSG.RankThree.Native.LyFiveDataBase
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
public import Certificates.Certificate3085Base
public meta import Certificates.Certificate3085Base

public section

namespace CFSG.RankThree.Native

open CFSG.Sporadic.He.Native CFSG.Sporadic.Ly.Native CFSG.Monster.B.Fischer

@[expose] def fiveStepArr (r : Array (Array (Array ℕ))) : FiveIns → Array (Array (Array ℕ))
  | .mu i j k => r.set! k (mulM 5 111 r[i]! r[j]!)
  | .pwr e i k => r.set! k (powM 5 111 r[i]! e)

@[expose] def fiveRunArr (prog : List FiveIns) (r : Array (Array (Array ℕ))) :
    Array (Array (Array ℕ)) :=
  prog.foldl fiveStepArr r

@[expose] def fiveInitArr : Array (Array (Array ℕ)) :=
  ((Array.replicate 65 (idM 111)).set! 1 matA).set! 2 matB

@[expose] def lyFiveRegsArr : Array (Array (Array ℕ)) := fiveRunArr lyFiveProg fiveInitArr

@[expose] def lyFiveAArr : Array (Array ℕ) := lyFiveRegsArr[1]!

@[expose] def lyFiveBArr : Array (Array ℕ) := lyFiveRegsArr[2]!

@[expose] def lyFiveAiArr : Array (Array ℕ) := powM 5 111 lyFiveAArr 24

@[expose] def lyFiveBiArr : Array (Array ℕ) := powM 5 111 lyFiveBArr 7

@[expose] def lyFiveXArr : Array (Array ℕ) := powM 5 111 lyFiveAArr 5

@[expose] def fiveLetterArr (z : ℤ) : Array (Array ℕ) :=
  if z = 1 then lyFiveAArr else if z = 2 then lyFiveBArr else if z = -1 then lyFiveAiArr
    else lyFiveBiArr

@[expose] def fiveWordArr (w : List ℤ) : Array (Array ℕ) :=
  w.foldl (fun acc z => mulM 5 111 acc (fiveLetterArr z)) (idM 111)

@[expose] def lyFiveVArr : Array (Array (Array ℕ)) :=
  Array.ofFn fun i : Fin 4 => fiveWordArr (lyFiveVWords i)

@[expose] def fiveNFDirect (c : ℕ) (e : Fin 4 → ℕ) : Array (Array ℕ) :=
  mulM 5 111 (mulM 5 111 (mulM 5 111 (mulM 5 111 (powM 5 111 lyFiveVArr[3]! (e 3))
    (powM 5 111 lyFiveVArr[2]! (e 2))) (powM 5 111 lyFiveVArr[1]! (e 1)))
    (powM 5 111 lyFiveVArr[0]! (e 0))) (powM 5 111 lyFiveXArr c)

@[expose] def lyFiveChkA25 : Bool := powM 5 111 lyFiveAArr 25 == idM 111

@[expose] def lyFiveChkX : Bool := lyNeId lyFiveXArr

@[expose] def lyFiveChkB8 : Bool := powM 5 111 lyFiveBArr 8 == idM 111

@[expose] def lyFiveChkB4 : Bool := lyNeId (powM 5 111 lyFiveBArr 4)

@[expose] def lyFiveChkBX : Bool :=
  mulM 5 111 lyFiveBArr lyFiveXArr == mulM 5 111 (powM 5 111 lyFiveXArr 2) lyFiveBArr

@[expose] def lyFiveChkV (i : Fin 4) : Bool :=
  (powM 5 111 lyFiveVArr[i.val]! 5 == idM 111) &&
    (mulM 5 111 lyFiveXArr lyFiveVArr[i.val]! == mulM 5 111 lyFiveVArr[i.val]! lyFiveXArr)

@[expose] def lyFiveChkComm (i j : Fin 4) : Bool :=
  mulM 5 111 (mulM 5 111 (mulM 5 111 lyFiveVArr[i.val]! lyFiveVArr[j.val]!)
    (powM 5 111 lyFiveVArr[i.val]! 4)) (powM 5 111 lyFiveVArr[j.val]! 4) ==
    powM 5 111 lyFiveXArr (lyFiveOmega i j).val

@[expose] def lyFiveChkConj (i : Fin 4) : Bool :=
  (mulM 5 111 lyFiveAArr lyFiveVArr[i.val]! ==
    mulM 5 111 (fiveNFDirect (lyFiveAlpha i).val fun j => (lyFiveAbar j i).val) lyFiveAArr) &&
  (mulM 5 111 lyFiveBArr lyFiveVArr[i.val]! ==
    mulM 5 111 (fiveNFDirect (lyFiveBeta i).val fun j => (lyFiveBbar j i).val) lyFiveBArr)

@[expose] def lyFiveSmallCheck : Bool :=
  lyFiveChkA25 && lyFiveChkX && lyFiveChkB8 && lyFiveChkB4 && lyFiveChkBX &&
    (List.finRange 4).all lyFiveChkV &&
    (List.finRange 4).all (fun i => (List.finRange 4).all (lyFiveChkComm i)) &&
    (List.finRange 4).all lyFiveChkConj

@[expose] def lyFiveTreeCheck : Bool :=
  (lyFiveParArr.size == 2880) && (lyFiveGenArr.size == 2880) && (lyFiveNextArr.size == 5760) &&
    (lyFiveQArr.size == 5760) &&
    ((List.range 2880).all fun k => k == 0 || (decide (lyFiveParArr[k]! < k) &&
      decide (lyFiveGenArr[k]! < 2))) &&
    ((List.range 5760).all fun t => decide (lyFiveNextArr[t]! < 2880) &&
      decide (lyFiveQArr[t]! < 3125))

@[expose] def lyFiveVPow (i : ℕ) : Array (Array (Array ℕ)) :=
  Array.ofFn fun k : Fin 5 => powM 5 111 lyFiveVArr[i]! k

@[expose] def lyFiveVPow0 : Array (Array (Array ℕ)) := lyFiveVPow 0

@[expose] def lyFiveVPow1 : Array (Array (Array ℕ)) := lyFiveVPow 1

@[expose] def lyFiveVPow2 : Array (Array (Array ℕ)) := lyFiveVPow 2

@[expose] def lyFiveXPow : Array (Array (Array ℕ)) :=
  Array.ofFn fun c : Fin 5 => powM 5 111 lyFiveXArr c

@[expose] def lyFiveP3 : Array (Array (Array ℕ)) := lyFiveVPow 3

@[expose] def lyFiveP32 : Array (Array (Array ℕ)) :=
  Array.ofFn fun u : Fin 25 => mulM 5 111 lyFiveP3[u.val / 5]! lyFiveVPow2[u.val % 5]!

@[expose] def lyFiveP321 : Array (Array (Array ℕ)) :=
  Array.ofFn fun u : Fin 125 => mulM 5 111 lyFiveP32[u.val / 5]! lyFiveVPow1[u.val % 5]!

@[expose] def lyFiveP3210 : Array (Array (Array ℕ)) :=
  Array.ofFn fun u : Fin 625 => mulM 5 111 lyFiveP321[u.val / 5]! lyFiveVPow0[u.val % 5]!

@[expose] def lyFiveNFArr (q : ℕ) : Array (Array ℕ) :=
  mulM 5 111 lyFiveP3210[q / 5]! lyFiveXPow[q % 5]!

@[expose] def lyFiveTStep (k : ℕ) (acc : Array (Array (Array ℕ))) : Array (Array ℕ) :=
  if k = 0 then idM 111 else
    mulM 5 111 (if lyFiveGenArr[k]! = 1 then lyFiveBArr else lyFiveAArr) acc[lyFiveParArr[k]!]!

@[expose] def lyFiveTArr : Array (Array (Array ℕ)) :=
  Nat.fold 2880 (fun k _ acc => acc.push (lyFiveTStep k acc)) #[]

@[expose] def lyFiveRelOK (k s : ℕ) : Bool :=
  (lyFiveParArr[lyFiveNextArr[2 * k + s]!]! == k && lyFiveGenArr[lyFiveNextArr[2 * k + s]!]! == s &&
    lyFiveNextArr[2 * k + s]! != 0 && lyFiveQArr[2 * k + s]! == 0) ||
  (mulM 5 111 (if s = 1 then lyFiveBArr else lyFiveAArr) lyFiveTArr[k]! ==
    mulM 5 111 lyFiveTArr[lyFiveNextArr[2 * k + s]!]! (lyFiveNFArr lyFiveQArr[2 * k + s]!))

@[expose] def lyFiveRelsCheck : Bool :=
  (List.range 2880).all fun k => lyFiveRelOK k 0 && lyFiveRelOK k 1

end CFSG.RankThree.Native
