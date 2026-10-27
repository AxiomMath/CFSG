module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Inputs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwoBD0Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Native

set_option compiler.extract_closed false

@[expose] def bD0Words : Array (List Nat) :=
  #[[11, 17, 3, 4, 2, 14, 11, 4, 14, 22, 16, 12, 8, 18, 17, 13, 16, 18, 17, 18, 17],
    [10, 2, 14, 3, 22, 17, 4, 7, 15, 12, 8, 16, 10, 16, 20, 12, 17, 17, 17, 18],
    [8, 12, 20, 2, 2, 13, 18, 14, 4, 13, 11, 12, 9, 10, 15, 19, 13, 19, 22, 20, 19, 16],
    [6, 0, 4, 8, 3, 19, 6, 14, 16, 10, 18, 15, 13, 14, 12, 20, 17, 22, 18, 20]]

@[expose] def bD0Conj : List Nat :=
  [2, 5, 2, 4, 0, 14, 7, 7, 4, 14, 17, 11, 18, 10, 20, 16, 19, 12, 17, 17, 19, 22, 20]

@[expose] def applyWPow (L : Array Table) (w : List Nat) : Nat → Nat → Nat
  | 0, p => p
  | n + 1, p => applyW L w (applyWPow L w n p)

@[expose] def bD0Img (L : Array Table) (a b c e t : Nat) : Nat :=
  applyWPow L bD0Words[0]! a (applyWPow L bD0Words[1]! b
    (applyWPow L bD0Words[2]! c (applyWPow L bD0Words[3]! e t)))

@[noinline, expose] def bD0CheckL (O : WOrbit) (L : Array Table) : Bool :=
  let T := (t3Tabs O L)[0]!
  (allIn 0 4 fun i => allIn 0 4 fun j => allIn 0 6 fun t =>
      applyW L bD0Words[i]! (applyW L bD0Words[j]! t) ==
        applyW L bD0Words[j]! (applyW L bD0Words[i]! t)) &&
    (allIn 0 4 fun i => allIn 0 6 fun t => applyWPow L bD0Words[i]! 3 t == t) &&
    (allIn 0 4 fun i => allIn 0 2 fun k =>
      applyW L bD0Words[i]! kleinPts[k]! == kleinPts[k]!) &&
    (allIn 0 3 fun a => allIn 0 3 fun b => allIn 0 3 fun c => allIn 0 3 fun e =>
      a + b + c + e == 0 || !(allIn 0 6 fun t => bD0Img L a b c e t == t)) &&
    (allIn 0 6 fun t =>
      applyW L bD0Conj (applyW L bD0Words[0]! t) == ap T (applyW L bD0Conj t))

@[expose] def bD0OK (O : WOrbit) : Bool := bD0CheckL O (chainLetters O)

@[noinline, expose] def babyTwoBD0Check (_ : Unit := ()) : Bool := bD0OK (orbitData ())

end CFSG.LocalAnalysis.GLTheoremA.H1017.BabyTwoBD0Native
