module

public import CFSG.Quasithin.H13.J4SecondLocal
public import Certificates.Data.CFSGNative.H13.J4Local
public meta import Certificates.Data.CFSGNative.H13.J4Local
public meta import Certificates.Data.CFSGNative.H13.J4Data
public meta import CFSG.Quasithin.H13.J4Image
public import CFSG.Quasithin.H13.J4OrderBase

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 CFSG.Quasithin.H13.J4.Native

@[expose] def normalThreeWord : List ℤ := [2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1]

@[expose] def firstBaseWord : List ℤ := [1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2]

@[expose] def secondBaseWord : List ℤ := [1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2]

@[expose] def secondConjugatorWord : List ℤ := [1, -2, 1, -2]

@[expose] def zPair : Pr12 := pr12Pow (pr12Word uvPairs12 normalThreeWord) 11

@[expose] def hPair : Pr12 := pr12Word uvPairs12 secondConjugatorWord

@[expose] def xPair : Pr12 := pr12Pow (pr12Word uvPairs12 firstBaseWord) 12

@[expose] def yPair : Pr12 :=
  pr12Mul (pr12Mul (pr12Inv hPair) (pr12Pow (pr12Word uvPairs12 secondBaseWord) 6)) hPair

@[expose] def localChecks : Bool :=
  let U := uvPairs12[0]?.getD pr12One
  let V := uvPairs12[1]?.getD pr12One
  rows12Ne zPair.1 (CFSG.Sporadic.SmallF2.Native.idRows 12) &&
    (pr12Pow zPair 3).1 == CFSG.Sporadic.SmallF2.Native.idRows 12 &&
    (pr12Mul (pr12Mul U zPair) (pr12Inv U)).1 == zPair.2 &&
    (pr12Mul V zPair).1 == (pr12Mul zPair V).1 &&
    (pr12Mul xPair zPair).1 == (pr12Mul zPair xPair).1 &&
    (pr12Mul yPair zPair).1 == (pr12Mul zPair yPair).1 &&
    (pr12Pow xPair 2).1 == CFSG.Sporadic.SmallF2.Native.idRows 12 &&
    (pr12Pow yPair 4).1 == CFSG.Sporadic.SmallF2.Native.idRows 12 &&
    (pr12Pow (pr12Mul xPair yPair) 11).1 == zPair.1 &&
    rows12Ne xPair.1 (CFSG.Sporadic.SmallF2.Native.idRows 12)

end CFSG.Quasithin.H13.J4
