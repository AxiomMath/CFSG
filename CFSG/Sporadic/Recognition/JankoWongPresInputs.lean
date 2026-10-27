module

public import CFSG.Certificates.CosetTablePresented
public import Certificates.Data.CFSGNative.McL.Certificate
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Sporadic.Recognition.JankoWong

open CFSG.CosetTable CFSG.Sporadic.Th.Native CFSG.Sporadic.McL.Native CFSG.Sporadic.VecOrbit.Native

abbrev JWWord : Type := List (Fin 6 × Bool)

@[expose] def jwWg (i : Fin 6) : JWWord := [(i, true)]

@[expose] def jwWInv (w : JWWord) : JWWord := (w.map fun l => (l.1, !l.2)).reverse

@[expose] def jwWConj (x y : JWWord) : JWWord := jwWInv y ++ x ++ y

@[expose] def jwWComm (x y : JWWord) : JWWord := jwWInv x ++ jwWInv y ++ x ++ y

@[expose] def jwWPow (x : JWWord) : ℕ → JWWord
  | 0 => []
  | n + 1 => x ++ jwWPow x n

@[expose] def jwWA1 : JWWord := jwWg 0

@[expose] def jwWS1 : JWWord := jwWg 1

@[expose] def jwWU : JWWord := jwWg 2

@[expose] def jwWV : JWWord := jwWg 3

@[expose] def jwWF1 : JWWord := jwWg 4

@[expose] def jwWV1 : JWWord := jwWg 5

@[expose] def jwWB1 : JWWord := jwWConj jwWA1 jwWS1

@[expose] def jwWA2 : JWWord := jwWConj jwWA1 jwWU

@[expose] def jwWS2 : JWWord := jwWConj jwWS1 jwWU

@[expose] def jwWZ : JWWord := jwWPow jwWA1 2

@[expose] def jwWF2 : JWWord := jwWConj jwWF1 jwWV

@[expose] def jwWF3 : JWWord := jwWConj jwWF1 jwWA2

@[expose] def jwWF4 : JWWord := jwWConj jwWF2 jwWA2

@[expose] def jwPairs (neg : Bool) : List (JWWord × JWWord) :=
  [(jwWPow jwWS1 3, []),
   (jwWPow jwWB1 2, jwWZ),
   (jwWConj jwWA1 jwWV, jwWInv jwWA1),
   (jwWConj jwWB1 jwWS1, jwWA1 ++ jwWB1),
   (jwWPow jwWA2 2, jwWZ),
   (jwWConj jwWA2 jwWV, jwWInv jwWA2),
   (jwWConj jwWS2 jwWV, jwWInv jwWS2),
   (jwWComm jwWA1 jwWA2, []),
   (jwWComm jwWA1 jwWS2, []),
   (jwWComm jwWS1 jwWS2, []),
   (jwWPow jwWV 2, jwWZ),
   (jwWPow jwWU 2, []),
   (jwWConj jwWV jwWU, jwWInv jwWV),
   (jwWPow (jwWV1 ++ jwWA2) 3, []),
   (jwWPow (jwWV1 ++ jwWU) 2, jwWV),
   (jwWConj jwWF1 jwWZ, jwWInv jwWF1),
   (jwWConj jwWF1 jwWU, jwWF1),
   (jwWConj jwWF3 jwWS2, jwWInv jwWF1 ++ jwWF3 ++ jwWS1),
   (jwWConj jwWF1 jwWF3, jwWF1 ++ jwWInv jwWS1),
   (jwWComm jwWF1 jwWF4, []),
   (jwWPow (jwWU ++ jwWZ ++ jwWF3) 3, []),
   (jwWPow (jwWU ++ jwWV ++ jwWInv jwWF3 ++ jwWF4) 3, []),
   (jwWConj jwWF3 jwWV1,
    if neg then jwWS1 ++ jwWInv jwWF1 ++ jwWF3 ++ jwWF4
    else jwWInv jwWS1 ++ jwWInv jwWF1 ++ jwWInv jwWF3 ++ jwWInv jwWF4)]

@[expose] def jwRels (neg : Bool) : List JWWord :=
  (jwPairs neg).map fun p => p.1 ++ jwWInv p.2

abbrev jwRels5 (neg : Bool) := restrictWords (subsetOf 6 [0, 1, 2, 3, 4]) (jwRels neg)

abbrev jwRels4 (neg : Bool) := restrictWords (subsetOf _ [0, 1, 2, 3]) (jwRels5 neg)

@[expose] def jwEnum6 (neg : Bool) : Bool := subsetCheck (jwRels neg) [0, 1, 2, 3, 4] 200000 275

@[expose] def jwEnum5 (neg : Bool) : Bool := subsetCheck (jwRels5 neg) [0, 1, 2, 3] 200000 2835

@[expose] def jwEnum4 (neg : Bool) : Bool := subsetCheck (jwRels4 neg) [] 20000 1152

@[expose] def jwGenWord (neg : Bool) : ℕ → List ℤ
  | 0 => [2, 1, -2, 1, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1,
    2, 2, 1, 2, 1, 2]
  | 1 => [1, -2, 1, 2, 2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2, 1, -2,
    1, 2, 1, 2, 2, 1, 2]
  | 2 => if neg then [1, -2, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, -2,
      1, 2, 1, -2, 1, 2, 2]
    else [-2, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, -2, 1, 2, 1, -2, 1, 2, 2, 1, -2, -2, 1, 2, 1, -2,
      1, 2, 2]
  | 3 => [2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, -2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 1, -2, 1, -2,
    1, 2, 2, 1, -2, 1, -2, 1, 2, 2]
  | 4 => if neg then [-2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, -2, -2, 1, -2, -2,
      1, 2, 1, 2, 1, 2, 1]
    else [1, 2, 1, 2, 2, 1, -2, -2, 1, -2, -2, 1, 2, 2, 1, 2, 2, 1, -2, -2, 1, -2]
  | 5 => [2, 1, -2, -2, 1, -2, 1, 2, 2, 1, -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, -2, 1, 2, 1, -2, 1,
    -2, 1, -2, -2, 1, -2, -2, 1, 2]
  | _ => []

@[expose] def jwSurjACodes : List ℕ := [0, 0]

@[expose] def jwSurjBCodes (neg : Bool) : List ℕ :=
  if neg then [9, 0, 4, 2, 0, 11, 8, 0, 9, 2, 0, 4] else [6, 8, 0, 4, 3, 0, 11, 8, 0, 3, 8, 0, 4, 6]

@[expose] def jwOfCodes (c : List ℕ) : JWWord :=
  c.map fun x => (⟨x / 2 % 6, Nat.mod_lt _ (by norm_num)⟩, decide (x % 2 = 0))

@[expose] def jwLetterZ (l : Fin 6 × Bool) : ℤ :=
  if l.2 then (l.1.val : ℤ) + 1 else -((l.1.val : ℤ) + 1)

@[expose] def jwSurjA : List ℤ := (jwOfCodes jwSurjACodes).map jwLetterZ

@[expose] def jwSurjB (neg : Bool) : List ℤ := (jwOfCodes (jwSurjBCodes neg)).map jwLetterZ

@[expose] def jwImg (O : VOrbit) (neg : Bool) (k : ℕ) : Table :=
  wordT 275 (genTables O) (jwGenWord neg k)

@[expose] def jwImgLetter (T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5 : Table) (z : ℤ) : Table :=
  if z = 1 then T0 else if z = 2 then T1 else if z = 3 then T2 else if z = 4 then T3
  else if z = 5 then T4 else if z = 6 then T5 else if z = -1 then V0 else if z = -2 then V1
  else if z = -3 then V2 else if z = -4 then V3 else if z = -5 then V4 else V5

@[noinline, expose] def jwTabCheck (neg : Bool) : Bool :=
  let O := orbitData ()
  let T0 := jwImg O neg 0
  let T1 := jwImg O neg 1
  let T2 := jwImg O neg 2
  let T3 := jwImg O neg 3
  let T4 := jwImg O neg 4
  let T5 := jwImg O neg 5
  let V0 := invT 275 T0
  let V1 := invT 275 T1
  let V2 := invT 275 T2
  let V3 := invT 275 T3
  let V4 := invT 275 T4
  let V5 := invT 275 T5
  invOK 275 T0 V0 && invOK 275 T1 V1 && invOK 275 T2 V2 && invOK 275 T3 V3 &&
    invOK 275 T4 V4 && invOK 275 T5 V5 &&
    (jwRels neg).all (fun r =>
      wordT 275 (jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5) (r.map jwLetterZ) ==
        idT 275) &&
    wordT 275 (jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5) jwSurjA == O.alpha &&
    wordT 275 (jwImgLetter T0 T1 T2 T3 T4 T5 V0 V1 V2 V3 V4 V5) (jwSurjB neg) == O.beta

@[expose] def jwEnums (neg : Bool) : Bool := jwEnum6 neg && jwEnum5 neg && jwEnum4 neg

@[expose] def jwChecks (neg : Bool) : Bool := jwEnums neg && jwTabCheck neg

end CFSG.Sporadic.Recognition.JankoWong
