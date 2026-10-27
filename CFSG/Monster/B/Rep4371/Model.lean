module

public section

namespace CFSG.Monster.B.Model

@[expose] def popcN : Nat → Nat → Nat
  | 0, _ => 0
  | k + 1, a => a % 2 + popcN k (a / 2)

@[expose] def parN (k a : Nat) : Bool := popcN k a % 2 == 1

@[expose] def xorSum (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xorSum f n ^^ f n

@[expose] def packN (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => packN f n ||| (if f n then 2 ^ n else 0)

@[expose] def combN (m : Nat → Nat) : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a => combN m n a ^^^ (if a.testBit n then m n else 0)

@[expose] def bmaskN (i : Nat) : Nat :=
  [0x11111e, 0x1111e1, 0x111e11, 0x11e111, 0x1e1111, 0xe11111, 0xa6c00c, 0x6ca00a, 0x6ac0c0,
    0xc6a0a0, 0xcccc00, 0xaaaa00].getD i 0

@[expose] def umaskN (k : Nat) : Nat :=
  [0xe, 0x1f, 0x10f, 0x100f, 0x1000f, 0x11111, 0xa, 0xc, 0x5f, 0x3f, 0x50f, 0x30f].getD k 0

@[expose] def wordN (a : Nat) : Nat := combN bmaskN 12 a

@[expose] def repN (d : Nat) : Nat := combN umaskN 12 d

@[expose] def coeffN (w : Nat) : Nat := packN (fun k => parN 24 (w &&& umaskN k)) 12

@[expose] def dualN (v : Nat) : Nat := packN (fun j => parN 24 (v &&& bmaskN j)) 12

@[expose] def pairN (a d : Nat) : Bool := parN 12 (a &&& d)

@[expose] def mu0N (a : Nat) : Bool := a.testBit 0

@[expose] def pi0N (a : Nat) : Nat := a ^^^ (if a.testBit 0 then 63 else 0)

@[expose] def shiftN (a c : Nat) : Nat := pi0N (c ^^^ a)

@[expose] def pN (a : Nat) : Bool := popcN 24 (wordN a) / 4 % 2 == 1

@[expose] def kN (a b : Nat) : Bool := popcN 24 (wordN a &&& wordN b) / 2 % 2 == 1

@[expose] def acodeN (a b : Nat) : Nat := dualN (wordN a &&& wordN b)

@[expose] def betaN (j k : Nat) : Bool :=
  if j < k then false
  else if j = k then popcN 24 (bmaskN j) / 4 % 2 == 1
  else popcN 24 (bmaskN j &&& bmaskN k) / 2 % 2 == 1

@[expose] def thetaRec : Nat → Nat → Nat
  | 0, _ => 0
  | n + 1, a =>
    if a.testBit n then
      thetaRec n a ^^^ packN (betaN n) 12 ^^^ dualN (combN bmaskN n a &&& bmaskN n)
    else thetaRec n a

@[expose] def thetaN (a : Nat) : Nat := thetaRec 12 a

@[expose] def thetaBit (a b : Nat) : Bool := pairN b (thetaN a)

abbrev Pauli : Type := Bool × Nat × Nat

@[reducible, expose] def Pauli.s (x : Pauli) : Bool := x.1

@[reducible, expose] def Pauli.a (x : Pauli) : Nat := x.2.1

@[reducible, expose] def Pauli.d (x : Pauli) : Nat := x.2.2

@[expose] def Pauli.mul (x y : Pauli) : Pauli :=
  (x.s ^^ y.s ^^ pairN y.a x.d, x.a ^^^ y.a, x.d ^^^ y.d)

@[expose] def permWordN (p : Array Nat) (w : Nat) : Nat := combN (fun i => 2 ^ p[i]!) 24 w

@[expose] def permCN (p : Array Nat) (a : Nat) : Nat := coeffN (permWordN p (wordN a))

@[expose] def permDN (p : Array Nat) (d : Nat) : Nat := dualN (permWordN p (repN d))

@[expose] def betaPN (p : Array Nat) (i j : Nat) : Bool :=
  thetaBit (permCN p (2 ^ i)) (permCN p (2 ^ j)) ^^ betaN i j

@[expose] def kappaN (p : Array Nat) (a : Nat) : Bool :=
  xorSum (fun i => xorSum (fun j => decide (i < j) && a.testBit i && a.testBit j && betaPN p i j)
    12) 12

@[expose] def qGN (ν : Nat) : Bool := popcN 6 ν * (popcN 6 ν - 1) / 2 % 2 == 1

@[expose] def bGN (μ ν : Nat) : Bool := (parN 6 μ && parN 6 ν) ^^ parN 6 (μ &&& ν)

@[expose] def gammaLowN (ν : Nat) : Nat := (ν % 64) ^^^ (if parN 6 ν then 63 else 0)

@[expose] def sumRange (f : Nat → Int) : Nat → Int
  | 0 => 0
  | n + 1 => sumRange f n + f n

@[expose] def sgnI (b : Bool) : Int := if b then -1 else 1

@[expose] def conjPauliN (q y : Pauli) : Pauli :=
  (y.s ^^ pairN y.a q.d ^^ pairN q.a y.d, y.a, y.d)

@[expose] def conjPermN (p : Array Nat) (y : Pauli) : Pauli :=
  (y.s ^^ kappaN p y.a, permCN p y.a, thetaN (permCN p y.a) ^^^ permDN p (thetaN y.a ^^^ y.d))

@[expose] def conjTN (a b : Nat) : Pauli :=
  (thetaBit b a, b ^^^ (if thetaBit a b then 63 else 0), acodeN a b)

@[expose] def conjDN (a d : Nat) : Pauli :=
  (!pairN 63 d && pairN a d,
    (if pairN 63 d then a else 0) ^^^ (if (pairN 63 d && pN a) ^^ pairN a d then 63 else 0),
    (if pairN 63 d then thetaN a else 0) ^^^ d)

@[expose] def conjYN (a : Nat) (y : Pauli) : Pauli :=
  Pauli.mul (Pauli.mul (y.s, 0, 0) (conjTN a y.a)) (conjDN a y.d)

@[expose] def conjXiN (y : Pauli) : Pauli :=
  let μ := y.a % 64
  let low := y.d % 64
  let ν := low ^^^ (if parN 6 low then 63 else 0)
  (y.s ^^ qGN ν ^^ bGN μ ν, ν ^^^ (y.a &&& 4032), gammaLowN (μ ^^^ ν) ^^^ (y.d &&& 4032))

@[expose] def ePauliN (q : Pauli) (η : Bool) (c : Nat) : Bool × Bool × Nat :=
  (q.s ^^ (η && mu0N q.a) ^^ pairN (shiftN q.a (pi0N c)) q.d, η ^^ pairN 63 q.d,
    shiftN q.a (pi0N c))

@[expose] def ePermN (p : Array Nat) (η : Bool) (c : Nat) : Bool × Bool × Nat :=
  (kappaN p (pi0N c) ^^ ((η ^^ kappaN p 63) && mu0N (permCN p (pi0N c))), η ^^ kappaN p 63,
    pi0N (permCN p (pi0N c)))

@[expose] def eYN (a : Nat) (η : Bool) (c : Nat) : Bool × Bool × Nat :=
  if η then (kN a (pi0N c), true, pi0N c) else (thetaBit (pi0N c) a, false, shiftN a (pi0N c))

@[expose] def xiGammaN (c : Nat) (e : Bool) : Int :=
  sumRange (fun μ => if pairN 63 (gammaLowN μ) == e then
    sgnI (qGN μ ^^ pairN (pi0N c) (gammaLowN μ)) else 0) 64

@[expose] def xiGTerm (η : Bool) (c ν : Nat) : Bool × Bool × Nat :=
  (qGN ν ^^ (η && mu0N ν), η, shiftN ν (pi0N c))

abbrev Key : Type := Nat × Nat × Nat

@[expose] def Key.A (j : Nat) : Key := (0, j, 0)

@[expose] def Key.X (a d : Nat) : Key := (1, a, d)

@[expose] def Key.W (η : Bool) (c : Nat) : Key := (2, if η then 1 else 0, c)

@[expose] def coeffOf (κ : Key) : List (Key × Int) → Int
  | [] => 0
  | e :: v => (if e.1 = κ then e.2 else 0) + coeffOf κ v

@[expose] def eqModel (D₁ : Int) (v₁ : List (Key × Int)) (D₂ : Int) (v₂ : List (Key × Int)) :
    Bool :=
  (v₁ ++ v₂).all fun e => coeffOf e.1 v₁ * D₂ == coeffOf e.1 v₂ * D₁

@[expose] def c4N (r r' : Nat) : Int :=
  if r = 0 then -32 else if r = r' ∨ r' = 0 then 32 else -32

@[expose] def signedTerm (κ : Key) (s : Bool) : Key × Int := (κ, sgnI s * 64)

@[expose] def keyActPauli (q : Pauli) : Key → List (Key × Int)
  | (0, j, _) => [(Key.A j, 64)]
  | (1, a, d) =>
    let y := conjPauliN q (false, a, d)
    [signedTerm (Key.X y.a y.d) y.s]
  | (_, e, c) =>
    let t := ePauliN q (e != 0) c
    [signedTerm (Key.W t.2.1 t.2.2) t.1]

@[expose] def keyActPerm (p : Array Nat) : Key → List (Key × Int)
  | (0, j, _) => [(Key.A p[j]!, sgnI (p[0]! != 0) * 64)]
  | (1, a, d) =>
    let y := conjPermN p (false, a, d)
    [signedTerm (Key.X y.a y.d) y.s]
  | (_, e, c) =>
    let t := ePermN p (e != 0) c
    [signedTerm (Key.W t.2.1 t.2.2) (t.1 ^^ (p[0]! != 0))]

@[expose] def keyActSign (a : Nat) : Key → List (Key × Int)
  | (0, j, _) => [signedTerm (Key.A j) ((wordN a).testBit 0 ^^ (wordN a).testBit j)]
  | (1, b, d) =>
    let y := conjYN a (false, b, d)
    [signedTerm (Key.X y.a y.d) y.s]
  | (_, e, c) =>
    let t := eYN a (e != 0) c
    [signedTerm (Key.W t.2.1 t.2.2) (t.1 ^^ (wordN a).testBit 0)]

@[expose] def keyActXi : Key → List (Key × Int)
  | (0, j, _) =>
    (List.range 4).map fun r' =>
      (Key.A (4 * (j / 4) + r'), -(c4N (j % 4) r' * sgnI ((bmaskN 0).testBit (4 * (j / 4) + r'))))
  | (1, a, d) =>
    let y := conjYN 1 (conjXiN (false, a, d))
    [signedTerm (Key.X y.a y.d) y.s]
  | (_, e, c) =>
    [false, true].flatMap fun f => (List.range 64).map fun ν =>
      let t := xiGTerm ((e != 0) ^^ f) c ν
      let u := eYN 1 t.2.1 t.2.2
      (Key.W u.2.1 u.2.2, -(xiGammaN c f * sgnI (t.1 ^^ u.1)))

@[expose] def actVec (act : Key → List (Key × Int)) (v : List (Key × Int)) : List (Key × Int) :=
  v.flatMap fun e => (act e.1).map fun f => (f.1, e.2 * f.2)

@[expose] def oddCodesOf (n : Nat) : Array Nat :=
  (((List.range n).map (2 * ·)).filter
    fun a => (wordN a).testBit 0 == (wordN a).testBit 1).toArray

@[expose] def oddCodes : Array Nat := oddCodesOf 2048

@[expose] def octCoeffsOf (n : Nat) : Array Nat :=
  (((List.range n).filter fun a => popcN 24 (wordN a) == 8 && wordN a % 4 == 3).mergeSort
    fun a b => wordN a ≤ wordN b).toArray

@[expose] def octCoeffs : Array Nat := octCoeffsOf 4096

@[expose] def localOrder (d : Nat) : List Nat :=
  [0, 1] ++ (List.range 24).filter fun i => 2 ≤ i && d.testBit i

@[expose] def spreadN (d m : Nat) : Nat := combN (fun t => 2 ^ (localOrder d).getD t 0) 8 m

@[expose] def localPairs : Array (Nat × Nat) :=
  #[(5, 6), (9, 10), (17, 18), (29, 30), (33, 34), (45, 46), (53, 54), (57, 58), (65, 66), (77, 78),
    (85, 86), (89, 90), (101, 102), (105, 106), (113, 114), (125, 126)]

@[expose] def minusKey (i j : Nat) : Key := Key.X 0 (dualN (2 ^ i ||| 2 ^ j))

@[expose] def plusKey (i j : Nat) : Key := Key.X 63 (dualN (2 ^ i ||| 2 ^ j))

@[expose] def oddCode (c i : Nat) : Nat := c ^^^ (if (wordN c).testBit i ^^ pN c then 63 else 0)

@[expose] def oddKey (c i : Nat) : Key :=
  Key.X (oddCode c i) (thetaN (oddCode c i) ^^^ dualN (2 ^ i))

@[expose] def octCode (a m : Nat) : Nat :=
  a ^^^ (if popcN 24 (spreadN (wordN a) m) / 2 % 2 == 1 then 63 else 0)

@[expose] def octKey (a m : Nat) : Key :=
  Key.X (octCode a m) (thetaN (octCode a m) ^^^ dualN (spreadN (wordN a) m))

@[expose] def rawModel (k : Nat) : List (Key × Int) :=
  if k = 0 then [(Key.A 0, 32), (Key.A 1, 32)]
  else if k ≤ 22 then [(Key.A (k + 1), 64)]
  else if k ≤ 66 then
    if (k - 23) % 2 = 0 then
      [(minusKey 0 ((k - 23) / 2 + 2), 64), (minusKey 1 ((k - 23) / 2 + 2), -64)]
    else [(plusKey 0 ((k - 23) / 2 + 2), 64), (plusKey 1 ((k - 23) / 2 + 2), -64)]
  else if k ≤ 1090 then [(oddKey oddCodes[k - 67]! 0, 64), (oddKey oddCodes[k - 67]! 1, -64)]
  else if k ≤ 2322 then
    [(octKey octCoeffs[(k - 1091) / 16]! (localPairs[(k - 1091) % 16]!).1, 64),
      (octKey octCoeffs[(k - 1091) / 16]! (localPairs[(k - 1091) % 16]!).2, -64)]
  else [(Key.W (decide (3347 ≤ k)) oddCodes[(k - 2323) % 1024]!, 64)]

@[expose] def rowModel (row : Array (Nat × Int)) : List (Key × Int) :=
  row.toList.flatMap fun e => (rawModel e.1).map fun f => (f.1, e.2 * f.2)

@[expose] def rowOK (act : Key → List (Key × Int)) (row : Array (Nat × Int)) (k : Nat) : Bool :=
  eqModel 4096 (actVec act (rawModel k)) 512 (rowModel row)

@[expose] def genOK (act : Key → List (Key × Int)) (rows : Array (Array (Nat × Int))) : Bool :=
  (List.range 4371).all fun k => rowOK act rows[k]! k

@[expose] def Mtab : Array (Array Int) :=
  #[#[-1, 1, 1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, -1, -1],
    #[1, -1, 1, 1, 1, 1, -1, 1, 1, 1, -1, 1, -1, 1, -1, -1],
    #[1, 1, -1, 1, 1, -1, 1, 1, 1, -1, 1, 1, -1, -1, 1, -1],
    #[-1, -1, -1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, 1, 1, -1],
    #[1, 1, 1, -1, -1, 1, 1, 1, 1, -1, -1, -1, 1, 1, 1, -1],
    #[-1, -1, 1, -1, -1, 1, -1, -1, 1, -1, 1, 1, -1, -1, 1, -1],
    #[-1, 1, -1, -1, -1, -1, 1, -1, 1, 1, -1, 1, -1, 1, -1, -1],
    #[1, -1, -1, -1, -1, -1, -1, 1, 1, 1, 1, -1, 1, -1, -1, -1],
    #[1, 1, 1, -1, 1, -1, -1, -1, -1, 1, 1, 1, 1, 1, 1, -1],
    #[-1, -1, 1, -1, 1, -1, 1, 1, -1, 1, -1, -1, -1, -1, 1, -1],
    #[-1, 1, -1, -1, 1, 1, -1, 1, -1, -1, 1, -1, -1, 1, -1, -1],
    #[1, -1, -1, -1, 1, 1, 1, -1, -1, -1, -1, 1, 1, -1, -1, -1],
    #[-1, 1, 1, 1, -1, -1, -1, 1, -1, -1, -1, 1, 1, -1, -1, -1],
    #[1, -1, 1, 1, -1, -1, 1, -1, -1, -1, 1, -1, -1, 1, -1, -1],
    #[1, 1, -1, 1, -1, 1, -1, -1, -1, 1, -1, -1, -1, -1, 1, -1],
    #[-1, -1, -1, 1, -1, 1, 1, 1, -1, 1, 1, 1, 1, 1, 1, -1]]

@[expose] def Mentry (i j : Nat) : Int := (Mtab[i]!)[j]!

@[expose] def tauRow (k : Nat) : Array (Nat × Int) :=
  if k = 0 then #[(0, 8)]
  else if k ≤ 22 then #[(23 + 2 * (k - 1), 8), (24 + 2 * (k - 1), -8)]
  else if k ≤ 66 then
    if (k - 23) % 2 = 0 then #[((k - 23) / 2 + 1, 4), (k, 4), (k + 1, 4)]
    else #[((k - 23) / 2 + 1, 4), (k - 1, -4), (k, -4)]
  else if k ≤ 1090 then
    #[(3347 + (k - 67), sgnI ((wordN oddCodes[k - 67]!).testBit 0) * 8)]
  else if k ≤ 2322 then
    (Array.range 16).map fun j => (1091 + 16 * ((k - 1091) / 16) + j, 2 * Mentry ((k - 1091) % 16) j)
  else if k ≤ 3346 then
    #[(67 + (k - 2323), sgnI (pN oddCodes[k - 2323]!) * 8)]
  else
    #[(2323 + (k - 3347),
      sgnI ((wordN oddCodes[k - 3347]!).testBit 0 ^^ pN oddCodes[k - 3347]!) * 8)]

@[expose] def octDataOK : Bool :=
  octCoeffs.size == 77 && (List.range 77).all fun b =>
    let w := wordN octCoeffs[b]!
    (List.range 256).all fun m =>
      (spreadN w m &&& w == spreadN w m) && (popcN 24 (spreadN w m) == popcN 8 m) &&
      (spreadN w (m ^^^ 255) == spreadN w m ^^^ w) &&
      (List.range 256).all fun m' => spreadN w (m &&& m') == spreadN w m &&& spreadN w m' &&
        (m == m' || spreadN w m % 16777216 != spreadN w m' % 16777216)

@[expose] def octSign (x z : Nat) : Int := sgnI ((popcN 8 (x &&& z) + popcN 8 z / 2) % 2 == 1)

@[expose] def octSignOK : Bool :=
  (List.range 16).all fun i => (List.range 256).all fun z =>
    popcN 8 z % 2 == 1 ||
      (octSign (localPairs[i]!).1 z - octSign (localPairs[i]!).2 z ==
        sumRange (fun j => 2 * Mentry i j *
          ((if z = (localPairs[j]!).1 ∨ z = (localPairs[j]!).1 ^^^ 255 then 1 else 0) -
            (if z = (localPairs[j]!).2 ∨ z = (localPairs[j]!).2 ^^^ 255 then 1 else 0))) 16)

@[expose] def recPerms : Array (Array Nat) :=
  #[#[0, 1, 2, 20, 5, 12, 18, 10, 13, 8, 17, 6, 4, 9, 14, 19, 15, 7, 11, 16, 22, 21, 3, 23],
    #[1, 0, 12, 13, 17, 18, 21, 23, 19, 16, 20, 22, 2, 3, 15, 14, 9, 4, 5, 8, 10, 6, 11, 7],
    #[0, 1, 14, 2, 5, 22, 16, 8, 17, 10, 7, 21, 3, 13, 15, 12, 20, 9, 19, 4, 11, 6, 18, 23],
    #[0, 1, 3, 12, 19, 4, 21, 10, 7, 17, 9, 20, 15, 13, 2, 14, 6, 8, 22, 18, 16, 11, 5, 23],
    #[0, 1, 10, 23, 5, 21, 6, 8, 14, 9, 22, 12, 18, 3, 7, 15, 17, 20, 11, 19, 16, 4, 2, 13],
    #[1, 0, 23, 11, 7, 9, 21, 4, 16, 5, 12, 3, 10, 19, 20, 17, 8, 15, 22, 13, 14, 6, 18, 2],
    #[1, 0, 19, 5, 20, 3, 8, 15, 14, 6, 17, 12, 16, 10, 7, 9, 11, 13, 2, 21, 18, 4, 22, 23],
    #[1, 0, 18, 5, 21, 3, 9, 14, 6, 15, 13, 16, 11, 17, 8, 7, 12, 10, 20, 2, 4, 19, 22, 23],
    #[1, 0, 10, 5, 20, 12, 2, 18, 22, 13, 17, 3, 16, 19, 9, 7, 23, 6, 8, 21, 15, 4, 14, 11],
    #[0, 1, 8, 3, 17, 4, 23, 14, 10, 9, 2, 11, 18, 6, 22, 12, 20, 5, 15, 19, 21, 16, 7, 13],
    #[1, 0, 19, 23, 5, 4, 22, 18, 16, 21, 15, 14, 17, 20, 11, 10, 8, 12, 7, 2, 13, 9, 6, 3],
    #[1, 0, 6, 11, 21, 3, 17, 15, 18, 14, 2, 23, 5, 9, 22, 20, 12, 10, 7, 13, 4, 19, 8, 16]]

@[expose] def qPauli (i : Nat) : Pauli :=
  if i = 0 then (true, 0, 0)
  else if i ≤ 11 then (false, 2 ^ i ^^^ (if (191 : Nat).testBit i then 1 else 0), 0)
  else (false, 0, 2 ^ (i - 11))

@[expose] def frameCode (w : List Int) : Nat := w.foldl (fun a k => a ^^^ 2 ^ (k.toNat - 3)) 0

end CFSG.Monster.B.Model
