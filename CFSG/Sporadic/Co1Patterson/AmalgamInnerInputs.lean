module

public import CFSG.Sporadic.Co1Patterson.AmalgamRigidInputs

public section

namespace CFSG.Sporadic.Co1Patterson.Native

open CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Patterson.TwistNative
  CFSG.Sporadic.Co1.InvNative

@[expose] def kRow (j : Nat) : Rows := twRow (kIdx.getD j 0)

@[expose] def kRowI (j : Nat) : Rows := inv (kRow j)

@[expose] def kWordR (w : List Nat) : Rows := w.foldl (fun acc j => mul acc (kRow j)) one

@[expose] def kWordIR (w : List Nat) : Rows := w.foldl (fun acc j => mul (kRowI j) acc) one

@[expose] def conjWords : List (List Nat) := [[], [0], [1], [0, 0], [0, 1], [1, 0]]

@[expose] def stabWords : List (List Nat) := [[0, 1, 1, 1], [1, 1, 1, 1, 1]]

@[expose] def rxRow : Rows := aRowOf (34, 0)

@[expose] def ryRow : Rows := mul (hprodRow 55) (aRowOf (108, 0))

@[expose] def tRow (j : Nat) : Rows :=
  mul (mul (kWordR (conjWords.getD (j % 6) [])) (if j < 6 then rxRow else ryRow))
    (kWordIR (conjWords.getD (j % 6) []))

@[expose] def tSub (b S : Nat) : Rows :=
  (List.range 6).foldl (fun acc j => if S.testBit j then mul acc (tRow (b + j)) else acc) one

@[expose] def vRows : List Rows := [one, iotaARows, yRow 0, mul (yRow 0) iotaARows]

@[expose] def stabR (g X : Rows) : Bool :=
  let gX := mul g X
  let Xg := mul X g
  vRows.any fun v => gX == mul v Xg

@[expose] def isVPar (c : Nat) (p : Nat × Nat) : Bool := c == 0 && (p.1 == 0 || p.1 == 1)

@[noinline, expose] def innerElemOK : Bool :=
  (List.range 2).all (fun j => validRows (kRow j) && validRows (kRowI j) &&
      mul (kRow j) (kRowI j) == one) &&
    pow (kRow 1) 15 == one &&
    mul rxRow rxRow == iotaARows && mul ryRow ryRow == yRow 0 &&
    stabWords.all (fun w => stabR (kWordR w) rxRow && stabR (kWordR w) ryRow)

@[noinline, expose] def innerGenOK : Bool :=
  let T0 := (List.range 64).map (tSub 0)
  let T6 := (List.range 64).map (tSub 6)
  let T := (List.range 12).map tRow
  aList.all (fun p => T0.any fun t => vRows.any fun v => mul t v == aRowOf p) &&
    ((List.range 6).all fun i => T6.any fun t => aList.any fun p =>
      mul t (aRowOf p) == twRow (hIdx.getD i 0)) &&
    T.all fun t => T.all fun t' =>
      let tt' := mul t t'
      let t't := mul t' t
      vRows.any fun v => tt' == mul v t't

@[expose] def loopAt (T : List Rows) (g₁ g₂ x₁ : Rows) (c : Nat) (p : Nat × Nat) (r : Rows) :
    Bool :=
  (!T.all (fun t => mul r t == mul t r) || isVPar c p) &&
    (let rx := mul r x₁
     let xr := mul x₁ r
     !vRows.any (fun v => rx == mul v xr) || isVPar c p) &&
    (!(stabR g₁ r && stabR g₂ r) ||
      (let rr := mul r r
       (rr != iotaARows || vRows.any fun v => r == mul v rxRow) &&
         (rr != yRow 0 || vRows.any fun v => r == mul v ryRow)))

@[noinline, expose] def innerLoopOK : Bool :=
  let T := (List.range 12).map tRow
  let g₁ := kWordR (stabWords.getD 0 [])
  let g₂ := kWordR (stabWords.getD 1 [])
  let AR := aList.map fun p => (p, aRowOf p)
  (List.range 64).all fun c =>
    let hc := hprodRow c
    AR.all fun pa => loopAt T g₁ g₂ (kRow 1) c pa.1 (mul hc pa.2)

@[expose] def w0Basis : List Nat := [2, 4, 8, 32, 64, 128]

@[expose] def genWords : List (List Nat) := [[1], [0, 0]]

@[expose] def expandWord (u : List Nat) : List Nat := u.flatMap fun i => genWords.getD i []

@[expose] def wMat (u : List Nat) : List Nat := w0Basis.map (actWord (expandWord u))

@[expose] def wKey (M : List Nat) : Nat := M.foldr (fun v acc => v + 256 * acc) 0

@[expose] def wordsOf (T : Array Nat × Array Nat) : Array (List Nat) :=
  (List.range T.1.size).foldl (fun acc i =>
    acc.push (if i == 0 then [] else T.2[i]! :: acc[T.1[i]!]!)) #[]

@[expose] def innerWords : List (List Nat) :=
  (wordsOf (treeOfMasks 2 64 innerWordMasks)).toList

@[noinline, expose] def innerBfsOK : Bool :=
  let W := innerWords
  W.length == 20160 && distinctKeys (W.map fun u => wKey (wMat u)) &&
    wVecs.all fun v => actWord [0, 0, 0, 0, 0, 0] v == v

@[noinline, expose] def innerOrbOK : Bool :=
  zRows == yRow 0 && (ptSet orbQ).contains qRows

end CFSG.Sporadic.Co1Patterson.Native
