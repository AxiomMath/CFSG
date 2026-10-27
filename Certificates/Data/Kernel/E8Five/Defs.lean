module

public import Mathlib.Data.Nat.Notation
public import Mathlib.Data.Int.Notation
public import Mathlib.Util.CompileInductive

public section

namespace CFSG.KC.E8Five

@[expose] def bandK (a b : Bool) : Bool := Bool.rec false b a

@[expose] def beqB (a b : Bool) : Bool := Bool.rec (Bool.rec true false b) b a

@[expose] def bitK (b : Bool) : ℕ := Bool.rec 0 1 b

@[expose] def allNK (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k r => bandK (f k) r) n

@[expose] def cntNK (n : ℕ) (f : ℕ → Bool) : ℕ :=
  Nat.rec (motive := fun _ => ℕ) 0 (fun k r => Nat.add (bitK (f k)) r) n

@[expose] def dot5 (a b : ℕ) : ℕ :=
  Nat.mod (Nat.add
    (Nat.add (Nat.mul (Nat.mod a 5) (Nat.mod b 5))
      (Nat.mul (Nat.mod (Nat.div a 5) 5) (Nat.mod (Nat.div b 5) 5)))
    (Nat.add (Nat.mul (Nat.mod (Nat.div a 25) 5) (Nat.mod (Nat.div b 25) 5))
      (Nat.mul (Nat.mod (Nat.div a 125) 5) (Nat.mod (Nat.div b 125) 5)))) 5

@[expose] def coefK (M : List (List ℤ)) (l : List ℤ) (k : ℕ) : ℤ :=
  l.getD 0 0 * (M.getD 0 []).getD k 0 + l.getD 1 0 * (M.getD 1 []).getD k 0 +
    l.getD 2 0 * (M.getD 2 []).getD k 0 + l.getD 3 0 * (M.getD 3 []).getD k 0 +
    l.getD 4 0 * (M.getD 4 []).getD k 0 + l.getD 5 0 * (M.getD 5 []).getD k 0 +
    l.getD 6 0 * (M.getD 6 []).getD k 0 + l.getD 7 0 * (M.getD 7 []).getD k 0

@[expose] def coef5K (M : List (List ℤ)) (l : List ℤ) (k : ℕ) : ℕ := (coefK M l k % 5).toNat

@[expose] def rowCodeK (M : List (List ℤ)) (l : List ℤ) : ℕ :=
  coef5K M l 0 + 5 * coef5K M l 1 + 25 * coef5K M l 2 + 125 * coef5K M l 3

@[expose] def rowsOfK (M : List (List ℤ)) (roots : List (List ℤ)) : List ℕ :=
  roots.map (rowCodeK M)

@[expose] def cntRootsK (rows : List ℕ) (n : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) 0 (fun r _ acc => Nat.add (bitK (Nat.beq (dot5 r n) 0)) acc)
    rows

@[expose] def t40K (rows : List ℕ) (n : ℕ) : Bool :=
  bandK (Bool.rec true false (Nat.beq n 0)) (Nat.beq (cntRootsK rows n) 40)

@[expose] def bitOf (M n : ℕ) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 n))

@[expose] def maskOK (rows : List ℕ) (M : ℕ) : Bool :=
  allNK 625 fun n => beqB (bitOf M n) (t40K rows n)

@[expose] def hypCntK (M m : ℕ) : ℕ :=
  cntNK 625 fun n => bandK (bitOf M n) (Nat.beq (dot5 m n) 0)

@[expose] def hypOKFrom (M a k : ℕ) : Bool :=
  allNK k fun i => Bool.rec (Nat.ble 25 (hypCntK M (Nat.add a i))) true (Nat.beq (Nat.add a i) 0)

@[expose] def fixOK (rows : List ℕ) : Bool := Nat.ble (cntNK 625 (t40K rows)) 24

@[expose] def mEig2 : List (List ℤ) :=
  [[-4, 0, -2, -1], [-3, -4, 0, -1], [-4, -1, 0, -1], [0, -3, -4, -2],
    [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

@[expose] def mEig3 : List (List ℤ) :=
  [[-4, 0, -1, -2], [-4, -1, -2, -1], [-3, -1, -4, -4], [0, -2, -4, -3],
    [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

@[expose] def mFix1 : List (List ℤ) :=
  [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0],
    [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

@[expose] def mFix2 : List (List ℤ) :=
  [[-4, -2, -3, 0], [1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1],
    [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

@[expose] def mask2 : ℕ :=
  103750171621518167506555333894665311847760465738540649615388897327887101121268701141466765379854832890009535587159804340272407362951783434255059910172792041891272423510305329591389532454912

@[expose] def mask3 : ℕ :=
  127759762276897549867963503341247602788953089555417226776553788013075188097098936234344431854645753571712044231095809667602526807858300371974953594968433192529289193759506553822423828922368

end CFSG.KC.E8Five
