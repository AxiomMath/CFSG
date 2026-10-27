module

public import CFSG.LocalAnalysis.EvenSporadicStandard.J4Std.DataLocalFamNative
public import Std.Data.HashSet

public section

namespace CFSG.KC.J4Fam

open CFSG.Sporadic.J4.QT (compT actT idT)
open CFSG.EvenSporadicStandard.J4Std.DataLocal (maskOf)

@[expose] def comT (s t : List Nat) : Bool := compT s t == compT t s

@[expose] def nodupL : List (List Nat) → Bool
  | [] => true
  | a :: l => l.all (fun b => b != a) && nodupL l

@[expose] def invsOK (INV : List (List Nat)) : Bool :=
  INV.length == 191 && INV.all (fun b => b != idT) && nodupL INV &&
    INV.all (fun t => t.length == 11 && t.all (· < 2048))

@[expose] def chunks {α : Type} : Nat → List α → List (List α)
  | 0, _ => []
  | f + 1, l => bif l.isEmpty then [] else l.take 16 :: chunks f (l.drop 16)

@[expose] def getT {α : Type} (T : List (List (List α))) (t : Nat) (d : α) : α :=
  ((T.getD (t / 256) []).getD (t / 16 % 16) []).getD (t % 16) d

@[expose] def treeOK {α : Type} [BEq α] (T : List (List (List α))) (l : List α) : Bool :=
  T == chunks l.length (chunks l.length l)

@[expose] def xsel (f : Nat → Bool) (X : Nat → Nat) : Nat :=
  (List.range 11).foldl (fun acc b => bif f b then acc ^^^ X b else acc) 0

@[expose] def tb (t : List Nat) (k s : Nat) : Bool := (t.getD k 0).testBit s

@[expose] def wordB (t : List Nat) (b : Nat) : Nat := maskOf ((List.range 11).filter fun k => tb t k b)

@[expose] def lanesW (w : Nat) (F : Nat → Nat) (l : List Nat) : Nat :=
  l.foldl (fun acc j => acc ||| (F j <<< (w * j))) 0

@[expose] def lanes (F : Nat → Nat) (l : List Nat) : Nat := lanesW 11 F l

@[expose] def ppPlane (ts : List (List Nat)) (b : Nat) : Nat :=
  lanes (fun j => wordB (ts.getD j []) b) (List.range 191)

@[expose] def ttPlane (ts : List (List Nat)) (b s : Nat) : Nat :=
  lanes (fun j => bif tb (ts.getD j []) b s then 1 else 0) (List.range 191)

@[expose] def ppOK (INV : List (List Nat)) (PP : List Nat) : Bool :=
  PP.length == 11 && (List.range 11).all fun b => PP.getD b 0 == ppPlane INV b

@[expose] def ttOK (INV : List (List Nat)) (TT : List (List Nat)) : Bool :=
  (List.range 11).all fun b => (List.range 11).all fun s =>
    (TT.getD b []).getD s 0 == ttPlane INV b s

@[expose] def aPl (PP : List Nat) (t : List Nat) (s : Nat) : Nat := xsel (fun b => tb t b s) (PP.getD · 0)

@[expose] def bPl (TT : List (List Nat)) (t : List Nat) (s : Nat) : Nat :=
  lanesW 1 (fun k => xsel (fun b => tb t k b) (fun b => (TT.getD b []).getD s 0)) (List.range 11)

@[expose] def REP : Nat := lanes (fun _ => 1) (List.range 191)

@[expose] def laneNZ (X : Nat) : Nat :=
  (List.range 11).foldl (fun acc k => acc ||| ((X >>> k) &&& REP)) 0

@[expose] def spread (m : Nat) : Nat := lanes (fun j => bif m.testBit j then 1 else 0) (List.range 191)

@[expose] def packW (t : List Nat) : Nat := lanes (wordB t) (List.range 11)

@[expose] def wallOK (INV : List (List Nat)) (WALL : Nat) : Bool :=
  WALL == lanesW 121 (fun p => packW (INV.getD p [])) (List.range 191)

@[expose] def fill (Y : Nat) : Nat := lanesW 1 (fun _ => Y) (List.range 11)

@[expose] def ePlGo (WALL s : Nat) : List Nat → Nat → Nat
  | [], _ => 0
  | p :: ps, j => (((WALL >>> (121 * p + 11 * s)) &&& 2047) <<< (11 * j)) ||| ePlGo WALL s ps (j + 1)

@[expose] def ePl (WALL : Nat) (row : List Nat) (s : Nat) : Nat := ePlGo WALL s row 0

@[expose] def packR : List Nat → Nat
  | [] => 0
  | x :: l => x ||| (packR l <<< 8)

@[expose] def fieldR (r j : Nat) : Nat := (r >>> (8 * j)) &&& 255

@[expose] def ptRowOK (m i : Nat) : List Nat → Nat → Bool
  | x :: xs, j => (bif j == i then x == 191 else bif m.testBit j then x < 191 else x == 0) &&
      ptRowOK m i xs (j + 1)
  | [], j => j == 191

@[expose] def diffAll (P Q : Nat → Nat) : Nat :=
  (List.range 11).foldl (fun acc s => acc ||| (P s ^^^ Q s)) 0

@[expose] def rowOK (INV : List (List Nat)) (CML : List Nat) (PTL : List (List Nat))
    (PTP : List Nat) (PP : List Nat) (TT : List (List Nat)) (WALL : Nat) (i : Nat) : Bool :=
  CML.getD i 0 < 2 ^ 191 &&
    spread (CML.getD i 0) ==
      REP ^^^ laneNZ (diffAll (aPl PP (INV.getD i [])) (bPl TT (INV.getD i []))) &&
    ptRowOK (CML.getD i 0) i (PTL.getD i []) 0 &&
    PTP.getD i 0 == packR (PTL.getD i []) &&
    diffAll (aPl PP (INV.getD i [])) (ePl WALL (PTL.getD i [])) &&&
      fill (spread (CML.getD i 0) ^^^ (1 <<< (11 * i))) == 0

@[expose] def plOK (PL : List Nat) : Bool :=
  PL.length == 11 && PL.all (· < 2 ^ 2048) &&
    (List.range 11).all fun b => (List.range 2048).all fun c =>
      (PL.getD b 0).testBit c == c.testBit b

@[expose] def fixBits (PL : List Nat) (t : List Nat) : Nat :=
  (2 ^ 2048 - 1) ^^^ (diffAll (fun s => xsel (fun b => tb t b s) (PL.getD · 0)) (PL.getD · 0) &&&
    (2 ^ 2048 - 1))

@[expose] def incr : List Nat → Bool
  | a :: b :: l => a < b && incr (b :: l)
  | _ => true

@[expose] def fixRowOK (INV : List (List Nat)) (FB : List Nat) (FLL : List (List Nat))
    (PL : List Nat) (i : Nat) : Bool :=
  FB.getD i 0 == fixBits PL (INV.getD i []) && incr (FLL.getD i []) &&
    (FLL.getD i []).all (· < 2048) && maskOf (FLL.getD i []) == FB.getD i 0

@[expose] def tbit (m i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight m i) 1) 1

@[expose] def bitsR (m : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | n + 1, i => bif tbit m i then i :: bitsR m n (i + 1) else bitsR m n (i + 1)

@[expose] def bitIdxK (m : Nat) : List Nat := bitsR m 191 0

@[expose] def prodR (r : Nat) : List Nat → Nat → Nat
  | [], acc => acc
  | j :: l, acc =>
    prodR r l (Nat.lor acc (Nat.shiftLeft 1 (Nat.land (Nat.shiftRight r (Nat.mul 8 j)) 255)))

@[expose] def extsGo (m : Nat) (bs : List Nat) : Nat → List Nat → List Nat → List Nat
  | i, c :: cs, r :: rs =>
    bif !tbit m i && Nat.beq (Nat.land m c) m then
      prodR r bs (Nat.lor m (Nat.shiftLeft 1 i)) :: extsGo m bs (i + 1) cs rs
    else extsGo m bs (i + 1) cs rs
  | _, _, _ => []

@[expose] def extsK (CML PTP : List Nat) (m : Nat) : List Nat := extsGo m (bitIdxK m) 0 CML PTP

@[expose] def entriesEq (T : List (List (List Nat))) (n : Nat) : List Nat → List Nat → Bool
  | x :: xs, t :: ts => t < n && x == getT T t 0 && entriesEq T n xs ts
  | [], [] => true
  | _, _ => false

@[expose] def closeChunk (CML PTP : List Nat) (T : List (List (List Nat))) (n : Nat)
    (LT : List (List (List Nat))) (TGT : List (List (List (List Nat)))) (N c : Nat) : Bool :=
  (List.range' (128 * c) 128).all fun p =>
    decide (N ≤ p) || entriesEq T n (extsK CML PTP (getT LT p 0)) (getT TGT p [])

@[expose] def coverOK (N : Nat) (TG : List (List Nat)) : Bool :=
  TG.foldl (fun acc l => l.foldl (fun a t => a ||| (1 <<< t)) acc) 0 &&& (2 ^ N - 1) == 2 ^ N - 1

@[expose] def andAll (FBT : List (List (List Nat))) (bs : List Nat) : Nat :=
  bs.foldl (fun acc j => acc &&& getT FBT j 0) (2 ^ 2048 - 1)

@[expose] def countR (X : Nat) : List Nat → Nat
  | [] => 0
  | c :: l => bif tbit X c then countR X l + 1 else countR X l

@[expose] def fixCntK (FBT : List (List (List Nat))) (FLLT : List (List (List (List Nat))))
    (m : Nat) : Nat :=
  match bitIdxK m with
  | [] => 2048
  | i :: bs => countR (andAll FBT bs) (getT FLLT i [])

@[expose] def boundOK1 (FBT : List (List (List Nat))) (FLLT : List (List (List (List Nat))))
    (m : Nat) : Bool :=
  m >>> 191 == 0 && (m == 0 || decide (fixCntK FBT FLLT m * ((bitIdxK m).length + 1) ≤ 1024))

@[expose] def boundsChunk (FBT : List (List (List Nat))) (FLLT : List (List (List (List Nat))))
    (LT : List (List (List Nat))) (N c : Nat) : Bool :=
  (List.range' (512 * c) 512).all fun p => decide (N ≤ p) || boundOK1 FBT FLLT (getT LT p 0)

end CFSG.KC.J4Fam
