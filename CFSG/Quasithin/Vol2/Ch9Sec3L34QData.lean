module

public import CFSG.Fischer.F4
public import Mathlib.Algebra.Order.Ring.Star

public section

namespace CFSG.Quasithin.H13.Ch9.L34Q

open CFSG.Fischer

abbrev M2 : Type := Matrix (Fin 2) (Fin 2) F4

@[expose] def f4 (n : ℕ) : F4 := ⟨⟨n % 4, Nat.mod_lt _ (by norm_num)⟩⟩

@[expose] def code (X : M2) : ℕ :=
  (X 0 0).code.val + 4 * ((X 0 1).code.val + 4 * ((X 1 0).code.val + 4 * (X 1 1).code.val))

@[expose] def decode (c : ℕ) : M2 := !![f4 c, f4 (c / 4); f4 (c / 16), f4 (c / 64)]

@[expose] def frob (x : F4) : F4 := x * x

@[expose] def gmap (A B : M2) (s t : Bool) (X : M2) : M2 :=
  A * (if s then Matrix.transpose (if t then X.map frob else X) else
    (if t then X.map frob else X)) * Matrix.transpose B

structure Par where
  A : M2
  B : M2
  s : Bool
  t : Bool

@[expose] def allF4 : List F4 := [f4 0, f4 1, f4 2, f4 3]

@[expose] def nzF4 : List F4 := [f4 1, f4 2, f4 3]

@[expose] def params : List Par :=
  allF4.flatMap fun a => nzF4.flatMap fun a' => nzF4.flatMap fun b1 => allF4.flatMap fun b =>
    nzF4.flatMap fun b2 => [false, true].flatMap fun s => [false, true].map fun t =>
      ⟨!![1, a; 0, a'], !![b1, b; 0, b2], s, t⟩

@[expose] def act (p : Par) (v : ℕ) : ℕ := code (gmap p.A p.B p.s p.t (decode v))

@[expose] def isInvAct (p : Par) : Bool :=
  (List.range 8).all fun k => act p (act p (2 ^ k)) == 2 ^ k

@[expose] def invPars : List Par := params.filter isInvAct

@[expose] def maskOf (P : ℕ → Bool) : ℕ :=
  (List.range 256).foldl (fun m v => if P v then m ||| (1 <<< v) else m) 0

@[expose] def fixM (p : Par) : ℕ := maskOf fun v => act p v == v

@[expose] def comM (p : Par) : ℕ :=
  (List.range 256).foldl (fun m v => m ||| (1 <<< code (gmap p.A p.B p.s p.t (decode v) +
    decode v))) 0

@[expose] def FULL : ℕ := maskOf fun _ => true

@[expose] def lo (k : ℕ) : ℕ := maskOf fun v => !v.testBit k

@[expose] def loTab : Array ℕ := #[lo 0, lo 1, lo 2, lo 3, lo 4, lo 5, lo 6, lo 7]

@[expose] def tr1 (m k : ℕ) : ℕ :=
  ((m &&& loTab.getD k 0) <<< (2 ^ k)) ||| ((m >>> (2 ^ k)) &&& loTab.getD k 0)

@[expose] def transB (m w : ℕ) : ℕ → ℕ
  | 0 => m
  | j + 1 => if w.testBit j then tr1 (transB m w j) j else transB m w j

@[expose] def sumOne (m w : ℕ) : ℕ := (m ||| transB m w 8) &&& FULL

@[expose] def basisOf (m : ℕ) : List ℕ :=
  ((List.range 256).foldl (fun (acc : List ℕ × ℕ) v =>
    if m.testBit v && !acc.2.testBit v then (v :: acc.1, sumOne acc.2 v) else acc) ([], 1)).1

structure IData where
  fix : ℕ
  com : ℕ
  bas : List ℕ

@[expose] def dataOf (p : Par) : IData := let c := comM p; ⟨fixM p, c, basisOf c⟩

@[expose] def invData : List IData := invPars.map dataOf

@[expose] def popcount (m : ℕ) : ℕ := (List.range 256).countP fun v => m.testBit v

@[expose] def dedupSorted : List ℕ → List ℕ
  | a :: b :: l => if a == b then dedupSorted (b :: l) else a :: dedupSorted (b :: l)
  | l => l

@[expose] def sortDedup (l : List ℕ) : List ℕ := dedupSorted (l.mergeSort (· ≤ ·))

@[expose] def closeBy (gens : List (ℕ → ℕ)) : ℕ → List ℕ → List ℕ → List ℕ
  | 0, all, _ => all
  | n + 1, all, front =>
    let new := sortDedup (front.flatMap fun W => gens.map fun g => g W)
    let fresh := new.filter fun x => !(all.contains x)
    if fresh.isEmpty then all else closeBy gens n (sortDedup (all ++ fresh)) fresh

@[expose] def capL : List ℕ := closeBy (invData.map fun d => (· &&& d.fix)) 12 [FULL] [FULL]

@[expose] def plusL : List ℕ :=
  closeBy (invData.map fun d => fun U => d.bas.foldl sumOne U) 12 [1] [1]

@[expose] def bfind (a : Array ℕ) (x : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
    if lo < hi then
      if a.getD ((lo + hi) / 2) 0 == x then true
      else if a.getD ((lo + hi) / 2) 0 < x then bfind a x fuel ((lo + hi) / 2 + 1) hi
      else bfind a x fuel lo ((lo + hi) / 2)
    else false

@[expose] def memS (a : Array ℕ) (x : ℕ) : Bool := bfind a x 20 0 a.size

@[expose] def elat (W : ℕ) (d : IData) : Bool := (W &&& d.fix == W) && (d.com &&& W == d.com)

@[expose] def count (W : ℕ) : ℕ := invData.countP (elat W)

@[expose] def capA : Array ℕ := capL.toArray

@[expose] def plusA : Array ℕ := plusL.toArray

@[expose] def capOK : Bool :=
  memS capA FULL &&
  capL.all (fun W => invData.all fun d => memS capA (W &&& d.fix)) &&
  capL.all (fun W => count W ^ 4 * popcount W ^ 3 ≤ 2 ^ 24)

@[expose] def plusOK : Bool :=
  memS plusA 1 &&
  plusL.all (fun U => invData.all fun d => memS plusA (d.bas.foldl sumOne U)) &&
  plusL.all (fun U => U == 1 || count U < popcount U)

@[expose] def basOK : Bool := invData.all fun d => d.bas.foldl sumOne 1 == d.com

@[expose] def qCheck : Bool := capOK && plusOK && basOK

end CFSG.Quasithin.H13.Ch9.L34Q
