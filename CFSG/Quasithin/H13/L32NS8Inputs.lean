module

public import CFSG.Quasithin.H13.L32NMat8Inputs

public section

namespace CFSG.Quasithin.H13.S8Cert

open Mat8Cert

@[expose] def s8G : List (List ℕ) :=
  [[1, 3, 4, 8, 48, 32, 64, 128], [1, 2, 6, 8, 16, 96, 64, 128], [1, 2, 4, 12, 16, 32, 192, 128],
    [9, 2, 4, 8, 16, 32, 64, 144], [16, 32, 64, 128, 1, 2, 4, 8]]

@[expose] def s8E : List (List ℕ) := elemsOf s8G

@[expose] def s8BasicB : Bool := subB s8G s8E && s8E.length == 40320

@[expose] def inII (v : ℕ) : Bool := v < 16 || v % 16 == 0

@[expose] def iiList : List ℕ := (List.range 256).filter fun v => v != 0 && inII v

@[expose] def stabIB : Bool :=
  s8E.all fun y => iiList.all fun v => !(mv8 y v == v) || (y.take 4).all (· < 16)

@[expose] def vR : ℕ := 18

@[expose] def orbB : Bool :=
  let hs : Std.HashSet ℕ := Std.HashSet.ofList (s8E.map fun y => mv8 y vR)
  (List.range 256).all fun v => v == 0 || inII v || q4N v || hs.contains v

@[expose] def stE : List (List ℕ) := s8E.filter fun x => mv8 x vR == vR

@[expose] def invSt (n : List ℕ) : List ℕ :=
  (stE.find? fun m => mul8 m n == one8).getD one8

@[expose] def z8G : List (List ℕ) :=
  [[13, 2, 6, 10, 16, 224, 80, 144], [160, 16, 128, 80, 2, 5, 10, 4],
    [3, 2, 4, 8, 16, 48, 64, 128], [9, 2, 6, 8, 16, 96, 64, 144]]

@[expose] def zB : Bool :=
  let hs : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf z8G)
  let h8 : Std.HashSet (List ℕ) := Std.HashSet.ofList s8E
  (elemsOf z8G).length == 16 && subB z8G (elemsOf z8G) && z8G.all h8.contains &&
    stE.all (fun n => mul8 (invSt n) n == one8) &&
    stE.all fun x =>
      !(mul8 x x == one8 && stE.all fun n =>
          let c := mul8 (mul8 n x) (invSt n)
          mul8 x c == mul8 c x) || hs.contains x

@[expose] def n8G : List (List ℕ) :=
  [[3, 2, 4, 8, 16, 48, 64, 128], [5, 2, 4, 10, 16, 160, 80, 128], [9, 2, 6, 8, 16, 96, 64, 144]]

@[expose] def nB : Bool :=
  let hZ : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf z8G)
  let hN : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf n8G)
  (elemsOf n8G).length == 8 && subB n8G (elemsOf n8G) && n8G.all hZ.contains &&
    stE.all (fun n => (elemsOf n8G).all fun x => hN.contains (mul8 (mul8 n x) (invSt n))) &&
    (elemsOf z8G).all fun x => hN.contains x ||
      (let B := elemsOf (stE.map fun n => mul8 (mul8 n x) (invSt n))
       B.length == 16 && nodupB B)

@[expose] def eW8 : List (List ℕ × ℕ) :=
  [([3, 2, 4, 8, 16, 48, 64, 128], 33), ([5, 2, 4, 10, 16, 160, 80, 128], 8),
    ([5, 2, 4, 10, 16, 160, 80, 128], 33), ([9, 2, 6, 8, 16, 96, 64, 144], 33)]

@[expose] def eSpan8 : List ℕ := spanN (eW8.map fun p => mv8 p.1 p.2 ^^^ p.2)

@[expose] def nodupN (L : List ℕ) : Bool := decide (L.mergeSort.IsChain (· < ·))

@[expose] def wB : Bool :=
  let hN : Std.HashSet (List ℕ) := Std.HashSet.ofList (elemsOf n8G)
  eW8.all (fun p => hN.contains p.1 && !(b4N p.2 vR)) && eSpan8.length == 16 && nodupN eSpan8

@[expose] def dotN (c w : ℕ) : Bool :=
  (bt c 0 && bt w 0) ^^ (bt c 1 && bt w 1) ^^ (bt c 2 && bt w 2) ^^ (bt c 3 && bt w 3) ^^
    (bt c 4 && bt w 4) ^^ (bt c 5 && bt w 5) ^^ (bt c 6 && bt w 6) ^^ (bt c 7 && bt w 7)

@[expose] def cF : ℕ := 18

@[expose] def fB : Bool :=
  !(dotN cF vR) && (elemsOf n8G).all fun x =>
    eSpan8.any fun w => mv8 x w != (w ^^^ (if dotN cF w then vR else 0))

@[expose] def s8Check : Bool := s8BasicB && stabIB && orbB && zB && nB && wB && fB

end CFSG.Quasithin.H13.S8Cert
