module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.PermData
public import CFSG.RankThree.Native.PermEnumeration

public section

namespace CFSG.OddTranspositions.PartThree.PlusFrame

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer CFSG.RankThree.Native

@[expose] def frameArr : Array ℕ := #[18, 31, 36, 41]

@[expose] def t0Gens : Array (Array ℕ) := #[
  #[4, 52, 26, 50, 30, 19, 55, 47, 43, 35, 56, 37, 25, 5, 11, 58, 44, 21, 36, 24, 48, 34, 2, 10,
    13, 7, 28, 40, 22, 39, 59, 41, 6, 20, 57, 27, 18, 46, 33, 54, 9, 31, 23, 49, 1, 8, 14, 12, 38,
    45, 15, 29, 16, 32, 51, 53, 42, 17, 3, 0],
  #[8, 11, 13, 3, 10, 6, 5, 7, 0, 14, 4, 1, 12, 2, 9, 15, 46, 26, 41, 28, 23, 55, 34, 20, 53, 50,
    17, 37, 19, 40, 49, 36, 57, 45, 22, 54, 31, 27, 56, 44, 29, 18, 59, 48, 39, 33, 16, 58, 43, 30,
    25, 52, 51, 24, 35, 21, 38, 32, 47, 42],
  #[0, 40, 32, 58, 59, 24, 22, 25, 23, 44, 45, 46, 47, 13, 14, 50, 35, 34, 18, 19, 20, 21, 6, 8, 5,
    7, 53, 52, 55, 54, 30, 31, 2, 48, 17, 16, 36, 37, 38, 39, 1, 41, 43, 42, 9, 10, 11, 12, 33, 56,
    15, 51, 27, 26, 29, 28, 49, 57, 3, 4]]

@[expose] def derivOrder : Array ℕ :=
  #[18, 31, 36, 41, 0, 1, 16, 10, 6, 5, 3, 2, 4, 7, 8, 9, 11, 12, 13, 14, 17, 19, 15, 20, 21, 22,
    23, 24, 25, 26, 27, 28, 29, 30, 32, 33, 34, 35, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 49,
    50, 51, 52, 53, 54, 55, 56, 57, 58, 59]

@[expose] def derivSrc : Array ℕ :=
  #[0, 0, 0, 0, 0, 0, 1082, 1002, 71, 361, 302, 187, 4, 7, 6, 66, 11, 10, 64, 14, 2166, 1874, 980,
    1081, 1100, 2467, 2469, 1098, 1096, 1103, 2170, 2163, 1092, 1861, 1889, 1085, 1086, 1862, 1875,
    1111, 1095, 1116, 1091, 1871, 1888, 1124, 2190, 1084, 2165, 1884, 1088, 1118, 1870, 1087, 1127,
    1863, 1869, 1094, 1093, 1129]

@[expose] def dSubsets : List (List (Fin 4)) :=
  [[], [0], [1], [2], [0, 1], [0, 2], [1, 2], [0, 1, 2]]

@[expose] def dImageList (S : List (Fin 4)) : Array ℕ :=
  (S.map fun i => plusTable[frameArr[(i : ℕ)]!]!).foldr (fun row acc => compA 60 row acc) (idA 60)

@[expose] def dActions (_ : Unit := ()) : List (Array ℕ) := dSubsets.map dImageList

@[expose] def evenPerms : List (Fin 4 → Fin 4) :=
  [![0, 1, 2, 3], ![0, 2, 3, 1], ![0, 3, 1, 2], ![1, 0, 3, 2], ![1, 2, 0, 3], ![1, 3, 2, 0],
    ![2, 0, 1, 3], ![2, 1, 3, 0], ![2, 3, 0, 1], ![3, 0, 2, 1], ![3, 1, 0, 2], ![3, 2, 1, 0]]

@[expose] def oddPerms : List (Fin 4 → Fin 4) :=
  [![0, 1, 3, 2], ![0, 2, 1, 3], ![0, 3, 2, 1], ![1, 0, 2, 3], ![1, 2, 3, 0], ![1, 3, 0, 2],
    ![2, 0, 3, 1], ![2, 1, 0, 3], ![2, 3, 1, 0], ![3, 0, 1, 2], ![3, 1, 2, 0], ![3, 2, 0, 1]]

@[expose] def isFrame (p : ℕ) : Bool := (List.finRange 4).any fun i => frameArr[(i : ℕ)]! == p

@[expose] def t0Cert (_ : Unit := ()) : ArrCert := enumBfs 60 t0Gens plusBase 40

@[expose] def t0Check (c : ArrCert) : Bool := enumOK 60 t0Gens plusBase c && (c.pts.size == 32)

@[expose] def t0SubCheck (E : ArrCert) : Bool :=
  (List.range t0Gens.size).all fun k => E.pts.toList.any (eqA 60 t0Gens[k]!)

@[expose] def frameMemCheck (c : ArrCert) : Bool :=
  (List.range 60).all fun k =>
    (c.pts.toList.any (eqA 60 plusTable[k]!)) == isFrame k

@[expose] def frameProdCheck (_ : Unit := ()) : Bool :=
  let p := compA 60 (compA 60 (compA 60 plusTable[18]! plusTable[31]!) plusTable[36]!)
    plusTable[41]!
  eqA 60 p (idA 60)

@[expose] def otherRows (i : Fin 4) : Array (Array ℕ) :=
  ((List.finRange 4).filterMap fun j =>
    if j = i then none else some plusTable[frameArr[(j : ℕ)]!]!).toArray

@[expose] def cardCheck (_ : Unit := ()) : Bool :=
  (List.finRange 4).all fun i =>
    let c := enumBfs 60 (otherRows i) plusBase 16
    enumOK 60 (otherRows i) plusBase c && (c.pts.size == 8)

@[expose] def mapsFrame (a : Array ℕ) : Bool :=
  (List.finRange 4).all fun i =>
    (List.finRange 4).any fun j => a[frameArr[(i : ℕ)]!]! == frameArr[(j : ℕ)]!

@[expose] def matchesPerm (a : Array ℕ) (σ : Fin 4 → Fin 4) : Bool :=
  (List.finRange 4).all fun i => a[frameArr[(i : ℕ)]!]! == frameArr[((σ i : Fin 4) : ℕ)]!

@[expose] def evenCheck (E : ArrCert) : Bool :=
  allLt E.pts.size fun k =>
    let a := E.pts[k]!
    !(mapsFrame a) || (oddPerms.all fun σ => !(matchesPerm a σ))

@[expose] def alternatingCheck (E : ArrCert) : Bool :=
  evenPerms.all fun σ => E.pts.toList.any fun a => matchesPerm a σ

@[expose] def initFun (a b : ℕ) : ℕ → ℕ := fun p =>
  if isFrame p then p else if p = 0 then a else if p = 1 then b else 0

@[expose] def initArr (a b : ℕ) : Array ℕ := ((List.range 60).map (initFun a b)).toArray

@[expose] def stepVal (a b : ℕ) (f : Array ℕ) (k : ℕ) : ℕ :=
  let s := derivSrc[k]!
  if s = 0 then initFun a b derivOrder[k]!
  else
    let x := (s - 1) / 60
    let y := (s - 1) % 60
    (plusTable[f[x]!]!)[f[y]!]!

@[expose] def deriveFun (a b : ℕ) (f : Array ℕ) : ℕ → Array ℕ
  | 0 => f
  | k + 1 =>
      let g := deriveFun a b f k
      g.set! (derivOrder[k]!) (stepVal a b g k)

@[expose] def deriveArr (a b : ℕ) : Array ℕ := deriveFun a b (initArr a b) 60

@[expose] def isTableHomArr (f : Array ℕ) : Bool :=
  (List.range 60).all fun i => (List.range 60).all fun j =>
    f[(plusTable[i]!)[j]!]! == (plusTable[f[i]!]!)[f[j]!]!

@[expose] def matchesArr (f g : Array ℕ) : Bool := (List.range 60).all fun p => f[p]! == g[p]!

@[expose] def autCheck (_ : Unit := ()) : Bool :=
  (List.range 60).all fun a => (List.range 60).all fun b =>
    let f := deriveArr a b
    !(isTableHomArr f) || ((dActions ()).any fun g => matchesArr f g)

@[expose] def occursBefore (p k : ℕ) : Bool :=
  (List.range k).any fun j => derivOrder[j]! == p

@[expose] def derivValidCheck (_ : Unit := ()) : Bool :=
  (List.range 60).all (fun k => derivOrder[k]! < 60) &&
    (List.range 60).all (fun p => (List.range 60).any (fun j => derivOrder[j]! == p)) &&
    (List.range 60).all (fun k => (List.range k).all (fun j => derivOrder[j]! != derivOrder[k]!)) &&
    (List.range 60).all fun k =>
      let p := derivOrder[k]!
      let s := derivSrc[k]!
      if s = 0 then (isFrame p || p = 0 || p = 1)
      else
        let x := (s - 1) / 60
        let y := (s - 1) % 60
        (x < 60) && (y < 60) && ((plusTable[x]!)[y]! == p) && occursBefore x k &&
          occursBefore y k

@[expose] def frameCheck (_ : Unit := ()) : Bool :=
  let c := t0Cert ()
  let E := plusEnum ()
  t0Check c && t0SubCheck E && frameMemCheck c && frameProdCheck () && cardCheck () &&
    evenCheck E && alternatingCheck E && autCheck () && derivValidCheck ()

end CFSG.OddTranspositions.PartThree.PlusFrame
