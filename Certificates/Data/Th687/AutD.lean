module

public import Certificates.Data.Th687.DModel
public import Certificates.Data.CFSGNative.ONSchreier.Compact

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.CosetTable CFSG.PSL3Four.Native

@[expose] def piArr : Array Tab := #[
  #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25,
    26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49,
    50],
  #[5, 3, 13, 0, 9, 1, 22, 21, 15, 2, 17, 16, 20, 4, 31, 12, 7, 6, 26, 25, 8, 11, 10, 32, 43, 14,
    23, 38, 36, 39, 37, 19, 18, 41, 40, 44, 34, 24, 33, 35, 28, 27, 46, 30, 29, 47, 45, 42, 50, 48,
    49],
  #[1, 0, 4, 3, 2, 5, 10, 11, 8, 9, 6, 7, 12, 13, 19, 20, 16, 17, 18, 14, 15, 21, 22, 23, 30, 25,
    32, 27, 28, 35, 24, 31, 26, 33, 34, 29, 40, 37, 41, 39, 36, 38, 45, 43, 44, 42, 46, 47, 48, 49,
    50],
  #[5, 3, 13, 1, 9, 0, 22, 21, 20, 4, 17, 16, 15, 2, 31, 12, 11, 10, 32, 25, 8, 7, 6, 26, 43, 19,
    23, 41, 40, 39, 37, 14, 18, 38, 36, 44, 34, 30, 33, 29, 28, 27, 46, 24, 35, 47, 42, 45, 50, 48,
    49],
  #[5, 3, 13, 0, 9, 1, 22, 21, 7, 6, 17, 16, 11, 10, 37, 12, 15, 2, 26, 43, 8, 20, 4, 32, 25, 24,
    33, 38, 36, 28, 31, 30, 27, 41, 40, 34, 44, 14, 23, 35, 39, 18, 46, 19, 29, 47, 45, 42, 49, 50,
    48],
  #[1, 0, 10, 5, 6, 3, 4, 20, 12, 13, 2, 15, 8, 9, 30, 11, 21, 22, 33, 24, 7, 16, 17, 27, 19, 37,
    32, 23, 44, 35, 14, 43, 26, 18, 39, 29, 40, 25, 41, 34, 36, 38, 45, 31, 28, 42, 47, 46, 50, 48,
    49],
  #[5, 3, 13, 1, 9, 0, 22, 21, 11, 10, 17, 16, 7, 6, 37, 12, 20, 4, 32, 43, 8, 15, 2, 26, 25, 30,
    33, 41, 40, 28, 31, 24, 27, 38, 36, 34, 44, 19, 23, 29, 39, 18, 46, 14, 35, 47, 42, 45, 49, 50,
    48],
  #[1, 0, 10, 3, 6, 5, 4, 20, 8, 9, 2, 15, 12, 13, 30, 11, 16, 17, 27, 24, 7, 21, 22, 33, 19, 43,
    32, 18, 39, 35, 14, 37, 26, 23, 44, 29, 40, 31, 41, 28, 36, 38, 45, 25, 34, 42, 46, 47, 50, 48,
    49]
]

@[expose] def iotaTab : Tab := #[1, 0, 4, 5, 2, 3, 10, 11, 12, 13, 6, 7, 8, 9, 19, 20, 21, 22, 23,
  14, 15, 16, 17, 18, 30, 31, 32, 33, 34, 35, 24, 25, 26, 27, 28, 29, 40, 43, 41, 44, 36, 38, 45,
  37, 39, 42, 47, 46, 48, 50, 49]

@[expose] def wYList : List (List (List (Fin 6 × Bool))) := [
  [[(0, false)], [(1, false)], [(2, false)], [(3, false)], [(4, true)], [(5, true)]],
  [[(0, false)], [(1, false)], [(2, false)], [(3, false)], [(5, true), (4, false), (0, false)],
    [(5, true)]],
  [[(0, false)], [(1, false)], [(2, false)], [(3, false)], [(0, true), (4, true)], [(5, true)]],
  [[(0, false)], [(1, false)], [(2, false)], [(3, false)], [(5, true), (4, false)], [(5, true)]],
  [[(0, false)], [(1, false)],
    [(2, false), (3, false), (2, false), (4, false), (2, false), (4, true), (2, false)],
    [(3, false)], [(5, false), (4, true)], [(5, true)]],
  [[(0, false)], [(1, false)],
    [(2, false), (3, false), (2, false), (4, true), (2, false), (4, false), (2, false)],
    [(3, false)], [(5, true), (4, false), (0, false)], [(5, true)]],
  [[(0, false)], [(1, false)],
    [(2, false), (3, false), (2, false), (4, false), (2, false), (4, true), (2, false)],
    [(3, false)], [(5, false), (0, true), (4, true)], [(5, true)]],
  [[(0, false)], [(1, false)],
    [(2, false), (3, false), (2, false), (4, true), (2, false), (4, false), (2, false)],
    [(3, false)], [(5, true), (4, false)], [(5, true)]]
]

@[expose] def mWord : Twist → List (Fin 6 × Bool)
  | .id => [(5, true), (3, false), (0, true), (4, true)]
  | .f1 => [(5, true), (3, false), (4, false)]
  | .f3 => [(5, true), (3, false), (0, true), (4, true)]
  | .f13 => [(5, true), (3, false), (4, false)]

@[expose] def hW : Fin 2 → List (Fin 6 × Bool)
  | 0 => [(1, true), (2, false), (5, true)]
  | 1 => [(4, false), (2, false), (3, false)]

@[expose] def x1W : List (Fin 6 × Bool) := [(1, true), (2, true), (5, false)]

@[expose] def lW : Fin 6 → List (Fin 2 × Bool)
  | 0 => [(1, true), (1, true), (1, true), (1, true), (1, true), (1, true)]
  | 1 => [(0, true), (1, true), (0, true), (0, true), (1, true), (0, true), (1, true), (1, true)]
  | 2 => [(1, true), (0, true), (1, true), (0, false), (0, false), (1, false), (0, true),
    (1, false), (0, true)]
  | 3 => [(0, true), (0, true), (1, true), (1, true), (1, true), (0, true), (1, true), (0, true),
    (0, true)]
  | 4 => [(0, false), (1, true), (0, false), (0, false), (1, true), (1, true), (0, true)]
  | 5 => [(0, false), (1, true), (1, true), (0, false), (1, true), (1, true)]

abbrev OutD := Twist × Bool

@[expose] def outList : List OutD :=
  [(.id, false), (.f1, false), (.f3, false), (.f13, false), (.id, true), (.f1, true), (.f3, true),
    (.f13, true)]

@[expose] def outIdx : OutD → Nat
  | (k, b) => (if b then 4 else 0) + (match k with | .id => 0 | .f1 => 1 | .f3 => 2 | .f13 => 3)

@[expose] def piTab (k : OutD) : Tab := piArr[outIdx k]!

@[expose] def wYD (k : OutD) (j : Fin 6) : List (Fin 6 × Bool) :=
  (wYList.getD (outIdx k) []).getD j.val []

@[expose] def autTests : List (List (Fin 2 × Bool)) :=
  RD.map (substWord (List.ofFn lW)) ++
    List.ofFn fun i => substWord (List.ofFn lW) (hW i) ++ [(i, false)]

@[expose] def tpow (x : Tab) : Nat → Tab
  | 0 => idTab 51
  | n + 1 => comp 51 x (tpow x n)

@[expose] def ord24 (x : Tab) : Bool :=
  tpow x 24 == idTab 51 && !(tpow x 12 == idTab 51) && !(tpow x 8 == idTab 51)

@[expose] def hTab (i : Fin 2) : Tab := wTab letArr (letInv ()) (hW i)

@[expose] def hInv (i : Fin 2) : Tab := wTab letArr (letInv ()) (FreeGroup.invRev (hW i))

@[expose] def x1Tab (_ : Unit := ()) : Tab := wTab letArr (letInv ()) x1W

@[expose] def x1Inv (_ : Unit := ()) : Tab := wTab letArr (letInv ()) (FreeGroup.invRev x1W)

@[expose] def xOrb (x : Tab) : Enum := orbitBFS 51 letArr (letInv ()) x 3456

@[expose] def dEnumInv (_ : Unit := ()) : Array Tab := (dEnum ()).tabs.map (invTab 51)

@[expose] def conjOK (p pinv x y : Tab) : Bool := comp 51 (comp 51 p x) pinv == y

@[expose] def piCheck (_ : Unit := ()) : Bool :=
  let GI := letInv ()
  outList.all fun k =>
    let p := piTab k
    let pinv := invTab 51 p
    CFSG.ONSchreier.Native.pisInv 51 p pinv && p.size == 51 && pinv.size == 51 &&
      (List.finRange 6).all (fun j => conjOK pinv p letArr[j.val]! (wTab letArr GI (wYD k j))) &&
      conjOK p pinv letArr[0]! letArr[0]! && conjOK p pinv letArr[5]! letArr[5]!

@[expose] def iotaCheck (_ : Unit := ()) : Bool :=
  let GI := letInv ()
  let ii := invTab 51 iotaTab
  CFSG.ONSchreier.Native.pisInv 51 iotaTab ii && iotaTab.size == 51 && ii.size == 51 &&
    (List.finRange 6).all fun j =>
      conjOK iotaTab ii letArr[j.val]! (if j.val == 5 then GI[5]! else letArr[j.val]!)

@[expose] def partnerCheck (_ : Unit := ()) : Bool :=
  let GI := letInv ()
  let ii := invTab 51 iotaTab
  [Twist.id, .f1, .f3, .f13].all fun k =>
    let m := wTab letArr GI (mWord k)
    let mi := wTab letArr GI (FreeGroup.invRev (mWord k))
    let p0 := piTab (k, false)
    let p1 := piTab (k, true)
    let p0i := invTab 51 p0
    let p1i := invTab 51 p1
    (List.finRange 6).all fun j =>
      comp 51 (comp 51 p0 letArr[j.val]!) p0i ==
        comp 51 (comp 51 iotaTab
          (comp 51 (comp 51 p1 (comp 51 (comp 51 mi letArr[j.val]!) m)) p1i)) ii

@[expose] def hGenCheck (_ : Unit := ()) : Bool :=
  let H := #[hTab 0, hTab 1]
  let HI := #[hInv 0, hInv 1]
  (List.finRange 6).all (fun j => wTab H HI (lW j) == letArr[j.val]!) &&
    ord24 (hTab 0) && autTests.all fun S => wTab H HI S == idTab 51

@[expose] def cover24Check (_ : Unit := ()) : Bool :=
  let GI := letInv ()
  let x0 := hTab 0
  let x1 := x1Tab ()
  let O0 := xOrb x0
  let O1 := xOrb x1
  let i0 := indexOf O0.tabs
  let i1 := indexOf O1.tabs
  let E := dEnum ()
  orbitOK 51 letArr GI x0 O0 && orbitOK 51 letArr GI x1 O1 &&
    allBelow E.tabs.size fun i =>
      let x := E.tabs[i]!
      !(ord24 x) || found i0 O0.tabs x || found i1 O1.tabs x

@[expose] def twTab (k : OutD) (i : Fin 2) : Tab :=
  comp 51 (comp 51 (piTab k) (hTab i)) (invTab 51 (piTab k))

@[expose] def twList (_ : Unit := ()) : List (OutD × Tab × Tab) :=
  outList.map fun k => (k, twTab k 0, twTab k 1)

@[expose] def autPairOK (F : List (OutD × Tab × Tab)) (E : Enum) (EI : Array Tab)
    (x xi y yi : Tab) : Bool :=
  !(autTests.all fun S => wTab #[x, y] #[xi, yi] S == idTab 51) ||
    F.any fun f => anyBelow E.tabs.size fun mi =>
      conjOK E.tabs[mi]! EI[mi]! f.2.1 x && conjOK E.tabs[mi]! EI[mi]! f.2.2 y

@[expose] def autCheck (_ : Unit := ()) : Bool :=
  let F := twList ()
  let E := dEnum ()
  let EI := dEnumInv ()
  let x0 := hTab 0
  let x0i := hInv 0
  let x1 := x1Tab ()
  let x1i := x1Inv ()
  allBelow E.tabs.size fun i =>
    autPairOK F E EI x0 x0i E.tabs[i]! EI[i]! && autPairOK F E EI x1 x1i E.tabs[i]! EI[i]!

end CFSG.Sporadic.Th.Recog
