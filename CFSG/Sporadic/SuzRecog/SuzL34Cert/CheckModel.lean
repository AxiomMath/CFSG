module

public import CFSG.Sporadic.SuzRecog.C1ModelTests

public section

namespace CFSG.Sporadic.SuzRecog.SuzL34Cert

open CFSG.PSL3Four.Native CFSG.Sporadic.SuzRecog CFSG.Sporadic.SuzRecog.C1Model
  CFSG.Sporadic.SuzOddCore CFSG.ComponentClassification.AS81.SuzB0

abbrev Dec := List Nat × Nat

@[expose] def s1pDecs : List Dec :=
  [([4, 9, 8, 1, 3, 1], 20), ([6, 8, 1, 2, 6, 1], 42), ([3, 1, 2, 1, 3], 0), ([], 56)]

@[expose] def l1Decs : List Dec :=
  [([], 1), ([], 10), ([], 93), ([8, 9, 8, 9, 4], 99)]

@[expose] def m1Decs : List Dec :=
  [([5, 3, 8, 9, 3, 1], 50), ([], 53), ([], 64), ([], 23), ([9, 4, 6, 4, 2], 73),
    ([4, 3, 9, 5, 6, 1], 106), ([8, 9, 8, 9, 4], 105), ([9, 8, 2, 9, 4], 77)]

@[expose] def cl1Decs : List Dec :=
  [([6, 5, 9, 8, 3, 2], 4), ([3, 7, 8, 5], 72), ([5, 8, 9, 7, 4, 5], 22),
    ([2, 9, 7, 9, 7, 2], 31)]

@[expose] def nl1Decs : List Dec :=
  [([2, 7, 1, 5, 2], 66), ([1, 9, 5, 3, 7], 84)]

@[expose] def m21Decs : List Dec :=
  [([], 86), ([], 1), ([8], 110), ([8], 0)]

@[expose] def l1CompDecs : List Dec :=
  [([8], 0), ([8], 110)]

@[expose] def tauDec : Dec := ([6, 7, 8, 4], 78)

@[expose] def lam0Dec : Dec := ([9, 7, 5, 2, 7, 3], 4)

@[expose] def aDec : Dec := ([7, 8, 5, 3], 95)

@[expose] def ntl1Decs : List Dec :=
  [([8], 110), ([8], 0), ([7, 8, 5, 3], 2), ([], 1), ([4, 3, 9, 5, 6, 1], 106), ([], 87),
    ([8, 1, 2, 1], 34), ([9, 8, 2, 9, 4], 71)]

@[expose] def tbarTabs : Array Tab :=
  #[#[0, 1, 5, 4, 3, 2, 6, 7, 9, 8, 12, 13, 10, 11, 15, 14],
    #[0, 1, 4, 5, 2, 3, 6, 7, 15, 14, 11, 10, 13, 12, 9, 8]]

@[expose] def xA : Tab := #[0, 1, 3, 2, 5, 4, 6, 7, 14, 15, 13, 12, 11, 10, 8, 9]

@[expose] def xBs : Array Tab :=
  #[#[0, 8, 7, 15, 10, 2, 13, 5, 9, 1, 14, 6, 3, 11, 4, 12],
    #[0, 8, 5, 13, 15, 7, 10, 2, 9, 1, 12, 4, 6, 14, 3, 11],
    #[0, 8, 15, 7, 3, 11, 12, 4, 9, 1, 6, 14, 10, 2, 5, 13],
    #[0, 8, 12, 4, 7, 15, 11, 3, 9, 1, 5, 13, 14, 6, 2, 10]]

@[expose] def decs (l : List Dec) : Array Tab := (l.map decTab).toArray

@[expose] def bitProd (B : Array Tab) (i : Nat) : Tab :=
  (List.range B.size).foldl (fun r k => if i.testBit k then comp 1782 r B[k]! else r) (idTab 1782)

@[expose] def l1Tabs (_ : Unit := ()) : Array Tab :=
  let B := decs l1Decs
  Array.ofFn (n := 16) fun i => bitProd B i.val

@[expose] def m21Tabs (_ : Unit := ()) : Array Tab :=
  let B := decs m21Decs
  Array.ofFn (n := 16) fun i => bitProd B i.val

@[expose] def isInv (x : Tab) : Bool := comp 1782 x x == idTab 1782 && !(x == idTab 1782)

@[expose] def commAll (x : Tab) (gs : Array Tab) : Bool :=
  gs.all fun g => comp 1782 g x == comp 1782 x g

@[expose] def normsSet (g : Tab) (B : Array Tab) (idxT : Std.HashMap Tab Nat)
    (T : Array Tab) : Bool :=
  let gi := invTab 1782 g
  B.all fun b => found idxT T (conjTab 1782 g gi b)

@[expose] def tupStep (gens ginv : Array Tab) (j : Nat) (x : Tab) : Tab :=
  Array.ofFn (n := 4 * 1782) fun i =>
    let b := i.val / 1782
    let p := i.val % 1782
    (gens[j]!)[x[1782 * b + (ginv[j]!)[p]!]!]!

@[expose] def blockTab (x : Tab) (b : Nat) : Tab :=
  Array.ofFn (n := 1782) fun p => x[1782 * b + p.val]!

@[expose] def tupleRoot (B : Array Tab) : Tab :=
  Array.ofFn (n := 4 * 1782) fun i => (B[i.val / 1782]!)[i.val % 1782]!

@[expose] def f1Check (_ : Unit := ()) : Bool :=
  let G := decs s1pDecs
  let E := enumBFS 1782 G 8192
  let B := decs l1Decs
  let L := l1Tabs ()
  let M := decs m1Decs
  let ME := enumBFS 1782 M 1024
  let Gi := G.map (invTab 1782)
  let idxE := indexOf E.tabs
  let idxL := indexOf L
  let centG := E.tabs.filter fun t => commAll t G
  let centB := E.tabs.filter fun t => commAll t B
  let centM := ME.tabs.filter fun t => commAll t M
  enumOK 1782 G E && E.tabs.size == 8192 &&
    centG.size == 2 && memTab centG tTab &&
    (allBelow L.size fun k => found idxE E.tabs L[k]!) &&
    (allBelow L.size fun i => posOf idxL L L[i]! == i) &&
    (allBelow B.size fun i => isInv B[i]! && commAll B[i]! B) &&
    centB.size == 1024 &&
    enumOK 1782 M ME && ME.tabs.size == 1024 &&
    (allBelow M.size fun i => commAll M[i]! B) &&
    centM.size == 16 && allBelow centM.size fun k => found idxL L centM[k]! &&
    allBelow E.tabs.size fun k =>
      !(isInv E.tabs[k]! && !found idxL L E.tabs[k]!) ||
        (let e := E.tabs[k]!
         let O := orbitBFS 1782 G Gi e 8192
         orbitOK 1782 G Gi e O && decide (9 ≤ O.tabs.size))

@[expose] def f2Check (_ : Unit := ()) : Bool :=
  let B := decs l1Decs
  let L := l1Tabs ()
  let idxL := indexOf L
  let C := LocalR.fusionGens
  let Ci := C.map (invTab 1782)
  let root := tupleRoot B
  let O := bfs (tupStep C Ci) 10 root 1080
  let inL4 (x : Tab) : Bool := allBelow 4 fun b => found idxL L (blockTab x b)
  let CL := decs cl1Decs
  let CE := enumBFS 1782 CL 3072
  let N := decs nl1Decs
  let M := decs m1Decs
  let ME := enumBFS 1782 M 1024
  let CG := CL ++ N
  let CGi := CG.map (invTab 1782)
  treeOK (tupStep C Ci) 10 root O && O.tabs.size == 1080 &&
    countBelow O.tabs.size (fun k => inL4 O.tabs[k]!) == 24 &&
    enumOK 1782 CL CE && CE.tabs.size == 3072 &&
    (allBelow CE.tabs.size fun k => commAll CE.tabs[k]! B) &&
    (allBelow N.size fun j => normsSet N[j]! B idxL L) &&
    normalOK 1782 ME.tabs CG CGi M

@[expose] def f3Check (_ : Unit := ()) : Bool :=
  let W := w0T
  let N := decs nl1Decs
  let Ni := N.map (invTab 1782)
  let O := orbitBFS 1782 N Ni W 288
  let L := l1Tabs ()
  let M := decs m1Decs
  let ME := enumBFS 1782 M 1024
  let idxL := indexOf L
  let idxME := indexOf ME.tabs
  orbitOK 1782 N Ni W O && O.tabs.size == 288 &&
    (allBelow O.tabs.size fun k => found idxME ME.tabs O.tabs[k]!) &&
    (allBelow O.tabs.size fun k => !found idxL L O.tabs[k]!) &&
    (allBelow O.tabs.size fun k => fixedCount O.tabs[k]! == 42) &&
    countBelow ME.tabs.size (fun k => isInv ME.tabs[k]! && !found idxL L ME.tabs[k]!) == 288

@[expose] def f4Check (_ : Unit := ()) : Bool :=
  let V := v0Enum.tabs
  let T := t0Enum.tabs
  let idxT := indexOf T
  let vs := V.filter fun x => isInv x && fixedCount x == 54
  let ts := T.filter isInv
  vs.size == 27 && (allBelow vs.size fun k => found idxT T vs[k]!) &&
    ts.size == 27 && allBelow ts.size fun k => fixedCount ts[k]! == 54

@[expose] def f5Check (_ : Unit := ()) : Bool :=
  let T := t0Enum.tabs
  let V := v0Enum.tabs
  let G0 := t0Tabs
  let B := decs l1Decs
  let L := l1Tabs ()
  let M21 := m21Tabs ()
  let Z := T.filter fun t => commAll t G0
  let idxT := indexOf T
  let idxL := indexOf L
  let idxM21 := indexOf M21
  let idxZ := indexOf Z
  let idxV := indexOf V
  let Ti := T.map (invTab 1782)
  let Vg := v0Tabs
  let Vgi := Vg.map (invTab 1782)
  let K := (enumBFS 1782 (decs l1CompDecs) 4).tabs
  let idxK := indexOf K
  let inter := L.filter fun x => found idxM21 M21 x
  let tau := decTab tauDec
  let tauI := invTab 1782 tau
  Z.size == 4 &&
    (allBelow L.size fun k => found idxT T L[k]!) &&
    (allBelow M21.size fun k => found idxT T M21[k]!) &&
    (allBelow L.size fun i => posOf idxL L L[i]! == i) &&
    (allBelow M21.size fun i => posOf idxM21 M21 M21[i]! == i) &&
    (allBelow G0.size fun j => normsSet G0[j]! T idxT T) &&
    inter.size == 4 && allBelow inter.size fun k => found idxZ Z inter[k]! &&
    (allBelow Z.size fun k => found idxL L Z[k]! && found idxM21 M21 Z[k]!) &&
    (allBelow T.size fun k =>
      !isInv T[k]! || found idxL L T[k]! || found idxM21 M21 T[k]!) &&
    (allBelow L.size fun i => allBelow M21.size fun j =>
      found idxZ Z L[i]! || found idxZ Z M21[j]! ||
        !(comp 1782 L[i]! M21[j]! == comp 1782 M21[j]! L[i]!)) &&
    (allBelow L.size fun i =>
      found idxZ Z L[i]! || (centTabs 1782 T L[i]!).size == 16) &&
    (allBelow M21.size fun j =>
      found idxZ Z M21[j]! || (centTabs 1782 T M21[j]!).size == 16) &&
    K.size == 4 &&
    found idxK K (idTab 1782) && found idxL L (idTab 1782) &&
    (allBelow K.size fun k => !found idxL L K[k]! || K[k]! == idTab 1782) &&
    (allBelow Vg.size fun j =>
      allBelow T.size fun k => found idxT T (conjTab 1782 Vg[j]! Vgi[j]! T[k]!)) &&
    found idxV V tau &&
    (allBelow B.size fun k => found idxM21 M21 (conjTab 1782 tau tauI B[k]!)) &&
    (allBelow T.size fun i => found idxZ Z (comp 1782 T[i]! T[i]!)) &&
    (allBelow T.size fun i => allBelow T.size fun j =>
      found idxZ Z (commTab 1782 T[i]! T[j]! Ti[i]! Ti[j]!))

@[expose] def f6Check (_ : Unit := ()) : Bool :=
  let V := v0Enum.tabs
  let B := decs l1Decs
  let L := l1Tabs ()
  let idxL := indexOf L
  let NTL := decs ntl1Decs
  let idxV := indexOf V
  let commB := V.filter fun t => commAll t B
  let normsB := V.filter fun t => normsSet t B idxL L
  commB.size == 64 && normsB.size == 256 &&
    allBelow NTL.size fun k => found idxV V NTL[k]! && normsSet NTL[k]! B idxL L

@[expose] def f7Check (_ : Unit := ()) : Bool :=
  let C0 := c0Tabs
  let G0 := t0Tabs
  let Z := t0Enum.tabs.filter fun t => commAll t G0
  let idxC0 := indexOf C0
  C0.size == 16 &&
    (allBelow C0.size fun i => allBelow C0.size fun j =>
      comp 1782 C0[i]! C0[j]! == comp 1782 C0[j]! C0[i]!) &&
    (allBelow C0.size fun i => comp 1782 C0[i]! C0[i]! == idTab 1782) &&
    (allBelow Z.size fun k => found idxC0 C0 Z[k]!) &&
    ct0Tabs.size == 192

@[expose] def f8Check (_ : Unit := ()) : Bool :=
  let T := t0Enum.tabs
  let W := w0T
  let T11 := T ++ T.map (comp 1782 W)
  let V := v0Enum.tabs
  let Vg := v0Tabs
  let Vgi := Vg.map (invTab 1782)
  let lam0 := decTab lam0Dec
  let lam0I := invTab 1782 lam0
  let a := decTab aDec
  let idxT11 := indexOf T11
  let idxV := indexOf V
  (allBelow Vg.size fun j =>
      allBelow T11.size fun k => found idxT11 T11 (conjTab 1782 Vg[j]! Vgi[j]! T11[k]!)) &&
    (allBelow V.size fun k => found idxT11 T11 (comp 1782 V[k]! V[k]!)) &&
    (allBelow V.size fun k =>
      !(comp 1782 V[k]! V[k]! == W) || found idxT11 T11 (comp 1782 V[k]! lam0I)) &&
    (allBelow V.size fun k =>
      !(isInv V[k]! && !(V[k]! == W) && fixedCount V[k]! == 42 &&
          fixedCount (comp 1782 V[k]! W) == 42) ||
        (!found idxT11 T11 V[k]! && !found idxT11 T11 (comp 1782 V[k]! lam0I))) &&
    found idxV V a && isInv a && !(a == W) && fixedCount a == 42 &&
      fixedCount (comp 1782 a W) == 42 &&
    found idxV V lam0 && comp 1782 lam0 lam0 == W

end CFSG.Sporadic.SuzRecog.SuzL34Cert
