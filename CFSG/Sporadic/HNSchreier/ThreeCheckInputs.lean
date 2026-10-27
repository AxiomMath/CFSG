
module

public import CFSG.Sporadic.HNSchreier.LocalCheckBase
public import CFSG.Sporadic.HNSchreier.FAData
public meta import CFSG.Sporadic.HNSchreier.LocalCheckBase
public meta import CFSG.Sporadic.HNSchreier.FAData

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[expose] def fixListOK (n : Nat) (t : Array Nat) (L : List Nat) : Bool :=
  (L.zip L.tail).all (fun p => decide (p.1 < p.2)) &&
    L.all (fun x => decide (x < n) && t[x]! == x) &&
    ((List.range n).countP fun x => t[x]! == x) == L.length

@[expose] def seedWordArr (n : Nat) (a0 a1 : Array Nat) : List Nat → Array Nat
  | [] => pid n
  | l :: w => pcomp n (if l = 1 then a0 else a1) (seedWordArr n a0 a1 w)

@[inline, expose] def inTree (T : Tree) (x : Nat) : Bool :=
  ap T.pos x < T.pts.size && ap T.pts (ap T.pos x) == x

@[noinline, expose] def threeChecks (O : VOrbit) : Bool :=
  let n := hnsData.n
  let a0 := natTab O.alpha
  let a1 := natTab O.beta
  let regs := progRegs n (initRegs n a0 a1) Data.subgroupProgram
  let hS := extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords
  let hSi := pinvs n hS
  let s1 := pword n hS hSi FAData.sWords[0]!
  let s3 := pword n hS hSi FAData.sWords[2]!
  let c1 := FAData.c1Words.map fun w => pword n hS hSi w
  let g3 := pcomp n (seedWordArr n a0 a1 FAData.g3Root) (pword n hS hSi FAData.g3H)
  let c3 := (FAData.c3Words.map fun w => pword n hS hSi w).push g3
  let L1 := c1.map toTable
  let L3 := c3.map toTable
  let lv1 := Array.range L1.size
  let lv3 := Array.range L3.size
  let T0 := treeBFS n 0 L1 lv1
  let T1 := treeBFS n 1047 L1 lv1
  let T2 := treeBFS n 119497 L1 lv1
  let T3 := treeBFS n 0 L3 lv3
  regs.size == 11 && strongOK n regs[1]! regs[2]! hS LocalData.strongWords &&
    FAData.sWords.size == 4 && FAData.sFixed.size == 4 &&
    allBelowN 4 (fun k => plettersOK 17 FAData.sWords[k]! &&
      fixListOK n (pword n hS hSi FAData.sWords[k]!) FAData.sFixed[k]!) &&
    FAData.c1Words.size == 8 && FAData.c3Words.size == 6 &&
    allBelowN 8 (fun j => plettersOK 17 FAData.c1Words[j]! &&
      peq n (pcomp n c1[j]! s1) (pcomp n s1 c1[j]!)) &&
    allBelowN 6 (fun j => plettersOK 17 FAData.c3Words[j]!) &&
    plettersOK 17 FAData.g3H && FAData.g3Root.all (fun l => l == 1 || l == 2) &&
    allBelowN 7 (fun j => peq n (pcomp n c3[j]! s3) (pcomp n s3 c3[j]!)) &&
    L1.size == 8 && L3.size == 7 && L1.all (fun t => t.size == n) &&
    L3.all (fun t => t.size == n) &&
    treeOK n 0 T0 L1 lv1 && treeOK n 1047 T1 L1 lv1 && treeOK n 119497 T2 L1 lv1 &&
    treeOK n 0 T3 L3 lv3 &&
    T0.pts.size == 1 && T1.pts.size == 560 && T2.pts.size == 84 && T3.pts.size == 60 &&
    (FAData.sFixed[0]!).all (fun x => inTree T0 x || inTree T1 x || inTree T2 x)

end CFSG.Sporadic.HNSchreier.Native
