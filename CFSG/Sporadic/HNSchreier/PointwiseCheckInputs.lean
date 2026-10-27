
module

public import CFSG.Sporadic.HNSchreier.SylowCheckBase
public import CFSG.Sporadic.HNSchreier.PointwiseData
public meta import CFSG.Sporadic.HNSchreier.SylowCheckBase
public meta import CFSG.Sporadic.HNSchreier.PointwiseData

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[expose] def boolWordArr (A B : Array Nat) : List Bool → Array Nat
  | [] => pid 12
  | b :: w => pcomp 12 (if b then A else B) (boolWordArr A B w)

@[noinline, expose] def pointwiseChecks (O : VOrbit) : Bool :=
  let n := hnsData.n
  let a0 := natTab O.alpha
  let a1 := natTab O.beta
  let ai := pinvs n #[a0, a1]
  let regs := progRegs n (initRegs n a0 a1) Data.subgroupProgram
  let hS := extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords
  let hSi := pinvs n hS
  let k1 := pword n hS hSi PointwiseData.k1
  let k2 := pword n hS hSi PointwiseData.k2
  let hw := pword n hS hSi PointwiseData.hw
  let hwi := pinvs n #[hw]
  let c1 := pword n hS hSi PointwiseData.c1
  let nS := extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
    LocalData.strongWords
  let nSi := pinvs 12 nS
  let P := natArr PointwiseData.natP
  let Q := natArr PointwiseData.natQ
  let P2 := natArr PointwiseData.natP2
  let g0 := PointwiseData.g0
  let B := Data.baseList
  ai.size == 2 && pisInv n a0 ai[0]! && pisInv n a1 ai[1]! &&
    g0.all (fun l => l == 1 || l == 2) && plettersOK 17 PointwiseData.hw &&
    plettersOK 17 PointwiseData.k1 && plettersOK 17 PointwiseData.k2 &&
    plettersOK 17 PointwiseData.c1 && hwi.size == 1 && pisInv n hw hwi[0]! &&
    seedWordIdx a0 a1 g0 hw[0]! == 88 && seedWordIdx a0 a1 g0 hw[88]! == 0 &&
    allBelowN n (fun x => (k1[x]! == x && k2[x]! == x) == (x == 0 || x == 88)) &&
    B.all (fun b =>
      seedWordIdx a0 a1 g0 hw[k1[(hwi[0]!)[seedWordInvIdx ai[0]! ai[1]! g0 b]!]!]! == c1[b]!) &&
    peq 12 (pword 12 nS nSi PointwiseData.k1) P && peq 12 (pword 12 nS nSi PointwiseData.k2) Q &&
    peq 12 (pword 12 nS nSi PointwiseData.c1) P2 &&
    allBelowN 12 (fun j => ((boolWordArr P Q PointwiseData.ufix)[j]! == j) == (j == 0)) &&
    PointwiseData.tw.length == 12 &&
    allBelowN 12 (fun b => (boolWordArr P Q PointwiseData.tw[b]!)[0]! == b) &&
    P[7]! == 7 && allBelowN 12 (fun j => P2[j]! != j)

end CFSG.Sporadic.HNSchreier.Native
