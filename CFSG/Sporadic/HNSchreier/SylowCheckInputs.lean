
module

public import CFSG.Sporadic.HNSchreier.ThreeCheckBase
public import CFSG.Sporadic.HNSchreier.FALocalCheckBase
public import CFSG.Sporadic.HNSchreier.SylowData
public meta import CFSG.Sporadic.HNSchreier.ThreeCheckBase
public meta import CFSG.Sporadic.HNSchreier.FALocalCheckBase
public meta import CFSG.Sporadic.HNSchreier.SylowData

public section

namespace CFSG.Sporadic.HNSchreier.Native

open CFSG.ONSchreier.Native CFSG.Sporadic.F5.Native CFSG.Perm.Native CFSG.Sporadic.Th.Native

@[expose] def pev (G : Array (Array Nat)) (par : Array (Nat × Nat)) : Nat → Nat → Nat → Nat
  | 0, _, y => y
  | f + 1, i, y => if i = 0 then y else G[(par[i]!).2]![pev G par f (par[i]!).1 y]!

@[expose] def seedWordInvIdx (a0i a1i : Array Nat) (w : List Nat) (y : Nat) : Nat :=
  w.foldl (fun y l => (if l = 1 then a0i else a1i)[y]!) y

@[expose] def treeReach (tree : Array (Nat × Nat)) : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, i => (tree[i]!).2 == 0 || treeReach tree f (tree[i]!).1

@[expose] def classLabels (cls : Array (List Nat)) : Array Nat := Id.run do
  let mut lab : Array Nat := Array.replicate 729 cls.size
  for c in [0:cls.size] do
    for i in cls[c]! do
      lab := lab.set! i c
  return lab

@[noinline, expose] def sylowChecks (O : VOrbit) : Bool :=
  let n := hnsData.n
  let a0 := natTab O.alpha
  let a1 := natTab O.beta
  let ai := pinvs n #[a0, a1]
  let regs := progRegs n (initRegs n a0 a1) Data.subgroupProgram
  let hS := extendStrong n #[regs[1]!, regs[2]!] LocalData.strongWords
  let hSi := pinvs n hS
  let g3 := pcomp n (seedWordArr n a0 a1 FAData.g3Root) (pword n hS hSi FAData.g3H)
  let c3 := (FAData.c3Words.map fun w => pword n hS hSi w).push g3
  let G := (FAData.pLift.map fun lw => lw.foldl (fun acc l => pcomp n acc c3[l - 1]!) (pid n)).push
    (pword n hS hSi FAData.pKernel)
  let Gi := pinvs n G
  let par := FAData.pParents
  let B := Data.baseList
  let bimgs := Array.ofFn (n := 729) fun i => B.map fun b => pev G par 729 i.val b
  let mark := Array.ofFn (n := 729) fun i => SylowData.order3.contains i.val
  let lab := classLabels FAData.wClass
  let nS := extendStrong 12 #[natArr LocalData.natGen1, natArr LocalData.natGen2]
    LocalData.strongWords
  let nSi := pinvs 12 nS
  regs.size == 11 && strongOK n regs[1]! regs[2]! hS LocalData.strongWords &&
    ai.size == 2 && pisInv n a0 ai[0]! && pisInv n a1 ai[1]! &&
    FAData.c3Words.size == 6 && allBelowN 6 (fun j => plettersOK 17 FAData.c3Words[j]!) &&
    plettersOK 17 FAData.g3H && FAData.g3Root.all (fun l => l == 1 || l == 2) &&
    plettersOK 17 FAData.pKernel && FAData.pLift.size == 5 &&
    FAData.pLift.all (fun lw => lw.all fun l => decide (1 ≤ l) && decide (l ≤ 7)) &&
    G.size == 6 && allBelowN 6 (fun j => pisInv n G[j]! Gi[j]!) &&
    par.size == 729 && par[0]! == (0, 0) &&
    allBelowN 729 (fun i => i == 0 || (decide ((par[i]!).1 < i) && decide ((par[i]!).2 < 6))) &&
    FAData.pLeft.size == 6 &&
    allBelowN 6 (fun j => (FAData.pLeft[j]!).size == 729 && allBelowN 729 fun i =>
      decide ((FAData.pLeft[j]!)[i]! < 729) &&
        bimgs[(FAData.pLeft[j]!)[i]!]! == B.map fun b => G[j]![pev G par 729 i b]!) &&
    allBelowN 729 (fun i => allBelowN 729 fun k => decide (k ≤ i) || bimgs[i]! != bimgs[k]!) &&
    SylowData.order3.length == 512 &&
    allBelowN 729 (fun i => mark[i]! == (i != 0 && B.all fun b =>
      pev G par 729 i (pev G par 729 i (pev G par 729 i b)) == b)) &&
    SylowData.conj.size == 6 &&
    allBelowN 6 (fun j => (SylowData.conj[j]!).size == 729 && allBelowN 729 fun i =>
      decide ((SylowData.conj[j]!)[i]! < 729) &&
        bimgs[(SylowData.conj[j]!)[i]!]! == B.map fun b => G[j]![pev G par 729 i Gi[j]![b]!]!) &&
    FAData.wClass.size == 48 && lab.size == 729 &&
    allBelowN 48 (fun c => (FAData.wClass[c]!).all fun i =>
      decide (i < 729) && mark[i]! && lab[i]! == c &&
        allBelowN 6 fun j => lab[(SylowData.conj[j]!)[i]!]! == c) &&
    allBelowN 729 (fun i => !mark[i]! || (decide (lab[i]! < 48) &&
      (FAData.wClass[lab[i]!]!).contains i)) &&
    SylowData.tree.size == 729 &&
    allBelowN 729 (fun i => !mark[i]! || (treeReach SylowData.tree 729 i &&
      (if (SylowData.tree[i]!).2 == 0 then i == FAData.wRep[lab[i]!]! else
        decide ((SylowData.tree[i]!).1 < 729) && decide ((SylowData.tree[i]!).2 ≤ 6) &&
        mark[(SylowData.tree[i]!).1]! && lab[(SylowData.tree[i]!).1]! == lab[i]! &&
        (SylowData.conj[(SylowData.tree[i]!).2 - 1]!)[(SylowData.tree[i]!).1]! == i))) &&
    FAData.wRep.size == 48 && FAData.wRoot.size == 48 && FAData.wHWord.size == 48 &&
    FAData.wNat.size == 48 && FAData.wCycles.size == 48 && SylowData.rho.size == 48 &&
    allBelowN 48 (fun c =>
      let r := FAData.wRep[c]!
      let w := FAData.wRoot[c]!
      let hw := FAData.wHWord[c]!
      let harr := pword n hS hSi hw
      let k := FAData.wCycles[c]!
      let ρ := natArr SylowData.rho[c]!
      decide (r < 729) && lab[r]! == c && w.all (fun l => l == 1 || l == 2) &&
        plettersOK 17 hw && decide (1 ≤ k) && decide (k ≤ 4) &&
        B.all (fun b => seedWordInvIdx ai[0]! ai[1]! w (pev G par 729 r (seedWordIdx a0 a1 w b)) ==
          harr[b]!) &&
        peq 12 (pword 12 nS nSi hw) (natArr FAData.wNat[c]!) &&
        pisInv 12 ρ (pinvCand 12 ρ) &&
        peq 12 (pcomp 12 (pcomp 12 ρ (tripleArr k)) (pinvCand 12 ρ)) (natArr FAData.wNat[c]!))

end CFSG.Sporadic.HNSchreier.Native
