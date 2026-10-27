module

public import Certificates.Data.Kernel.Cert690.Base
public import CFSG.GF2Type.Smith1979W3.Cert690.Census.Defs
public import Mathlib.Data.List.Dedup
public import CFSG.Fischer.Uniq.CompTau
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.GroupTheory.ClassTwoThree
public import CFSG.RankThree.OrthogonalInvolutions.SuzukiTypes
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Utils

public section

namespace CFSG.KC.C690

open CFSG.GF2Type.Smith1979W3.Cert690 CFSG.LargeExtraspecial.O62

@[expose] noncomputable def actF (m v : Nat) : Nat := mulF m (Nat.land v (nat_lit 63))

structure GK where
  n : Nat
  getO : Nat → Nat
  ix : Nat → Nat
  getInv : Nat → Nat

@[expose] noncomputable def gkOf (O : List Nat) (S : List (Nat × Nat)) (inv : List Nat)
    (n : Nat) : GK :=
  ⟨n, fun i => (posT O).find i 0, fun c => (idxT S).find c n, fun i => (posT inv).find i 0⟩

@[expose] def singL (minus : Bool) : List Nat :=
  (List.range 64).filter fun n => n != 0 && !(qB minus n)

@[expose] noncomputable def isA2K (G : GK) (minus : Bool) (i : Nat) : Bool :=
  decide (i < G.n) &&
  let c := G.getO i
  c != oneF && mulF c c == oneF &&
  let I := (List.range 64).map fun v => actF c v ^^^ v
  I.dedup.length == 4 && I.all (fun x => !(qB minus x))

@[expose] noncomputable def transWitK (G : GK) (s : List Nat) (b : Nat) : List Nat :=
  s.map fun e => (List.range G.n).find? (fun i => actF (G.getO i) e == b) |>.getD 0

@[expose] noncomputable def transK (G : GK) (s : List Nat) (b : Nat) (w : List Nat) : Bool :=
  s.length != 0 && w.length == s.length && s[0]! == b &&
  (List.range s.length).all fun k =>
    let i := w[k]!
    decide (i < G.n) && actF (G.getO i) s[k]! == b

@[expose] noncomputable def a2FixK (G : GK) (minus : Bool) (b : Nat) : List Nat :=
  (List.range G.n).filter fun i => actF (G.getO i) b == b && isA2K G minus i

@[expose] noncomputable def conjK (G : GK) (a x : Nat) : Nat :=
  G.ix (mulF (mulF (G.getO a) (G.getO x)) (G.getO (G.getInv a)))

@[expose] noncomputable def lOKK (G : GK) (minus : Bool) (b : Nat) (L : Array Nat) : Bool :=
  L.size != 0 && L.toList.contains 0 && L.toList.dedup.length == L.size &&
  L.toList.all (fun i =>
    decide (i < G.n) && actF (G.getO i) b == b &&
      (i == 0 || mulF (G.getO i) (G.getO i) == oneF)) &&
  L.toList.all (fun i => L.toList.all fun j =>
    let p := mulF (G.getO i) (G.getO j)
    let y := G.ix p
    decide (y < G.n) && G.getO y == p && L.toList.contains y) &&
  L.toList.any (isA2K G minus)

@[expose] noncomputable def l2OKK (G : GK) (b : Nat) (Llist : Array (Array Nat))
    (a2 : List Nat) (wit : Array (Nat × Nat)) : Bool :=
  wit.size == a2.length &&
  (List.range a2.length).all fun k =>
    let t := a2[k]!
    let j := (wit[k]!).1
    let c := (wit[k]!).2
    decide (j < Llist.size) && decide (c < G.n) && actF (G.getO c) b == b &&
    let L := Llist[j]!
    L.size == 2 && L.toList.contains 0 &&
    (let ci := G.getO (G.getInv c)
     let cj := fun x =>
       let p := mulF (mulF (G.getO c) (G.getO x)) ci
       let y := G.ix p
       (decide (y < G.n) && G.getO y == p, y)
     L.toList.all (fun x => (cj x).1 && ((cj x).2 == 0 || (cj x).2 == t)) &&
     L.toList.any (fun x => (cj x).1 && (cj x).2 == 0) &&
     L.toList.any (fun x => (cj x).1 && (cj x).2 == t))

@[expose] noncomputable def l3OKK (G : GK) (b : Nat) (Llist : Array (Array Nat))
    (tasks wit : Array (Nat × Nat)) : Bool :=
  wit.size == tasks.size &&
  (List.range tasks.size).all fun k =>
    let j := (tasks[k]!).1
    let u := (tasks[k]!).2
    let kk := (wit[k]!).1
    let c := (wit[k]!).2
    decide (j < Llist.size) && decide (u < G.n) && decide (kk < Llist.size) && decide (c < G.n) &&
    let L := Llist[j]!
    actF (G.getO u) b == b &&
      (G.getO u != oneF && mulF (G.getO u) (G.getO u) == oneF) && !(L.toList.contains u) &&
    L.toList.all (fun x => mulF (G.getO u) (G.getO x) == mulF (G.getO x) (G.getO u)) &&
    actF (G.getO c) b == b &&
    (let U := L.toList ++ L.toList.map (fun x => G.ix (mulF (G.getO x) (G.getO u)))
     U.length == 2 * L.size && U.all (fun x => decide (x < G.n)) &&
     U.dedup.length == U.length &&
     (let V := U.map (fun x => conjK G c x)
      V.dedup.length == (Llist[kk]!).size &&
      V.all (fun y => (Llist[kk]!).toList.contains y) &&
      (Llist[kk]!).toList.all (fun y => V.contains y)))

@[expose] noncomputable def l3ValidK (G : GK) (b : Nat) (Llist : Array (Array Nat))
    (j u : Nat) : Bool :=
  decide (j < Llist.size) && decide (u < G.n) &&
  actF (G.getO u) b == b && (G.getO u != oneF && mulF (G.getO u) (G.getO u) == oneF) &&
    !((Llist[j]!).toList.contains u) &&
  (Llist[j]!).toList.all fun x => mulF (G.getO u) (G.getO x) == mulF (G.getO x) (G.getO u)

@[expose] noncomputable def l3CompleteK (G : GK) (b : Nat) (Llist : Array (Array Nat))
    (tasks : Array (Nat × Nat)) : Bool :=
  (List.range Llist.size).all fun j =>
    (List.range G.n).all fun u =>
      if l3ValidK G b Llist j u then tasks.toList.contains (j, u) else true

@[expose] noncomputable def censusLsK (G : GK) (minus : Bool) (Ld : LData) : Bool :=
  let b := b0Of minus
  let a2 := a2FixK G minus b
  Ld.Llist.size == (if minus then 17 else 22) &&
  (candidatesOf minus Ld.Llist).size == (if minus then 11 else 20) &&
  Ld.Llist.toList.all (fun L => lOKK G minus b L) &&
  l2OKK G b Ld.Llist a2 Ld.l2wit &&
  l3CompleteK G b Ld.Llist Ld.l3tasks &&
  l3OKK G b Ld.Llist Ld.l3tasks Ld.l3wit

end CFSG.KC.C690

end
