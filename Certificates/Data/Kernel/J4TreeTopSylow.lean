module

public import Certificates.Data.Kernel.J4TreeNode
public import Certificates.Data.CFSGNative.J4Tree.TopData

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native

@[expose] def mergeF : Nat → List Nat → List Nat → List Nat
  | 0, a, b => a ++ b
  | _ + 1, [], b => b
  | _ + 1, a :: as, [] => a :: as
  | f + 1, a :: as, b :: bs =>
    if Nat.blt b a then b :: mergeF f (a :: as) bs else a :: mergeF f as (b :: bs)

@[expose] def halves : List Nat → List Nat × List Nat
  | a :: b :: l => let p := halves l; (a :: p.1, b :: p.2)
  | l => (l, [])

@[expose] def msort : Nat → List Nat → List Nat
  | 0, l => l
  | f + 1, l =>
    match l with
    | [] => []
    | [a] => [a]
    | a :: b :: l' =>
      let p := halves (a :: b :: l')
      mergeF (l'.length + 2) (msort f p.1) (msort f p.2)

@[expose] def subS : Nat → List Nat → List Nat → Bool
  | _, [], _ => true
  | 0, _ :: _, _ => false
  | _ + 1, _ :: _, [] => false
  | f + 1, p :: ps, k :: ks =>
    if Nat.beq p k then subS f ps (k :: ks) else Nat.blt k p && subS f (p :: ps) ks

@[expose] def triples : List Nat → List (Nat × Nat × Nat)
  | a :: b :: c :: l => (a, b, c) :: triples l
  | _ => []

@[expose] def keyOf (x d : Nat) : Nat := x * 64 + d

@[expose] noncomputable def treeOK (par : Nat → Nat → Nat) (n Y : Nat)
    (es : List (Nat × Nat × Nat)) : Bool :=
  let ks := es.map fun e => keyOf e.1 e.2.1
  let ps := msort 64 ((es.filter fun e => !(Nat.beq e.2.1 0)).map
    fun e => keyOf (par e.2.2 e.1) (e.2.1 - 1))
  incrFrom 0 (es.map Prod.fst) &&
    es.all (fun e => Nat.blt e.1 (2 ^ 144) && Nat.blt e.2.1 64 &&
      (if e.2.1 = 0 then Nat.beq e.1 Y else Nat.blt e.2.2 n)) &&
    subS (ps.length + ks.length) ps ks

@[expose] noncomputable def closedOK (f : Nat → Nat → Nat) (n : Nat) (xs : List Nat) : Bool :=
  (List.range n).all fun j => msort 64 (xs.map (f j)) == xs

@[expose] def coprimeAll : List Nat → Bool
  | [] => true
  | a :: l => l.all (fun b => Nat.gcd a b == 1) && coprimeAll l

structure TGlob where
  k : Nat
  wn : List Nat
  cc : List (Nat × Nat)
  G : List Nat
  GI : List Nat
  odd : List (Nat × List Nat × List (Nat × Nat × Nat))
  kids : List (Nat × Nat)
deriving Inhabited

@[expose] def parseOdd : Nat → List Nat → List (Nat × List Nat × List (Nat × Nat × Nat)) × List Nat
  | 0, l => ([], l)
  | f + 1, o :: ng :: l =>
    let r := parseOdd f ((l.drop ng).drop (3 * o))
    ((o, l.take ng, triples ((l.drop ng).take (3 * o))) :: r.1, r.2)
  | _ + 1, l => ([], l)

@[expose] def parseG (l : List Nat) : TGlob :=
  match l with
  | k :: nw :: nc :: l =>
    let n := nw + nc
    let wn := l.take nw
    let l := l.drop nw
    let cc := pairs (l.take (2 * nc))
    let l := l.drop (2 * nc)
    let G := l.take n
    let l := l.drop n
    let GI := l.take n
    let l := l.drop n
    let o := parseOdd (l.headD 0) (l.drop 1)
    let l := o.2
    ⟨k, wn, cc, G, GI, o.1, pairs ((l.drop 1).take (2 * l.headD 0))⟩
  | _ => default

@[expose] noncomputable def oddOK (G GI : List Nat) (o : Nat) (gi : List Nat)
    (es : List (Nat × Nat × Nat)) : Bool :=
  let Go := gi.map (G.getD · 0)
  let GIo := gi.map (GI.getD · 0)
  gi.all (fun j => Nat.blt j G.length) && es.length == o && o % 2 == 1 &&
    treeOK (fun j x => M x (GIo.getD j 0)) gi.length oneK es &&
    closedOK (fun j x => M x (Go.getD j 0)) gi.length (es.map Prod.fst)

@[expose] noncomputable def topGlobOK (T : Tabs) (i : Nat) (g : TGlob) : Bool :=
  let d := topNodes.getD i default
  let B := (treeBasis g.k).map (ccT T)
  let S := g.cc.map (ccT T)
  g.k == d.node && g.kids == d.kids &&
    g.kids.all (fun kd => Nat.blt kd.2 d.children.length &&
      (d.children.getD kd.2 default).target == kd.1 && !(Nat.beq kd.1 0)) &&
    treeTopIds.contains g.k && (treeBasis g.k).all coordOK && g.cc.all coordOK &&
    g.G.length == g.wn.length + g.cc.length && g.GI.length == g.G.length &&
    (g.G.zip (g.wn.map (wordT T 64) ++ S)).all (fun p => Nat.beq p.1 p.2) &&
    (g.G.zip g.GI).all (fun p => invK p.1 p.2) &&
    B.all (fun b => sqOneK b && B.all fun b' => commK b b') &&
    g.G.all (fun a => B.all fun b => commK a b) &&
    leadsOK S &&
    g.odd.all (fun o => oddOK g.G g.GI o.1 o.2.1 o.2.2) &&
    coprimeAll (2 ^ g.cc.length :: g.odd.map Prod.fst) &&
    treeOrd g.k == 2 ^ g.cc.length * (g.odd.map Prod.fst).foldr (· * ·) 1

end CFSG.KC.J4TreeS

end
