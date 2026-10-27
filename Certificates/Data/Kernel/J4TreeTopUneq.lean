module

public import Certificates.Data.Kernel.J4TreeTopMerge

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native

@[expose] def pow2F : Nat → Nat → Bool
  | 0, _ => false
  | f + 1, x => x == 1 || (x % 2 == 0 && Nat.blt 0 x && pow2F f (x / 2))

structure TUneq where
  i : Nat
  j : Nat
  y : Nat × Nat
  tgt : Nat
  L : Nat
  h : Nat
  hI : Nat
  msk : List Nat
  sC : List (Nat × Nat)
  eC : List (Nat × Nat)
  zw : List (List Nat)
  q : Nat
  zs : List (Nat × Nat × Nat)
deriving Inhabited

@[expose] def parseZW : Nat → Nat → List Nat → List (List Nat) × List Nat
  | 0, _, l => ([], l)
  | _ + 1, 0, l => ([], l)
  | f + 1, n + 1, l =>
    let r := parseZW f n ((l.drop 1).drop (l.headD 0))
    (((l.drop 1).take (l.headD 0)) :: r.1, r.2)

@[expose] def parseU (l : List Nat) : TUneq :=
  match l with
  | i :: j :: a :: b :: t :: n :: h :: hI :: nm :: l =>
    let msk := l.take nm
    let l := l.drop nm
    let sC := pairs ((l.drop 1).take (2 * l.headD 0))
    let l := (l.drop 1).drop (2 * l.headD 0)
    let eC := pairs ((l.drop 1).take (2 * l.headD 0))
    let l := (l.drop 1).drop (2 * l.headD 0)
    let z := parseZW 64 (l.headD 0) (l.drop 1)
    let l := z.2
    ⟨i, j, (a, b), t, n, h, hI, msk, sC, eC, z.1, l.headD 0, triples ((l.drop 1).take (3 * l.headD 0))⟩
  | _ => default

@[expose] noncomputable def wordG (G GI : List Nat) (w : List Nat) : Nat :=
  w.foldl (fun a j => M a (if Nat.blt j G.length then G.getD j 0 else GI.getD (j - G.length) 0))
    oneK

@[expose] def invWord (n : Nat) (w : List Nat) : List Nat :=
  w.reverse.map fun j => if Nat.blt j n then j + n else j - n

@[expose] noncomputable def zOK (g : TGlob) (B : List Nat) (Y : Nat) (c : TUneq) : Bool :=
  let n := g.G.length
  let Z := c.zw.map (wordG g.G g.GI)
  let ZI := c.zw.map fun w => wordG g.G g.GI (invWord n w)
  c.zw.all (fun w => w.all fun j => Nat.blt j (2 * n)) && (Z.zip ZI).all (fun p => invK p.1 p.2) &&
    Z.all (fun z => commK z Y && B.all fun b => commK z b) &&
    oddOK Z ZI c.q (List.range Z.length) c.zs

@[expose] noncomputable def childBaseOK (T : Tabs) (g : TGlob) (c : TUneq)
    (es : List (Nat × Nat × Nat)) : Bool :=
  let d := topNodes.getD c.i default
  let dc := d.children.getD c.j default
  let B := (treeBasis g.k).map (ccT T)
  let Y := ccT T c.y
  g.k == d.node && Nat.blt c.j d.children.length && c.y == dc.y && c.tgt == dc.target &&
    coordOK c.y && (treeBasis g.k).all coordOK && sqOneK Y && B.all (fun b => commK Y b) &&
    es.length == c.L &&
    treeOK (fun j x => M (M (g.GI.getD j 0) x) (g.G.getD j 0)) g.G.length Y es &&
    zOK g B Y c

@[expose] noncomputable def topUneqOK (T : Tabs) (g : TGlob) (c : TUneq)
    (es : List (Nat × Nat × Nat)) : Bool :=
  let B := (treeBasis g.k).map (ccT T)
  let Y := ccT T c.y
  let H := wordT T 64 c.h
  let TB := (treeBasis c.tgt).map (ccT T)
  let TT := TB.map fun t => M (M H t) c.hI
  childBaseOK T g c es && Nat.ble 1 c.tgt && Nat.ble c.tgt treeN &&
    (treeBasis c.tgt).all coordOK && invK H c.hI && c.msk.length == B.length + 1 &&
    ((B ++ [Y]).zip c.msk).all (fun p => Nat.beq (M (M c.hI p.1) H) (prodMask TB p.2)) &&
    pow2F 64 (treeOrd c.tgt) && c.L * treeOrd c.tgt * c.q == treeOrd g.k &&
    c.zs.all (fun e => Nat.beq e.1 oneK || TT.any fun t => !commK e.1 t)

@[expose] noncomputable def topPruneOK (T : Tabs) (g : TGlob) (c : TUneq)
    (es : List (Nat × Nat × Nat)) : Bool :=
  let B := (treeBasis g.k).map (ccT T)
  let Y := ccT T c.y
  let S := c.sC.map (ccT T)
  let E := c.eC.map (ccT T)
  childBaseOK T g c es && c.tgt == 0 && c.sC.all coordOK && c.eC.all coordOK &&
    S.all (fun s => commK s Y && B.all fun b => commK s b) && leadsOK S &&
    c.L * 2 ^ c.sC.length * c.q == treeOrd g.k &&
    c.eC.length == 7 && leadsOK E &&
    E.all (fun e => inEK e && sqOneK e && commK e Y && B.all (fun b => commK e b) &&
      S.all fun s => commK e s)

end CFSG.KC.J4TreeS

end
