module

public import Certificates.Data.Kernel.J4TreeTopSylow

public section

namespace CFSG.KC.J4TreeS

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native

@[expose] def decW (w : Nat) : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | f + 1, n, x =>
    if n = 0 then [] else if n = 1 then [x % 2 ^ w] else
      decW w f (n / 2) (x % 2 ^ (w * (n / 2))) ++ decW w f (n - n / 2) (x / 2 ^ (w * (n / 2)))

@[expose] def entOf (e : Nat) : Nat × Nat × Nat := (e / 65536, e / 256 % 256, e % 256)

structure TMerge where
  i : Nat
  j : Nat
  y : Nat × Nat
  tgt : Nat
  L : Nat
  h : Nat
  hI : Nat
  msk : List Nat
deriving Inhabited

@[expose] def parseM (l : List Nat) : TMerge :=
  match l with
  | i :: j :: a :: b :: t :: n :: h :: hI :: nm :: l => ⟨i, j, (a, b), t, n, h, hI, l.take nm⟩
  | _ => default

@[expose] noncomputable def topMergeOK (T : Tabs) (g : TGlob) (c : TMerge)
    (es : List (Nat × Nat × Nat)) : Bool :=
  let d := topNodes.getD c.i default
  let dc := d.children.getD c.j default
  let B := (treeBasis g.k).map (ccT T)
  let Y := ccT T c.y
  let H := wordT T 64 c.h
  let TB := (treeBasis c.tgt).map (ccT T)
  g.k == d.node && Nat.blt c.j d.children.length && c.y == dc.y && c.tgt == dc.target &&
    Nat.ble 1 c.tgt && Nat.ble c.tgt treeN && coordOK c.y && (treeBasis g.k).all coordOK &&
    (treeBasis c.tgt).all coordOK && sqOneK Y && B.all (fun b => commK Y b) &&
    invK H c.hI && c.msk.length == B.length + 1 &&
    ((B ++ [Y]).zip c.msk).all (fun p => Nat.beq (M (M c.hI p.1) H) (prodMask TB p.2)) &&
    es.length == c.L && c.L * treeOrd c.tgt == treeOrd g.k &&
    treeOK (fun j x => M (M (g.GI.getD j 0) x) (g.G.getD j 0)) g.G.length Y es

end CFSG.KC.J4TreeS

end
