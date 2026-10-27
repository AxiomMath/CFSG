module

public import Certificates.Data.Kernel.M24G.Replay
public import Certificates.Data.CFSGNative.AS91.M24Geom

public section

namespace CFSG.KC.M24G

open CFSG.Quasithin.H13.AS91.M24G

@[expose] def copG (ts : Nat → List Nat) (p p' : Nat) : Bool := (ts p).any fun q => (ts p').contains q

@[expose] def piG (ts : Nat → List Nat) (tr : Nat → Nat × Nat × Nat) (oi : Nat → Nat → Bool)
    (oc : Nat → Nat → Nat) (co : Nat → Nat → List Nat) (pen : Nat → Nat → List Nat)
    (ix : Nat → Nat → Nat) (l m : Nat) : Bool :=
  match ((ts l).filter fun q => oi m q), ((ts m).filter fun q => oi l q) with
  | [π], [π'] =>
    let y := oc m π
    let x := oc l π'
    let co := co l m
    let inPi := fun k => (ts k).contains π
    let inPi' := fun k => (ts k).contains π'
    let pencil := pen π y
    let xy := ix x y
    co.all (fun k => inPi k || inPi' k) &&
      (co.filter inPi).length == 3 && (co.filter inPi).all (pencil.contains ·) &&
      pencil.length == 3 &&
      pencil.all (fun k => k != m && Native.meets (tr m) (tr k)) &&
      x &&& y == 0 && decide (xy < Native.nTrio) && pencil.contains xy &&
      xy != l && Native.meets (tr l) (tr xy) &&
      pencil.all fun k => k == xy || (!(Native.meets (tr l) (tr k)) && copG ts l k)
  | _, _ => false

@[expose] def stmt313G (tr : Nat → Nat × Nat × Nat) (oi : Nat → Nat → Bool) (LU : List Nat)
    (d22 : Nat → Bool) : Bool :=
  (List.range Native.nTrio).all (fun p => !(oi p 0) || LU.all fun m => Native.zc (tr m) (tr p) != 0) &&
    (List.range Native.nTrio).all fun m => Native.zc (tr 0) (tr m) != 0 || d22 m

inductive IxTree (α : Type) where
  | leaf : IxTree α
  | node : IxTree α → α → IxTree α → IxTree α

@[expose] def evensL {α : Type} : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: l => x :: evensL l

@[expose] def oddsL {α : Type} : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: l => y :: oddsL l

@[expose] def ofListT {α : Type} : Nat → List α → IxTree α
  | 0, _ => .leaf
  | _ + 1, [] => .leaf
  | n + 1, x :: l => .node (ofListT n (evensL l)) x (ofListT n (oddsL l))

@[expose] def treeOf {α : Type} (L : List α) : IxTree α := ofListT L.length L

@[expose] def getT {α : Type} [Inhabited α] : IxTree α → Nat → α
  | .leaf, _ => default
  | .node _ x _, 0 => x
  | .node l _ r, i + 1 => if i % 2 = 0 then getT l (i / 2) else getT r (i / 2)

@[expose] def trK (TL : List (Nat × Nat × Nat)) (p : Nat) : Nat × Nat × Nat := getT (treeOf TL) p

@[expose] def tsK (TS : List (List Nat)) (p : Nat) : List Nat := getT (treeOf TS) p

@[expose] def slK (SL : List (List Nat)) (q : Nat) : List Nat := getT (treeOf SL) q

@[expose] def octsInK (TL : List (Nat × Nat × Nat)) (SL : List (List Nat)) (p q : Nat) : List Nat :=
  let u := Native.octsS (slK SL q)
  (Native.octsT (trK TL p)).filter fun o => u.contains o

@[expose] def oiK (TL : List (Nat × Nat × Nat)) (SL : List (List Nat)) (p q : Nat) : Bool :=
  (octsInK TL SL p q).length == 1

@[expose] def ocK (TL : List (Nat × Nat × Nat)) (SL : List (List Nat)) (p q : Nat) : Nat :=
  (octsInK TL SL p q).headD 0

@[expose] def coK (TS : List (List Nat)) (l m : Nat) : List Nat :=
  ((List.range Native.nTrio).filter (copG (tsK TS) l)).filter (copG (tsK TS) m)

@[expose] def penK (TL : List (Nat × Nat × Nat)) (TS : List (List Nat)) (π y : Nat) : List Nat :=
  ((List.range Native.nTrio).filter fun k => (tsK TS k).contains π).filter
    fun k => (Native.octsT (trK TL k)).contains y

@[expose] def ixK (TL : List (Nat × Nat × Nat)) (x y : Nat) : Nat :=
  idxK (posTree Native.key3 TL) Native.nTrio (Native.key3 (Native.sort3 x y (Native.full ^^^ x ^^^ y)))

@[expose] def stmt310K (TL : List (Nat × Nat × Nat)) (TS SL : List (List Nat)) : Bool :=
  (List.range Native.nTrio).all fun m => Native.zc (trK TL 0) (trK TL m) != 1 ||
    piG (tsK TS) (trK TL) (oiK TL SL) (ocK TL SL) (coK TS) (penK TL TS) (ixK TL) 0 m

@[expose] def d2K (TL : List (Nat × Nat × Nat)) (TS : List (List Nat)) (l k : Nat) : Bool :=
  !(Native.meets (trK TL l) (trK TL k)) && copG (tsK TS) l k

@[expose] def stmt313K (TL : List (Nat × Nat × Nat)) (TS SL : List (List Nat)) : Bool :=
  stmt313G (trK TL) (oiK TL SL) ((List.range Native.nTrio).filter fun p => (tsK TS p).contains 0)
    fun m => ((List.range Native.nTrio).filter (d2K TL TS 0)).any (d2K TL TS m)

end CFSG.KC.M24G
