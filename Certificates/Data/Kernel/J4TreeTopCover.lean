module

public import Certificates.Data.Kernel.J4TreeNode
public import Certificates.Data.CFSGNative.J4Tree.TopData

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native

structure C1Glob where
  wn : List Nat
  cc : List (Nat × Nat)
  G : List Nat
  GI : List Nat
  ys : List (Nat × Nat)
deriving Inhabited

@[expose] def parseC1 (l : List Nat) : C1Glob :=
  match l with
  | nw :: nc :: l =>
    let n := nw + nc
    let wn := l.take nw
    let l := l.drop nw
    let cc := pairs (l.take (2 * nc))
    let l := l.drop (2 * nc)
    let G := l.take n
    let l := l.drop n
    let GI := l.take n
    let l := l.drop n
    ⟨wn, cc, G, GI, pairs ((l.drop 1).take (2 * l.headD 0))⟩
  | _ => default

@[expose] noncomputable def c1GlobOK (T : Tabs) (z : Nat) (g : C1Glob) : Bool :=
  let Z := ccT T (z, 0)
  g.G.length == g.wn.length + g.cc.length && g.GI.length == g.G.length &&
    g.cc.all coordOK && g.ys.all coordOK &&
    (g.G.zip (g.wn.map (wordT T 64) ++ g.cc.map (ccT T))).all (fun p => Nat.beq p.1 p.2) &&
    (g.G.zip g.GI).all (fun p => invK p.1 p.2) && g.G.all (fun a => commK a Z) &&
    g.ys == topNode1.children.map TopChild.y

@[expose] def xorSel : List Nat → Nat → Nat
  | [], _ => 0
  | c :: cs, I => (if I % 2 = 1 then c else 0) ^^^ xorSel cs (I / 2)

@[expose] noncomputable def conjCh (G GI : List Nat) : Nat → List Nat → Nat
  | X, [] => X
  | X, i :: ch => conjCh G GI (M (M (G.getD i 0) X) (GI.getD i 0)) ch

@[expose] noncomputable def c1Walk (T : Tabs) (G GI Y : List Nat) (Z e : Nat) (cs : List Nat)
    (L : Nat) : Nat → Nat → List Nat → Bool
  | _, acc, [] => acc == L
  | f + 1, acc, I :: j :: l =>
    let X := ccT T (xorSel cs I, e)
    if j = 0 then
      match l with
      | v₁ :: v₂ :: l => non2AK T.sx X v₁ && non2AK T.sx (M X Z) v₂ &&
          c1Walk T G GI Y Z e cs L f (acc ||| 2 ^ I) l
      | _ => false
    else
      match l with
      | d :: l =>
        let ch := l.take d
        let W := conjCh G GI X ch
        let Yj := Y.getD (j - 1) 0
        Nat.blt (j - 1) Y.length && ch.length == d && ch.all (fun i => Nat.blt i G.length) &&
          (Nat.beq W Yj || Nat.beq W (M Yj Z)) &&
          c1Walk T G GI Y Z e cs L f (acc ||| 2 ^ I) (l.drop d)
      | [] => false
  | _, _, _ => false

@[expose] noncomputable def cover1OK (T : Tabs) (z e : Nat) (g : C1Glob) (D R : List Nat) : Bool :=
  match D with
  | _ :: m :: l =>
    c1Walk T g.G g.GI (g.ys.map (ccT T)) (ccT T (z, 0)) e (l.take m) ((l.drop m).headD 0) R.length 0 R
  | _ => false

end CFSG.KC.J4TreeT

end
