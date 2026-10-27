module

public import Certificates.Data.Kernel.J4TreeTopWalk
public import Certificates.Data.Kernel.J4TreeTopCover

public section

namespace CFSG.KC.J4TreeT

open CFSG.KC.J4Tree CFSG.KC.J4TreeN CFSG.KC.F2W CFSG.J4Tree.Native

structure CKGlob where
  wn : List Nat
  cc : List (Nat × Nat)
  G : List Nat
  GI : List Nat
  ms : List (List Nat)
  ys : List (Nat × Nat)
deriving Inhabited

@[expose] def parseCK (r : Nat) (l : List Nat) : CKGlob :=
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
    let ms := groups (2 * r) n (l.take (2 * r * n))
    let l := l.drop (2 * r * n)
    ⟨wn, cc, G, GI, ms, pairs ((l.drop 1).take (2 * l.headD 0))⟩
  | _ => default

@[expose] noncomputable def normMsK (B : List Nat) (g gi : Nat) (ms : List Nat) : Bool :=
  ms.length == 2 * B.length && ms.all (fun m => Nat.blt m (2 ^ B.length)) &&
    (B.zipIdx).all fun p =>
      Nat.beq (M (M g p.1) gi) (prodMask B (ms.getD p.2 0)) &&
        Nat.beq (M (M gi p.1) g) (prodMask B (ms.getD (B.length + p.2) 0))

@[expose] noncomputable def ckGlobOK (T : Tabs) (B : List Nat) (H : WHd) (d : TopNode)
    (g : CKGlob) : Bool :=
  g.G.length == g.wn.length + g.cc.length && g.GI.length == g.G.length &&
    g.ms.length == g.G.length && g.cc.all coordOK && g.ys.all coordOK &&
    (g.G.zip (g.wn.map (wordT T 64) ++ g.cc.map (ccT T))).all (fun p => Nat.beq p.1 p.2) &&
    (g.G.zip g.GI).all (fun p => invK p.1 p.2) &&
    ((g.G.zip g.GI).zip g.ms).all (fun p => normMsK B p.1.1 p.1.2 p.2) &&
    g.ys == d.children.map TopChild.y && H.gs == d.two

@[expose] noncomputable def ckWalk (sx : Nat) (G GI Y AL : List Nat) (X₀ : Nat) (S : List Nat)
    (L : Nat) : Nat → Nat → List Nat → Bool
  | _, acc, [] => acc == L
  | f + 1, acc, I :: j :: l =>
    let X := prodFrom X₀ S I
    if j = 0 then
      let zs := l.take AL.length
      zs.length == AL.length && (AL.zip zs).all (fun p => non2AK sx (M X p.1) p.2) &&
        ckWalk sx G GI Y AL X₀ S L f (acc ||| 2 ^ I) (l.drop AL.length)
    else
      match l with
      | m :: d :: l =>
        let ch := l.take d
        let W := conjCh G GI X ch
        Nat.blt (j - 1) Y.length && Nat.blt m AL.length && ch.length == d &&
          ch.all (fun i => Nat.blt i G.length) &&
          Nat.beq W (M (Y.getD (j - 1) 0) (AL.getD m 0)) &&
          ckWalk sx G GI Y AL X₀ S L f (acc ||| 2 ^ I) (l.drop d)
      | _ => false
  | _, _, _ => false

@[expose] noncomputable def coverKOK (T : Tabs) (B : List Nat) (H : WHd) (g : CKGlob) (e : Nat)
    (D R : List Nat) : Bool :=
  let K := T.kel e
  match D with
  | 2 :: Ki :: ce :: m :: l =>
    let cs := (l.take m).map fun i => H.vs.getD i 0
    ckWalk T.sx g.G g.GI (g.ys.map (ccT T)) ((List.range (2 ^ B.length)).map (prodMask B))
      (M (T.eta ce) K) (cs.map fun c => M (M Ki (T.eta c)) K) ((l.drop m).headD 0) R.length 0 R
  | _ => R.isEmpty

end CFSG.KC.J4TreeT

end
