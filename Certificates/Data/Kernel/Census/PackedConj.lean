module

public import Certificates.Data.Kernel.Census.PackedExc

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

structure ConjDataP where
  xs : List Nat
  rs : List Nat
  cjs : List (List Nat)
  bs : List (Nat × Nat)
  us : Array Nat
  im : List Nat
  wt : List Nat
  cm : List Nat
  cs : Array Nat
  ci : Array Nat
  roots : List (Nat × Nat)
  nodes : Array NodeP
  ents : Array (List (Nat × Nat × Nat))
  wcs : Array (Array ArrCertP)
  excs : List ExcRefP

section Checks

variable (n w : Nat)

@[expose] noncomputable def ppcA : List Nat → Nat → Nat
  | [], _ => pid n w
  | x :: l, m => nIf(Nat.beq (Nat.mod m 2) 1, pc n w x (ppcA l (Nat.div m 2)), ppcA l (Nat.div m 2))

@[expose] noncomputable def ppcAt : List Nat → Nat → Nat → Nat
  | [], _, p => p
  | x :: l, m, p =>
    nIf(Nat.beq (Nat.mod m 2) 1, at' w x (ppcAt l (Nat.div m 2) p), ppcAt l (Nat.div m 2) p)

@[expose] noncomputable def ppcOK : List Nat → List Nat → List (List Nat) → List (Nat × Nat) → Bool
  | [], _, _, _ => true
  | x :: l, r :: rs, c :: cs, b :: bs =>
    pvalid n w x && Nat.beq (pc n w x x) (ppcA n w l r) && Nat.beq c.length l.length &&
      (l.zip c).all (fun yc => Nat.beq (pc n w yc.1 x) (pc n w x (ppcA n w l yc.2))) &&
      Nat.blt b.2 n && b.1.testBit b.2 && !(b.1.testBit (at' w x b.2)) &&
      l.all (fun y => (List.range n).all fun p => !(b.1.testBit p) || b.1.testBit (at' w y p)) &&
      ppcOK l rs cs bs
  | _, _, _, _ => false

@[expose] noncomputable def pinvRest (xs : List Nat) : Nat → List Nat → List Nat → Option (List Nat)
  | _, im, [] => some im
  | m, im, x :: wt =>
    cond (Nat.beq (im.headD (2 ^ xs.length)) m) (pinvRest xs (m + 1) im.tail wt)
      (cond (Nat.beq m 0 || (Nat.blt x n && !(Nat.beq (ppcAt w xs m (ppcAt w xs m x)) x)))
        (pinvRest xs (m + 1) im wt) none)

@[expose] noncomputable def pinvOK (xs : List Nat) (us : Array Nat) (im wt : List Nat) : Bool :=
  Nat.beq im.length us.size && (us.toList.zip im).all (fun ua => Nat.beq (ppcA n w xs ua.2) ua.1) &&
    Nat.beq wt.length (2 ^ xs.length) && pinvRest n w xs 0 im wt == some []

@[expose] noncomputable def ptabOK (xs cm : List Nat) (cs ci : Array Nat) : Bool :=
  Nat.beq cm.length cs.size && Nat.beq ci.size cs.size &&
    (cs.toList.zip cm).all (fun sm => Nat.beq (ppcA n w xs sm.2) sm.1) &&
    (ci.toList.zip cs.toList).all fun p => Nat.beq (pc n w p.1 p.2) (pid n w)

@[expose] noncomputable def pconjT (s t x : Nat) : Nat :=
  bif Nat.beq s (pid n w) && Nat.beq t (pid n w) then x else pc n w s (pc n w x t)

@[expose] noncomputable def prootOKC (bs : Array (Array Nat)) (cN : Array ArrCertP)
    (cs ci : Array Nat) (u : Nat) (r : Nat × Nat) : Bool :=
  Nat.blt r.1 bs.size && Nat.blt r.2 cs.size &&
    ((List.range bs[r.1]!.size).all fun l =>
      Nat.beq bs[r.1]![l]! (pconjT n w cs[r.2]! ci[r.2]! u) ||
        Nat.beq bs[r.1]![l]! (pid n w)) &&
    pmem cN[r.1]! (pconjT n w cs[r.2]! ci[r.2]! u)

@[expose] noncomputable def pentOK (bs : Array (Array Nat)) (cN : Array ArrCertP)
    (cs ci : Array Nat) (i u : Nat) (e : Nat × Nat × Nat) : Bool :=
  bIf(Nat.beq e.1 0,
    Nat.blt e.2.1 bs[i]!.size && Nat.blt e.2.2 n &&
      !(Nat.beq (at' w u (at' w bs[i]![e.2.1]! e.2.2)) (at' w bs[i]![e.2.1]! (at' w u e.2.2))),
    bIf(Nat.beq e.1 1, pmem cN[i]! u,
      Nat.blt e.2.1 bs.size && Nat.blt e.2.2 cs.size &&
        Nat.beq cN[e.2.1]!.pts.size (2 * cN[i]!.pts.size) &&
        ((List.range bs[i]!.size).all fun l =>
          pmem cN[e.2.1]! (pconjT n w cs[e.2.2]! ci[e.2.2]! bs[i]![l]!)) &&
        pmem cN[e.2.1]! (pconjT n w cs[e.2.2]! ci[e.2.2]! u)))

@[expose] noncomputable def pentsOK (bs : Array (Array Nat)) (cN : Array ArrCertP)
    (us cs ci : Array Nat) (es : List (Nat × Nat × Nat)) (i : Nat) : Bool :=
  Nat.beq es.length us.size && (us.toList.zip es).all fun ue => pentOK n w bs cN cs ci i ue.1 ue.2

@[expose] noncomputable def pnodeOKC (ps : List Nat) (inX outX inW : Nat → Bool)
    (allowPW allowInX allowU : Bool) (d : ConjDataP) (cN : Array ArrCertP) (e0 : Array Nat)
    (i : Nat) : Bool :=
  let wt := pwitOK n w ps inX outX allowPW allowInX allowU d.nodes[i]!.basis cN[i]! d.wcs[i]!
    d.nodes[i]!.wit
  penumOK n w d.nodes[i]!.basis ps cN[i]! &&
    ((wt && d.nodes[i]!.wit.isMono) ||
      ((wt || pexcOK n w ps inW e0 cN d.excs i) &&
        pentsOK n w (d.nodes.map NodeP.basis) cN d.us d.cs d.ci d.ents[i]! i))

end Checks

end CFSG.KC.Census
