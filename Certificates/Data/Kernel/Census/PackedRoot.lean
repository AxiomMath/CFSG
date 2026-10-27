module

public import Certificates.Data.Kernel.Census.PackedConj

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

inductive RootWitP where
  | perf (l : Nat)
  | ord4 (l m : Nat)
  | ord4p (ls : List Nat) (m : Nat)
  | ord4c (e c₁ c₂ m : Nat)
deriving Inhabited

structure PerfCertP where
  gens : List (List Nat × Nat)
  comms : List (Nat × Nat)
  x : Nat
  k : Nat
  conjs : List Nat
  cP : ArrCertP
  cQ : ArrCertP
  cR : ArrCertP
deriving Inhabited

structure RootConjP where
  x : Nat
  xs : List Nat
  xi : List Nat
  rs : List Nat
  cjs : List (List Nat)
  bs : List (Nat × Nat)
  im : List Nat
  wt : List (List Nat)
  ukc : List (Array (Nat × Nat × Nat × Nat))
  kb : List Nat
  cs : Array Nat
  gams : Array (Nat × Nat)
  ga : Array Nat
  gi : Array Nat
  perfs : Array PerfCertP
  cands : Array RootWitP
deriving Inhabited

@[expose] def uget {α : Type} [Inhabited α] : List (Array α) → Nat → α
  | [], _ => default
  | b :: bs, k => bif Nat.blt k b.size then b[k]! else uget bs (k - b.size)

@[expose] def usize {α : Type} (bs : List (Array α)) : Nat := (bs.map Array.size).sum

@[expose] def RootConjP.e (r : RootConjP) (k : Nat) : Nat × Nat × Nat × Nat := uget r.ukc k

section Checks

variable (n w : Nat)

@[expose] noncomputable def puAtF (r : RootConjP) : Nat → Nat → Nat → Nat :=
  fun f => Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ p => p)
    (fun _ ih k p =>
      let e := r.e k
      bif Nat.beq e.1 0 then ppcAt w r.xs e.2.1 p else
        at' w r.xs[e.2.2.1]! (ih e.2.1 (at' w r.xi[e.2.2.1]! p))) f

@[expose] noncomputable def puAt (r : RootConjP) (k p : Nat) : Nat :=
  puAtF w r ((r.e k).2.2.2 + 1) k p

@[expose] noncomputable def pkeyU (r : RootConjP) (k : Nat) : Nat :=
  Nat.ofDigits n (r.kb.map (puAt w r k))

@[expose] noncomputable def pinvol (p : Nat) : Bool :=
  Nat.beq (pc n w p p) (pid n w) && !(Nat.beq p (pid n w))

@[expose] noncomputable def pfix (p : Nat) : Nat :=
  ((List.range n).filter fun i => Nat.beq (at' w p i) i).length

@[expose] noncomputable def pperfGens (ga : Array Nat) (P : PerfCertP) : Array Nat :=
  (P.gens.map fun gl => ppow n w (pprod n w (gl.1.map fun l => ga[l]!)) gl.2).toArray

@[expose] noncomputable def pperfOK (ps : List Nat) (ga : Array Nat) (P : PerfCertP) : Bool :=
  let gs := pperfGens n w ga P
  let m := P.cP.pts.size
  let qs := (P.comms.map fun ij => pcomm n w P.cP.pts[ij.1]! P.cP.pts[ij.2]!).toArray
  let xa := P.cP.pts[P.x]!
  let rs := (P.conjs.map fun p => pconj n w P.cP.pts[p]! (pc n w xa xa)).toArray
  P.gens.all (fun gl => gl.1.all fun l => Nat.blt l ga.size) && penumOK n w gs ps P.cP &&
    P.comms.all (fun ij => Nat.blt ij.1 m && Nat.blt ij.2 m) && penumOK n w qs ps P.cQ &&
    Nat.beq P.cQ.pts.size m && Nat.blt P.x m && Nat.beq (ppow n w xa (2 ^ P.k)) (pid n w) &&
    P.conjs.all (fun p => Nat.blt p m) && penumOK n w rs ps P.cR && Nat.beq P.cR.pts.size m

@[expose] noncomputable def pord4 (y : Nat) : Bool :=
  !(Nat.beq (pc n w y y) (pid n w)) && Nat.beq (ppow n w y 4) (pid n w)

@[expose] noncomputable def pcandOK (inX : Nat → Bool) (x : Nat) (ga gi : Array Nat)
    (pG : Array (Array Nat)) (b : Nat) : RootWitP → Bool
  | .perf l => (pG[l]!).toList.any fun g => !(pcommA n w b g)
  | .ord4 l m => pord4 n w (ppow n w (pc n w (pc n w b ga[l]!) (pc n w b gi[l]!)) m)
  | .ord4p ls m =>
    pord4 n w (ppow n w (pprod n w (ls.map fun l => pc n w (pc n w b ga[l]!) (pc n w b gi[l]!))) m)
  | .ord4c e c₁ c₂ m =>
    let e' := bif Nat.beq e 0 then b else pc n w x b
    pvalid n w c₁ && pvalid n w c₂ && inX c₁ && inX c₂ && pcommA n w c₁ e' && pcommA n w c₂ e' &&
      pord4 n w (ppow n w (pc n w (pc n w x (pcomm n w c₁ c₂)) (pc n w x (pcomm n w c₂ c₁))) m)

@[expose] noncomputable def pleafOK (inX : Nat → Bool) (bmode : Nat) (skip : List Nat) (x : Nat)
    (ga gi : Array Nat) (pG : Array (Array Nat)) (b : Nat) (c : RootWitP) : Bool :=
  !(pinvol n w b) || Nat.beq b x || (Nat.beq bmode 1 && !(inX b)) || (Nat.beq bmode 2 && inX b) ||
    skip.contains (pfix n w b) || skip.contains (pfix n w (pc n w x b)) ||
    pcandOK n w inX x ga gi pG b c

@[expose] noncomputable def pentryOK (inX : Nat → Bool) (bmode : Nat) (skip : List Nat)
    (pG : Array (Array Nat)) (r : RootConjP) (k : Nat) : Bool :=
  let e := r.e k
  bif Nat.beq e.1 0 then
    Nat.beq e.2.2.2 0 && pinvol n w (ppcA n w r.xs e.2.1) && Nat.blt e.2.2.1 r.cands.size &&
      pleafOK n w inX bmode skip r.x r.ga r.gi pG (ppcA n w r.xs e.2.1) r.cands[e.2.2.1]!
  else
    Nat.blt e.2.1 (usize r.ukc) && Nat.beq e.2.2.2 ((r.e e.2.1).2.2.2 + 1) &&
      Nat.blt e.2.2.1 r.xs.length

@[expose] noncomputable def pordOK (r : RootConjP) : Bool :=
  (List.range (usize r.ukc - 1)).all fun i => Nat.blt (pkeyU n w r i) (pkeyU n w r (i + 1))

@[expose] def RootWitP.inRange (r : RootConjP) : RootWitP → Bool
  | .perf l => Nat.blt l r.perfs.size
  | .ord4 l _ => Nat.blt l r.gams.size
  | .ord4p ls _ => ls.all fun l => Nat.blt l r.gams.size
  | .ord4c .. => true

@[expose] noncomputable def prootConjOK (ps : List Nat) (inX inW : Nat → Bool) (pw : Bool)
    (bmode : Nat) (skip : List Nat) (r : RootConjP) : Bool :=
  let pG := r.perfs.map (pperfGens n w r.ga)
  pvalid n w r.x && pinvol n w r.x && inW r.x &&
    Nat.beq r.xi.length r.xs.length &&
    (r.xs.zip r.xi).all (fun gi => Nat.beq (pc n w gi.2 gi.1) (pid n w)) &&
    ppcOK n w r.xs r.rs r.cjs r.bs &&
    r.xs.all (fun g => pcommA n w g r.x && inW g) &&
    r.cs.toList.all (fun c => pvalid n w c && inX c && pcommA n w c r.x) &&
    Nat.beq r.ga.size r.gams.size && Nat.beq r.gi.size r.gams.size &&
    (List.range r.gams.size).all (fun l =>
      Nat.blt r.gams[l]!.1 r.cs.size && Nat.blt r.gams[l]!.2 r.cs.size &&
      Nat.beq r.ga[l]! (pcomm n w r.cs[r.gams[l]!.1]! r.cs[r.gams[l]!.2]!) &&
      Nat.beq r.gi[l]! (pcomm n w r.cs[r.gams[l]!.2]! r.cs[r.gams[l]!.1]!)) &&
    (pw || Nat.beq r.perfs.size 0) && r.perfs.toList.all (pperfOK n w ps r.ga) &&
    r.cands.toList.all (RootWitP.inRange r) &&
    Nat.beq r.wt.flatten.length (2 ^ r.xs.length) &&
    pinvRest n w r.xs 0 r.im r.wt.flatten == some [] &&
    Nat.beq (usize r.ukc) r.im.length &&
    (List.range (usize r.ukc)).all (pentryOK n w inX bmode skip pG r) && pordOK n w r

@[expose] noncomputable def pskipFix (rs : List RootConjP) (i : Nat) : List Nat :=
  (rs.take i).map fun r => pfix n w r.x

@[expose] noncomputable def prootsConjOK (ps : List Nat) (inX inW : Nat → Bool) (pw : Bool)
    (bmode : Nat) (rs : List RootConjP) : Bool :=
  (List.range rs.length).all fun i => prootConjOK n w ps inX inW pw bmode (pskipFix n w rs i) rs[i]!

end Checks

end CFSG.KC.Census
