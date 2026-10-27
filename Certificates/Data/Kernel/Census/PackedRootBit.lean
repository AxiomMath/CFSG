module

public import Certificates.Data.Kernel.Census.PackedRoot

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

section Checks

variable (n w : Nat)

@[expose] noncomputable def pleafOKB (inX : Nat → Bool) (bmode : Nat) (skip : List Nat) (x : Nat)
    (ga gi : Array Nat) (pG : Array (Array Nat)) (o b : Nat) (c : RootWitP) : Bool :=
  (Nat.beq bmode 1 && Nat.beq o 1) || (Nat.beq bmode 2 && Nat.beq o 0) || !(pinvol n w b) ||
    Nat.beq b x || skip.contains (pfix n w b) || skip.contains (pfix n w (pc n w x b)) ||
    pcandOK n w inX x ga gi pG b c

@[expose] noncomputable def pentryOKB (inX : Nat → Bool) (bmode : Nat) (skip : List Nat)
    (pG : Array (Array Nat)) (k : Nat) (r : RootConjP) (j : Nat) : Bool :=
  let e := r.e j
  bif Nat.beq e.1 0 then
    Nat.beq e.2.2.2 0 && pinvol n w (ppcA n w r.xs e.2.1) && Nat.blt e.2.2.1 r.cands.size &&
      pleafOKB n w inX bmode skip r.x r.ga r.gi pG (Nat.land (Nat.shiftRight e.2.1 k) 1)
        (ppcA n w r.xs e.2.1) r.cands[e.2.2.1]!
  else
    Nat.blt e.2.1 (usize r.ukc) && Nat.beq e.2.2.2 ((r.e e.2.1).2.2.2 + 1) &&
      Nat.blt e.2.2.1 r.xs.length

@[expose] noncomputable def prootConjOKB (ps : List Nat) (inX inW : Nat → Bool) (pw : Bool)
    (bmode : Nat) (skip : List Nat) (k : Nat) (r : RootConjP) : Bool :=
  let pG := r.perfs.map (pperfGens n w r.ga)
  pvalid n w r.x && pinvol n w r.x && inW r.x &&
    Nat.beq r.xi.length r.xs.length &&
    (r.xs.zip r.xi).all (fun gi => Nat.beq (pc n w gi.2 gi.1) (pid n w)) &&
    ppcOK n w r.xs r.rs r.cjs r.bs &&
    r.xs.all (fun g => pcommA n w g r.x && inW g) &&
    Nat.blt k r.xs.length && ((List.range r.xs.length).all fun i => Nat.beq i k || inX r.xs[i]!) &&
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
    (List.range (usize r.ukc)).all (pentryOKB n w inX bmode skip pG k r) && pordOK n w r

@[expose] noncomputable def prootsConjOKB (ps : List Nat) (inX inW : Nat → Bool) (pw : Bool)
    (bmode : Nat) (ks : List Nat) (rs : List RootConjP) : Bool :=
  Nat.beq ks.length rs.length &&
    (List.range rs.length).all fun i =>
      prootConjOKB n w ps inX inW pw bmode (pskipFix n w rs i) ks[i]! rs[i]!

end Checks

end CFSG.KC.Census
