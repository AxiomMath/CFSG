module

public import Certificates.Data.Kernel.Spor.Chain
public import Certificates.Data.CFSGNative.SporadicSchreier.Count

public section

namespace CFSG.KC.KGC31P

open CFSG.KC.Enum CFSG.KS

variable (n w : Nat)

@[expose] noncomputable def pc (x y : Nat) : Nat := pcomp n w (mask w) x y

@[expose] noncomputable def pinv (x : Nat) : Nat := pinvS n w (mask w) x

@[expose] noncomputable def ppw (x : Nat) : Nat → Nat
  | 0 => pidn n w
  | e + 1 => pc n w x (ppw x e)

@[expose] noncomputable def pcj (x xi t : Nat) : Nat := pc n w (pc n w x t) xi

@[expose] noncomputable def pword (G : Int → Nat) (wd : List Int) : Nat :=
  wd.foldr (fun l T => pc n w (G l) T) (pidn n w)

@[expose] noncomputable def pmask : List Nat → Nat → Nat
  | [], _ => pidn n w
  | b :: bs, m => pc n w (if m % 2 = 1 then b else pidn n w) (pmask bs (m / 2))

@[expose] noncomputable def pspan (bs : List Nat) : List Nat :=
  (List.range (2 ^ bs.length)).map (pmask n w bs)

@[expose] noncomputable def porbTabs (m x xi t : Nat) : List Nat :=
  (List.range m).map fun j => pcj n w (ppw n w x j) (ppw n w xi j) t

@[expose] noncomputable def porbIs (orb bs : List Nat) : Bool :=
  (orb.all fun o => (pspan n w bs).any (Nat.beq o)) &&
    bs.all fun b => (pspan n w orb).any (Nat.beq b)

@[expose] noncomputable def pbadAct (m x xi t : Nat) : Bool :=
  !(Nat.beq (pcj n w x xi t) t) &&
    (List.range m).all fun j =>
      Nat.beq (pc n w t (pcj n w (ppw n w x j) (ppw n w xi j) t))
        (pc n w (pcj n w (ppw n w x j) (ppw n w xi j) t) t)

@[expose] noncomputable def porbOne (m x : Nat) (cands : List (List Nat)) (t : Nat) : Bool :=
  !(pbadAct n w m x (pinv n w x) t) || cands.any (porbIs n w (porbTabs n w m x (pinv n w x) t))

@[expose] noncomputable def pactOne (m x t : Nat) : Bool := !(pbadAct n w m x (pinv n w x) t)

@[expose] noncomputable def pord (m x : Nat) : Bool :=
  Nat.beq (ppw n w x m) (pidn n w) &&
    (CFSG.Sporadic.Schreier.Native.divParts m).all fun e => !(Nat.beq (ppw n w x e) (pidn n w))

@[expose] noncomputable def pelab (gs : List Nat) : Bool :=
  (gs.all fun g => Nat.beq (pc n w g g) (pidn n w)) &&
    gs.all fun g => gs.all fun h => Nat.beq (pc n w g h) (pc n w h g)

@[expose] noncomputable def pinSpan (bs : List Nat) (t : Nat) : Bool := (pspan n w bs).any (Nat.beq t)

@[expose] noncomputable def pframeOne (m x : Nat) (ub : List Nat) (cands : List (List Nat))
    (v : Nat) : Bool :=
  pinSpan n w ub v || !(pelab n w (ub ++ porbTabs n w m x (pinv n w x) v)) ||
    cands.any (porbIs n w (ub ++ porbTabs n w m x (pinv n w x) v))

@[expose] noncomputable def pebasis (bs : List Nat) : Bool :=
  (bs.all fun b => Nat.beq (pc n w b b) (pidn n w)) &&
    (bs.all fun b => bs.all fun c => Nat.beq (pc n w b c) (pc n w c b)) &&
    (List.range (2 ^ bs.length)).all fun m => m == 0 || !(Nat.beq (pmask n w bs m) (pidn n w))

@[expose] noncomputable def pnormAll (bs : List Nat) (T Ti : Nat) : Bool :=
  bs.all fun b => (pspan n w bs).any (Nat.beq (pcj n w T Ti b))

@[expose] noncomputable def pmasksOK (bs : List Nat) (g : Nat) (masks : List Nat) : Bool :=
  bs.length == masks.length &&
    (bs.zip masks).all fun p => Nat.beq (pc n w g p.1) (pc n w (pmask n w bs p.2) g)

@[expose] noncomputable def pcommAll (gs : List Nat) (e : Nat) : Bool :=
  gs.all fun g => Nat.beq (pc n w e g) (pc n w g e)

@[expose] noncomputable def pblocksOK (bl : List (List Nat)) (g : Nat) : Bool :=
  bl.all fun T => bl.any fun T' => T.all fun p => T'.contains (pg w (mask w) g p)

@[expose] noncomputable def pfixesBlocks (bl : List (List Nat)) (g : Nat) : Bool :=
  bl.all fun T => T.all fun p => T.contains (pg w (mask w) g p)

end CFSG.KC.KGC31P

end
