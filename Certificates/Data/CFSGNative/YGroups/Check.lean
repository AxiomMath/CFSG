module

public import Certificates.Data.CFSGNative.YGroups.Felsch

public section

namespace CFSG.YGroups.Native

@[expose] def reduceStep (L : Nat) (inv : Nat → Nat) (st : List Nat) (c : Nat) : List Nat :=
  cond (Nat.beq c L) st <|
    match st with
    | [] => [c]
    | d :: st' => cond (Nat.beq d (inv c)) st' (c :: d :: st')

@[expose] def freelyTrivial (L : Nat) (inv : Nat → Nat) (w : List Nat) : Bool :=
  (w.foldl (reduceStep L inv) []).isEmpty

@[expose] def wordAt : List (List Nat) → Nat → List Nat
  | [], _ => []
  | w :: _, 0 => w
  | _ :: ws, n + 1 => wordAt ws n

@[expose] def refOK (fx fc fy inv : Nat → Nat) (f r cur c : Nat) : Bool :=
  and (Nat.blt (Nat.div r 2) f) <|
    cond (Nat.beq (Nat.mod r 2) 0)
      (and (Nat.beq (fx (Nat.div r 2)) cur) (Nat.beq (fc (Nat.div r 2)) c))
      (and (Nat.beq (fy (Nat.div r 2)) cur) (Nat.beq (fc (Nat.div r 2)) (inv c)))

@[expose] def refNext (fx fy : Nat → Nat) (r : Nat) : Nat :=
  cond (Nat.beq (Nat.mod r 2) 0) (fy (Nat.div r 2)) (fx (Nat.div r 2))

@[expose] def walkOK (fx fc fy inv refs : Nat → Nat) (f t o s : Nat) : Nat → Nat → List Nat → Bool
  | _, cur, [] => Nat.beq cur s
  | q, cur, c :: w =>
    cond (Nat.beq q t)
      (and (and (Nat.beq (fx f) cur) (Nat.beq (fc f) c))
        (walkOK fx fc fy inv refs f t o s (Nat.succ q) (fy f) w))
      (and (refOK fx fc fy inv f (refs (Nat.add o q)) cur c)
        (walkOK fx fc fy inv refs f t o s (Nat.succ q) (refNext fx fy (refs (Nat.add o q))) w))

@[expose] def factOK (N L' : Nat) (fx fc fy kind wi fs ft fo refs pl inv : Nat → Nat)
    (rels subs : List (List Nat)) (f : Nat) : Bool :=
  and (Nat.blt (fx f) N) <| and (Nat.blt (fy f) N) <|
  match kind f with
  | 0 => and (Nat.beq (pl (fy f)) (Nat.add (Nat.mul (fx f) L') (fc f)))
      (and (Nat.blt (fc f) L') (Nat.blt (fx f) (fy f)))
  | 2 => and (Nat.blt (wi f) rels.length) <| and (Nat.blt (ft f) (wordAt rels (wi f)).length)
      (walkOK fx fc fy inv refs f (ft f) (fo f) (fs f) 0 (fs f) (wordAt rels (wi f)))
  | 3 => and (Nat.blt (wi f) subs.length) <| and (Nat.blt (ft f) (wordAt subs (wi f)).length)
      (walkOK fx fc fy inv refs f (ft f) (fo f) 0 0 0 (wordAt subs (wi f)))
  | _ => false

@[expose] def factsOK (N L' : Nat) (fx fc fy kind wi fs ft fo refs pl inv : Nat → Nat)
    (rels subs : List (List Nat)) : Nat → Nat → Bool
  | _, 0 => true
  | lo, n + 1 => and (factOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs lo)
      (factsOK N L' fx fc fy kind wi fs ft fo refs pl inv rels subs (Nat.succ lo) n)

@[expose] def liveCount (live : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => Nat.add (liveCount live n) (cond (live n) 1 0)

@[expose] def coverOK (N L F : Nat) (fx fc fy inv ffi : Nat → Nat) (live : Nat → Bool) :
    Nat → Nat → Bool
  | _, 0 => true
  | lo, n + 1 =>
    and (cond (live (Nat.div lo L))
        (and (refOK fx fc fy inv F (ffi lo) (Nat.div lo L) (Nat.mod lo L))
          (and (live (refNext fx fy (ffi lo))) (Nat.blt (refNext fx fy (ffi lo)) N)))
        true)
      (coverOK N L F fx fc fy inv ffi live (Nat.succ lo) n)

@[expose] def stripEps (L : Nat) (w : List Nat) : List Nat := w.filter fun c => !(Nat.beq c L)

@[expose] def isRot (w r : List Nat) : Bool :=
  (List.range r.length).any fun i => r.drop i ++ r.take i == w

@[expose] def invWord (inv : Nat → Nat) (w : List Nat) : List Nat := (w.map inv).reverse

@[expose] def relsOK (L : Nat) (inv : Nat → Nat) (base ws : List (List Nat)) : Bool :=
  ws.all fun w => and (w.all fun c => Nat.blt c (Nat.succ L))
    (or (freelyTrivial L inv w)
      (base.any fun r => or (isRot (stripEps L w) r) (isRot (stripEps L w) (invWord inv r))))

@[expose] def lettersOK (L : Nat) (ws : List (List Nat)) : Bool :=
  ws.all fun w => w.all fun c => Nat.blt c L

@[expose] def invId : Nat → Nat := fun c => c

@[expose] def Cert.fxF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).fx
@[expose] def Cert.fcF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).fc
@[expose] def Cert.fyF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).fy
@[expose] def Cert.kindF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).kind
@[expose] def Cert.wiF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).wi
@[expose] def Cert.fsF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).fs
@[expose] def Cert.ftF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).ft
@[expose] def Cert.foF (c : Cert) : Nat → Nat := fun i => (c.facts[i]!).fo
@[expose] def Cert.refsF (c : Cert) : Nat → Nat := fun i => c.refs[i]!
@[expose] def Cert.plF (c : Cert) : Nat → Nat := fun i => c.pl[i]!
@[expose] def Cert.ffiF (c : Cert) : Nat → Nat := fun i => c.ffi[i]!
@[expose] def Cert.liveF (c : Cert) : Nat → Bool := fun i => c.live[i]!

@[expose] def certOK (L : Nat) (base subs : List (List Nat)) (k : Nat) (c : Cert) : Bool :=
  and (Nat.beq c.L L) <|
  and (Nat.blt 0 c.N) <|
  and (c.liveF 0) <|
  and (c.subs.toList == subs) <|
  and (lettersOK (Nat.succ L) (c.rels.toList ++ subs)) <|
  and (relsOK L invId base c.rels.toList) <|
  and (factsOK c.N (Nat.succ L) c.fxF c.fcF c.fyF c.kindF c.wiF c.fsF c.ftF c.foF c.refsF c.plF
    invId c.rels.toList subs 0 c.facts.size) <|
  and (coverOK c.N L c.facts.size c.fxF c.fcF c.fyF invId c.ffiF c.liveF 0 (c.N * L)) <|
  Nat.beq (liveCount c.liveF c.N) k

@[expose] def enumOK (L : Nat) (base subs : List (List Nat)) (maxPts k : Nat) : Bool :=
  certOK L base subs k (certOf (enumerate L (Array.range L) base subs maxPts))

end CFSG.YGroups.Native
