module

public import Certificates.Data.Kernel.Census.PackedConj

public section

namespace CFSG.KC.Census

open CFSG.KC.Enum

section Words

variable (w h : Nat) (L : Nat → Nat)

@[expose] def lsw (k : Nat) : Nat := bif Nat.blt k h then Nat.add h k else Nat.sub k h

@[expose] noncomputable def wPt : List Nat → Nat → Nat
  | [], p => p
  | k :: l, p => at' w (L k) (wPt l p)

@[expose] noncomputable def wInvPt : List Nat → Nat → Nat
  | [], p => p
  | k :: l, p => wInvPt l (at' w (L (lsw h k)) p)

@[expose] noncomputable def pcwPt : List (List Nat) → Nat → Nat → Nat
  | [], _, p => p
  | x :: l, m, p =>
    bif Nat.beq (Nat.mod m 2) 1 then wPt w L x (pcwPt l (Nat.div m 2) p) else pcwPt l (Nat.div m 2) p

@[expose] noncomputable def pcwInvPt : List (List Nat) → Nat → Nat → Nat
  | [], _, p => p
  | x :: l, m, p =>
    pcwInvPt l (Nat.div m 2) (bif Nat.beq (Nat.mod m 2) 1 then wInvPt w h L x p else p)

@[expose] def iterPt (f : Nat → Nat) : Nat → Nat → Nat
  | 0, p => p
  | k + 1, p => f (iterPt f k p)

@[expose] noncomputable def pcRelB (bs : List Nat) :
    List (List Nat) → List Nat → List (List Nat) → Bool
  | [], _, _ => true
  | x :: l, r :: rs, c :: cs =>
    Nat.beq c.length l.length &&
      bs.all (fun b => Nat.beq (wPt w L x (wPt w L x b)) (pcwPt w L l r b)) &&
      (l.zip c).all (fun yc => bs.all fun b =>
        Nat.beq (wPt w L yc.1 (wPt w L x b)) (wPt w L x (pcwPt w L l yc.2 b))) &&
      pcRelB bs l rs cs
  | _, _, _ => false

@[expose] noncomputable def invLB (n : Nat) : Bool :=
  (List.range h).all fun k => (List.range n).all fun p =>
    Nat.blt (at' w (L k) p) n && Nat.beq (at' w (L (Nat.add h k)) (at' w (L k) p)) p

@[expose] noncomputable def resB (wr m O ix : Nat) (x : List Nat) (xr : Nat) : Bool :=
  (List.range m).all fun q =>
    Nat.beq (at' w O (at' wr ix (wPt w L x (at' w O q)))) (wPt w L x (at' w O q)) &&
      Nat.beq (at' wr xr q) (at' wr ix (wPt w L x (at' w O q)))

@[expose] noncomputable def commPt (c₁ c₂ : List Nat) (p : Nat) : Nat :=
  wPt w L c₁ (wPt w L c₂ (wInvPt w h L c₁ (wInvPt w h L c₂ p)))

@[expose] noncomputable def gamPt : List (Nat × List Nat × List Nat) → Nat → Nat
  | [], p => p
  | f :: l, p => commPt w h L f.2.1 f.2.2 (gamPt l p)

@[expose] noncomputable def gamInvPt : List (Nat × List Nat × List Nat) → Nat → Nat
  | [], p => p
  | f :: l, p => gamInvPt l (commPt w h L f.2.2 f.2.1 p)

@[expose] noncomputable def wcPt (xw : List (List Nat)) (me : Nat)
    (gs : List (Nat × List Nat × List Nat)) (p : Nat) : Nat :=
  pcwPt w L xw me (gamPt w h L gs (pcwInvPt w h L xw me (gamInvPt w h L gs p)))

@[expose] noncomputable def witB (bs : List Nat) (xw : List (List Nat)) (me : Nat)
    (gs : List (Nat × List Nat × List Nat)) (k : Nat) : Bool :=
  let y := iterPt (wcPt w h L xw me gs) k
  gs.all (fun f =>
    bs.any (fun b => !(Nat.beq (pcwPt w L xw f.1 b) b)) &&
      bs.all (fun b => Nat.beq (wPt w L f.2.1 (pcwPt w L xw f.1 b)) (pcwPt w L xw f.1 (wPt w L f.2.1 b))) &&
      bs.all (fun b => Nat.beq (wPt w L f.2.2 (pcwPt w L xw f.1 b)) (pcwPt w L xw f.1 (wPt w L f.2.2 b)))) &&
    bs.any (fun b => !(Nat.beq (y (y b)) b)) && bs.all (fun b => Nat.beq (y (y (y (y b)))) b)

@[expose] noncomputable def conjB (bs : List Nat) (xw : List (List Nat)) (me : Nat) (y : List Nat)
    (a : Nat) : Bool :=
  bs.all fun b => Nat.beq (pcwPt w L xw me (wPt w L y b)) (wPt w L y (at' w a b))

end Words

end CFSG.KC.Census

end
