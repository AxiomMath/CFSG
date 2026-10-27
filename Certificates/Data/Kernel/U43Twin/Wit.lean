module

public import Certificates.Data.Kernel.U43Pk.Cover

public section

namespace CFSG.KD.U43Twin

open CFSG.KC.Enum CFSG.KD.U43Pk

@[expose] noncomputable def powK (P n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDK (fun _ acc => strictN acc fun a => mulK P a) n

@[expose] noncomputable def cbK (C X : Nat) : Nat := strictN (mulK C X) fun Y => mulK Y (conjTK C)

@[expose] noncomputable def neqK (A1 A2 B1 B2 W : Nat) : Bool :=
  bAnd(Nat.blt W 256, strictB (Nat.div W 16) fun p => strictB (Nat.mod W 16) fun q =>
    notK (Nat.beq (mT (enK A1 A2 p) (enK B1 B2 q)) (mT (enK A1 A2 q) (enK B1 B2 p))))

@[expose] noncomputable def invK (T F W : Nat → Nat) (Z i : Nat) : Bool :=
  strictB (T i) fun P => strictB (mulK P P) fun S =>
    bIf(bAnd(isZK S, notK (isZK P)),
      strictB (W i) fun w => strictB (F w) fun e =>
        bAnd(Nat.blt w 35, bAnd(rawValidK e, Nat.beq (nrmK (mulK e P)) (nrmK (mulK Z e)))),
      true)

@[expose] noncomputable def sqK (T SP R : Nat → Nat) (Z i : Nat) : Bool :=
  strictB (T i) fun P =>
    bIf(Nat.beq (nrmK (mulK P P)) (nrmK Z),
      strictB (SP i) fun s => bAnd(Nat.blt 0 s, bAnd(Nat.blt s 97, Nat.beq (R (Nat.sub s 1)) i)),
      true)

@[expose] noncomputable def sqpK (T R : Nat → Nat) (X : Nat → Nat → Nat) (C Z k : Nat) : Bool :=
  strictB (R k) fun i => bAnd(Nat.blt i 1024, strictB (T i) fun P =>
    bAnd(Nat.beq (X 0 k) (powK P 2), bAnd(Nat.beq (X 1 k) (mulK P (X 0 k)),
      bAnd(Nat.beq (X 2 k) (mulK Z P), Nat.beq (X 3 k) (cbK C P)))))

@[expose] noncomputable def vioK (Pi Pj P2 P3 Fa Eb W : Nat) : Bool :=
  strictB (nrmK Fa) fun f =>
  strictB (mulK Pj Pi) fun A => strictB (mulK Pj P2) fun B => strictB (mulK Pj P3) fun D =>
    bAnd(notK (Nat.beq f (nrmK IDK)), bAnd(notK (Nat.beq f (nrmK Pi)),
    bAnd(notK (Nat.beq f (nrmK P2)), bAnd(notK (Nat.beq f (nrmK P3)),
    bAnd(notK (Nat.beq f (nrmK Pj)), bAnd(notK (Nat.beq f (nrmK A)),
    bAnd(notK (Nat.beq f (nrmK B)), bAnd(notK (Nat.beq f (nrmK D)), neqK Eb Fa Fa Eb W))))))))

@[expose] noncomputable def q8pK (T R : Nat → Nat) (X : Nat → Nat → Nat) (EL : Nat → Nat → Nat)
    (w k l : Nat) : Bool :=
  strictB (T (R k)) fun Pi => strictB (T (R l)) fun Pj => strictB (fld(w, 0, 3)) fun t =>
    bIf(Nat.beq t 0, neqK Pj Pi (X 2 k) Pj (fld(w, 2, 255)),
    bIf(Nat.beq t 1, strictB (fld(w, 2, 1)) fun s =>
        bAnd(Nat.beq (nrmK Pi) (nrmK (EL s (fld(w, 3, 7)))),
          Nat.beq (nrmK Pj) (nrmK (EL s (fld(w, 6, 7))))),
      bAnd(Nat.beq t 2,
        vioK Pi Pj (X 0 k) (X 1 k) (nIf(Nat.beq (fld(w, 2, 1)) 1, X 3 l, X 3 k))
          (nIf(Nat.beq (fld(w, 3, 1)) 1, Pj, Pi)) (fld(w, 4, 255)))))

@[expose] noncomputable def permK (T W : Nat → Nat) (EL : Nat → Nat → Nat) (P1 Q1 i : Nat) : Bool :=
  strictB (T i) fun P => strictB (conjTK P) fun H => strictB (W i) fun w =>
    bAnd(rawValidK H, bAnd(isZK (mulK P H), strictB (fld(w, 0, 1)) fun s =>
      bAnd(Nat.beq (nrmK (mulK (mulK P P1) H)) (nrmK (EL s (fld(w, 1, 7)))),
        Nat.beq (nrmK (mulK (mulK P Q1) H)) (nrmK (EL s (fld(w, 4, 7)))))))

@[expose] noncomputable def halfK (P A B : Nat) (L : Nat → Nat) (w : Nat) : Bool :=
  strictB (fld(w, 0, 3)) fun t => strictB (fld(w, 2, 255)) fun v =>
    bIf(Nat.beq t 0, bAnd(Nat.blt v 24, Nat.beq (nrmK P) (nrmK (L v))),
      bIf(Nat.beq t 1, neqK P A A P v, neqK P B B P v))

@[expose] noncomputable def centK (T W : Nat → Nat) (P1 Q1 P2 Q2 : Nat) (L1 L2 : Nat → Nat)
    (i : Nat) : Bool :=
  strictB (T i) fun P => strictB (W i) fun w =>
    bAnd(halfK P P2 Q2 L2 (fld(w, 0, 1023)), halfK P P1 Q1 L1 (fld(w, 10, 1023)))

@[expose] noncomputable def evenK (w : Nat) : Bool :=
  strictB (powK w 2) fun w2 =>
    bIf(bAnd(isZK w2, notK (isZK w)), true, bAnd(isZK (powK w 4), notK (isZK w2)))

@[expose] noncomputable def oddK (T W G : Nat → Nat) (i : Nat) : Bool :=
  strictB (T i) fun P =>
    bIf(isZK P, true, strictB (powK P 8) fun P8 =>
      bIf(isZK (mulK P P8),
        strictB (W i) fun g => bAnd(Nat.blt g 16, strictB (G g) fun H =>
          evenK (mulK (mulK (mulK P H) P8) (powK H 3))),
        true))

end CFSG.KD.U43Twin

end
