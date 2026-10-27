module

public import Certificates.Data.Kernel.SporSch.Co2M
public import Certificates.Data.Kernel.MonsterB.BfsReplay
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KS.Co2LE

open CFSG.KC.Enum CFSG.KS.Co2M CFSG.KC.Bfs

@[expose] noncomputable def M484 : ℕ := nat_lit 49947976805055875702105555676690660891977570282639538413746511354005947821116249921924897649015871538557230897942505966327167610868612564900642815

@[expose] noncomputable def fR (R : ℕ → ℕ) (k f : ℕ) : ℕ := pg (nat_lit 22) M22 (R k) f

@[expose] noncomputable def eM (R : ℕ → ℕ) (k : ℕ) : ℕ := Nat.land (R k) M484

@[expose] noncomputable def tR (R : ℕ → ℕ) (k j : ℕ) : ℕ := fR R k (Nat.add (nat_lit 22) j)

@[expose] noncomputable def mR (R : ℕ → ℕ) (ng k : ℕ) : ℕ := fR R k (Nat.add (nat_lit 22) ng)

@[expose] noncomputable def pR (R : ℕ → ℕ) (ng k : ℕ) : ℕ := fR R k (Nat.add (nat_lit 23) ng)

@[expose] noncomputable def lR (R : ℕ → ℕ) (ng k : ℕ) : ℕ := fR R k (Nat.add (nat_lit 24) ng)

@[expose] noncomputable def sR (R : ℕ → ℕ) (ng k : ℕ) : ℕ := fR R k (Nat.add (nat_lit 25) ng)

@[expose] noncomputable def codeK (PV X : ℕ) : ℕ :=
  Nat.lor (vmK (VG PV (nat_lit 0)) X) (Nat.lor (Nat.shiftLeft (vmK (VG PV (nat_lit 1)) X) (nat_lit 22))
    (Nat.shiftLeft (vmK (VG PV (nat_lit 3)) X) (nat_lit 44)))

@[expose] noncomputable def nextR (R : ℕ → ℕ) (ng N k : ℕ) : ℕ :=
  nIf(Nat.blt (Nat.succ k) N, mR R ng (Nat.succ k), N)

@[expose] noncomputable def optIs (o : Option ℕ) (m : ℕ) : Bool :=
  Option.rec (motive := fun _ => Bool) false (fun a => Nat.beq a m) o

@[expose] noncomputable def recK (R G : ℕ → ℕ) (PV ng N k : ℕ) : Bool :=
  bAnd(allN ng (fun j => bAnd(Nat.blt (tR R k j) N,
      Nat.beq (eM R (tR R k j)) (mmK (eM R k) (G j)))),
  bAnd(Nat.blt k (mR R ng k),
  bAnd(optIs (rRow (tR R) ng k (mR R ng k)) (nextR R ng N k),
  bAnd(bIf(Nat.beq k (nat_lit 0), true, bAnd(Nat.blt (pR R ng k) k,
      bAnd(Nat.blt (lR R ng k) ng, Nat.beq (tR R (pR R ng k) (lR R ng k)) k))),
  bAnd(Nat.blt (sR R ng k) N,
    bIf(Nat.blt (Nat.succ k) N, Nat.blt (codeK PV (eM R (sR R ng k)))
      (codeK PV (eM R (sR R ng (Nat.succ k)))), true))))))

@[expose] noncomputable def conjK (R : ℕ → ℕ) (C C' PI w N k : ℕ) : Bool :=
  bAnd(Nat.blt (pg w (CFSG.KS.mask w) PI k) N,
    Nat.beq (eM R (pg w (CFSG.KS.mask w) PI k)) (mmK C' (mmK (eM R k) C)))

@[expose] noncomputable def centK (R G : ℕ → ℕ) (ng k : ℕ) : Bool :=
  allN ng fun j => Nat.beq (mmK (G j) (eM R k)) (mmK (eM R k) (G j))

end CFSG.KS.Co2LE

end
