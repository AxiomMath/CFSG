module

public import Certificates.Data.Kernel.Misc.OmegaSixO

public section

namespace CFSG.KD.OmegaSix

open CFSG.KD.BfsK CFSG.KD.YamakiRepF CFSG.KC.Loop
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def cjO (G S : Nat → Nat) (x s : Nat) : Nat := MULF (MULF (G s) x) (S s)

@[expose] noncomputable def hdrO (S : Nat → Nat) (a b r x : Nat) : Bool :=
  bAnd(Nat.beq (S 0) a, bAnd(Nat.beq (S 1) (MULF b (MULF b (MULF b b))),
    bAnd(Nat.beq (S 2) r, Nat.beq (S 4) x)))

@[expose] noncomputable def headC3 (R : Nat → Nat) (o n : Nat) : Bool :=
  bAnd(Nat.beq (recX R o 0) (R 4), bAnd(Nat.beq (recC R o 3 0) 1,
    Nat.beq (recC R o 3 (Nat.mul n 3)) n))

@[expose] noncomputable def subOrbK (R : Nat → Nat) (n : Nat) (S : Nat → Nat) (nS : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR 0 n fun t => memK S 5 nS (recX R 5 t)

@[expose] noncomputable def rank1K (X : Nat) : Bool :=
  anyK 6 fun c => strictY (subK X c) fun a => bIf(Nat.beq a 0, false,
    CFSG.KC.Misc.Clos.allR 0 6 fun d => strictY (subK X d) fun b =>
      bIf(Nat.beq b 0, true, Nat.beq b a))

@[expose] noncomputable def relK (X Y : Nat) : Bool :=
  strictY (MULF Y Y) fun s => bIf(Nat.beq (MULF s s) ONE,
    bIf(Nat.beq (MULF X X) ONE,
      strictY (MULF X Y) fun u => strictY (MULF u u) fun u2 =>
        bIf(Nat.beq (MULF (MULF u2 u2) u) ONE,
          strictY (MULF X s) fun v => strictY (MULF v v) fun v2 =>
            Nat.beq (MULF (MULF v2 v2) v) ONE, false), false), false)

@[expose] noncomputable def centL (L : Nat → Nat) (nL Y : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR 0 nL fun m => strictY (L m) fun T =>
    bIf(Nat.beq (MULF T Y) (MULF Y T), rank1K T, true)

@[expose] noncomputable def centAt (XA XB : Nat) (L : Nat → Nat) (nL Y : Nat) : Bool :=
  bIf(relK XA Y, false, bIf(relK XB Y, centL L nL Y, true))

@[expose] noncomputable def centChunk (R : Nat → Nat) (o n XA XB : Nat) (L : Nat → Nat)
    (nL len q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul len q) len fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (centAt XA XB L nL), true)

@[expose] noncomputable def cLAt (XB : Nat) (L : Nat → Nat) (nL T : Nat) : Bool :=
  bIf(Nat.beq T ONE, true,
    bIf(Nat.beq (MULF T XB) (MULF XB T), bsK L (fun m => m) T 16 0 nL, true))

@[expose] noncomputable def cLChunk (R : Nat → Nat) (o n XB : Nat) (L : Nat → Nat)
    (nL len q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul len q) len fun t =>
    bIf(Nat.blt t n, strictY (recX R o t) (cLAt XB L nL), true)

end CFSG.KD.OmegaSix

end
