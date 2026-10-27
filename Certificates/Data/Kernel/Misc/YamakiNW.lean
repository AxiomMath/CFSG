module

public import Certificates.Data.Kernel.Misc.YamakiNA

public section

namespace CFSG.KD.YamakiNA

open CFSG.KD.BfsK CFSG.KD.YamakiCE CFSG.ClassicalInvolution.Sp62Rec
open CFSG.KD.Sp62 (MULF ONE)

@[expose] noncomputable def vnum (w : Nat) : Nat :=
  w % 2 + w / 2 % 2 * 64 + w / 4 % 2 * 4096 + w / 8 % 2 * 262144 + w / 16 % 2 * 16777216 +
    w / 32 % 2 * 1073741824

@[expose] noncomputable def mapsTo (x w c : Nat) : Bool := Nat.beq (MULF x (vnum w)) (vnum c)

@[expose] noncomputable def wK (R : Nat → Nat) : Bool :=
  ((List.range 64).all fun t => wCodes.all fun w => mapsTo (recX R 12 t) w w) &&
    (List.range 64).all fun v =>
      !((List.range 6).all fun j => mapsTo (R (Nat.add j 3)) v v) || wCodes.contains v

@[expose] noncomputable def stabChunk (R : Nat → Nat) (o n : Nat) (RX : Nat → Nat) (oX nX : Nat)
    (P : Nat → Nat) (L q : Nat) : Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n)
    (CFSG.KD.YamakiRepF.strictY (recX R o t) fun x =>
      !(wCodes.all fun w => wCodes.any fun c => mapsTo x w c) ||
        (Nat.blt (P t) nX && Nat.beq (recX RX oX (P t)) x))
    true

@[expose] noncomputable def rhoChunk (R : Nat → Nat) (o n : Nat) (RA : Nat → Nat) (L q : Nat) :
    Bool :=
  CFSG.KC.Misc.Clos.allR (Nat.mul L q) L fun t => cond (Nat.blt t n)
    (CFSG.KD.YamakiRepF.strictY (recX R o t) fun x =>
      !([9, 20, 38].all fun w => mapsTo x w w) || memK RA 12 64 x)
    true

end CFSG.KD.YamakiNA

end
