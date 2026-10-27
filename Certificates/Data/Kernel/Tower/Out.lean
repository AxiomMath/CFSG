module

public import Certificates.Data.Kernel.Tower.L1
public import Certificates.Data.Kernel.Tower.Chi

public section

namespace Certificates.KernelTower

@[expose] def l8 (T i : Nat) : Nat := lane T 8 255 i

@[expose] def oSt (HD l : Nat) : Nat := l16 HD (Nat.add 8 l)

@[expose] def oLen (HD l : Nat) : Nat := Nat.sub (oSt HD (Nat.succ l)) (oSt HD l)

@[expose] noncomputable def oConj (mul2 : Nat → Nat → Nat) (G HD c i : Nat) : Nat :=
  mul2 (mul2 (l16 G i) c) (l16 HD i)

@[expose] noncomputable def oMask (IL a n : Nat) : Nat :=
  Nat.rec 0 (fun q acc => Nat.lor (Nat.shiftLeft 1 (l16 IL (Nat.add a q))) acc) n

@[expose] noncomputable def oMaskAll (HD IL nl : Nat) : Nat :=
  Nat.rec 0 (fun l acc => Nat.lor (oMask IL (oSt HD l) (oLen HD l)) acc) nl

@[expose] noncomputable def oEnt (mul2 : Nat → Nat → Nat) (G HD LB l c : Nat) : Bool :=
  Nat.blt c 16384 && Nat.beq (l8 LB c) l &&
    allB 4 fun i => Nat.beq (l8 LB (oConj mul2 G HD c i)) l

@[expose] noncomputable def oNinv (mul2 : Nat → Nat → Nat) (S r HL : Nat) : Nat :=
  Nat.add (cntB 128 fun q => !Nat.beq (l16 HL q) 0 && Nat.beq (mul2 (l16 HL q) (l16 HL q)) 0)
    (cntB 128 fun q => bitS S (mul2 (l16 HL q) r))

@[expose] noncomputable def oRep (mul2 : Nat → Nat → Nat) (bc : Nat → Nat) (S r HL : Nat) : Bool :=
  allB 128 (fun q => Nat.blt (l16 HL q) 16384 &&
    Nat.beq (mul2 (l16 HL q) r) (mul2 r (bc (l16 HL q))) && Nat.blt (bc (l16 HL q)) 16384) &&
    allB 127 (fun q => Nat.blt (l16 HL q) (l16 HL (Nat.succ q))) &&
    !Nat.beq (oNinv mul2 S r HL) 87

@[expose] noncomputable def oLab (mul2 : Nat → Nat → Nat) (G HD LB IL l : Nat) : Bool :=
  Nat.ble (oLen HD l) 128 &&
    (Nat.blt (oLen HD l) 128 || anyB 3 fun m => Nat.beq (l16 HD (Nat.add 5 m)) l) &&
    allB (oLen HD l) fun q => oEnt mul2 G HD LB l (l16 IL (Nat.add (oSt HD l) q))

@[expose] noncomputable def outB (mul2 : Nat → Nat → Nat) (bc : Nat → Nat) (G U S HD LB IL : Nat)
    (HL : Nat → Nat) : Bool :=
  allB 4 (fun i => Nat.blt (l16 HD i) 16384 && Nat.beq (mul2 (l16 U i) (l16 HD i)) 0) &&
    Nat.beq (oMaskAll HD IL (l16 HD 4)) S &&
    allB (l16 HD 4) (oLab mul2 G HD LB IL) &&
    allB 3 fun m => !Nat.blt (l16 HD (Nat.add 5 m)) (l16 HD 4) ||
      oRep mul2 bc S (l16 IL (oSt HD (l16 HD (Nat.add 5 m)))) (HL m)

end Certificates.KernelTower
