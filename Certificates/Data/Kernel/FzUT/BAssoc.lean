module

public import Certificates.Data.Kernel.FzUT.BMod
public import Certificates.Data.Kernel.FzUT.Codes

public section

namespace CFSG.KC.FzBMod

@[expose] noncomputable def rhoC (x : Nat) : Nat :=
  Nat.add (Nat.shiftLeft (Nat.land x 3) 4) (Nat.add (Nat.land x 12) (Nat.shiftRight x 4))

@[expose] noncomputable def rhoB : Bool :=
  allN 64 (fun x => bAnd(Nat.beq (rhoC (rhoC x)) x, Nat.blt (rhoC x) 64))

@[expose] noncomputable def rhoMulB : Bool :=
  allN 64 (fun x => allN 64 (fun y =>
    Nat.beq (rhoC (uMulP x y)) (CFSG.KC.FzUT.pmulP (rhoC x) (rhoC y))))

@[expose] noncomputable def tabHomB (T : Nat) : Bool :=
  allN 64 (fun a => allN 64 (fun b =>
    Nat.beq (lk6 T (uMulP a b)) (uMulP (lk6 T a) (lk6 T b))))

@[expose] noncomputable def actCompB (c : Bool) : Bool :=
  allN 16 (fun w => allN 16 (fun v => allN 64 (fun u =>
    Nat.beq (actL c (amulL w v) u) (actL c w (actL c v u)))))

@[expose] noncomputable def amAssocB : Bool :=
  allN 16 (fun w => allN 16 (fun v => allN 16 (fun t =>
    Nat.beq (amulL (amulL w v) t) (amulL w (amulL v t)))))

@[expose] noncomputable def idB (c : Bool) : Bool :=
  allN 64 (fun u => bAnd(Nat.beq (actL c 0 u) u, bAnd(Nat.beq (uMulP 0 u) u,
    Nat.beq (uMulP u 0) u))) &&
  allN 16 (fun w => bAnd(Nat.beq (actL c w 0) 0, bAnd(Nat.beq (amulL 0 w) w,
    Nat.beq (amulL w 0) w)))

end CFSG.KC.FzBMod
