module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.XorSpan

open CFSG.KC.Enum

@[expose] noncomputable def row (w m K k : Nat) : Nat := fld(K, Nat.mul w k, m)

@[expose] noncomputable def piv (dw K k : Nat) : Nat :=
  fld(K, Nat.add dw (Nat.shiftLeft k (nat_lit 3)), nat_lit 255)

@[expose] noncomputable def xorIf (w m dw K k v : Nat) : Nat :=
  nIf(Nat.beq fld(v, piv dw K k, nat_lit 1) (nat_lit 1), Nat.xor v (row w m K k), v)

@[expose] noncomputable def red (w m dw K n v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun v => v)
    (fun k ih v => strictN (xorIf w m dw K k v) ih) n v

@[expose] noncomputable def inSpan (d w m dw K v : Nat) : Bool :=
  Nat.beq (red w m dw K d v) (nat_lit 0)

@[expose] noncomputable def rrefK (d w m dw K : Nat) : Bool :=
  bAnd(Nat.beq (Nat.shiftRight K (Nat.add dw (Nat.shiftLeft d (nat_lit 3)))) (nat_lit 0),
  allN d (fun k => strictB (row w m K k) fun r => strictB (piv dw K k) fun p =>
    bAnd(Nat.beq fld(r, p, nat_lit 1) (nat_lit 1),
    bAnd(Nat.beq (Nat.shiftRight r (Nat.succ p)) (nat_lit 0),
    bAnd(allN d (fun l => bIf(Nat.beq l k, true,
      Nat.beq fld(row w m K l, p, nat_lit 1) (nat_lit 0))),
      bIf(Nat.blt (Nat.succ k) d, Nat.blt p (piv dw K (Nat.succ k)), true))))))

@[expose] noncomputable def mapsK (d w m dw : Nat) (f : Nat → Nat) (Kh Kq : Nat) : Bool :=
  allN d (fun k => inSpan d w m dw Kq (f (row w m Kh k)))

@[expose] noncomputable def img2 (w m h hm TL TH v : Nat) : Nat :=
  Nat.xor fld(TL, Nat.mul w (Nat.land v hm), m) fld(TH, Nat.mul w (Nat.shiftRight v h), m)

end CFSG.KC.XorSpan

end
