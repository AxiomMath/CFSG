module

public import Certificates.Data.Kernel.J4Run

public section

namespace CFSG.KJ4.R

open CFSG.KJ4 CFSG.KJ4.S CFSG.KC.Loop

@[expose] noncomputable def ojAt (FT OT : Nat → Nat) (g : Nat) : Bool :=
  letB (fJ (FT g)) (fun J => orB (Nat.beq J (nat_lit 0)) (Nat.beq (oJ (OT (Nat.sub J (nat_lit 1)))) J))

@[expose] noncomputable def j4MFix (k : KD) (d : MD) : Bool :=
  andB (Nat.ble d.nH (nat_lit 65536)) (andB (Nat.ble d.nSG (nat_lit 65536))
  (andB (Nat.ble d.nW (nat_lit 65536))
  (andB (allIn (nat_lit 0) d.nW (fun w => Nat.blt (wR (d.WT w)) (nat_lit 12)))
  (andB (allIn d.nH (nat_lit 65536) (fun a => Nat.beq (d.HT a) (nat_lit 0)))
  (andB (allIn d.nSG (nat_lit 65536) (fun e => Nat.beq (d.SG e) (nat_lit 0)))
  (andB (allIn d.nW (nat_lit 65536) (fun w => Nat.beq (d.WT w) (nat_lit 0)))
    (allIn (nat_lit 0) k.NF (ojAt k.FT k.OT))))))))

end CFSG.KJ4.R

end
