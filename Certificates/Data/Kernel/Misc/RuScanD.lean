module

public import Certificates.Data.Kernel.Misc.RuScan

public section

namespace CFSG.KC.Misc.RuScan

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.Misc.RuInv

@[expose] noncomputable def witKD (ys : List Nat) (T r : Nat) : Bool :=
  bIf(Nat.beq (Nat.land r (nat_lit 3)) (nat_lit 2), true, witK ys T r)

@[expose] noncomputable def chk2D (LR TR W : Nat → Nat) (H T lo cnt : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun i =>
    strictB (TR (Nat.add o0 (Nat.div i c1))) (fun t0 =>
    strictB (TR (Nat.add o1 (Nat.mod i c1))) (fun t1 =>
      witKD [H, t0, t1] T (W i))))))))

@[expose] noncomputable def chk3D (LR TR W : Nat → Nat) (H T lo cnt : Nat) : Bool :=
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 0)) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 1)) (fun o1 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) (LR 2)) (fun o2 =>
  strictB (rcnt (LR 1)) (fun c1 =>
  strictB (rcnt (LR 2)) (fun c2 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun i =>
    strictB (Nat.div i c2) (fun q =>
    strictB (TR (Nat.add o0 (Nat.div q c1))) (fun t0 =>
    strictB (TR (Nat.add o1 (Nat.mod q c1))) (fun t1 =>
    strictB (TR (Nat.add o2 (Nat.mod i c2))) (fun t2 =>
      witKD [H, t0, t1, t2] T (W i))))))))))))

end CFSG.KC.Misc.RuScan

end
