module

public import Certificates.Data.Kernel.D43.Twin

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS.ON

@[expose] noncomputable def cubeChk (F : Nat → Nat) (k p : Nat) : Bool :=
  strictB (tabAt F k p) fun a => bAnd(Nat.blt a (nat_lit 26572),
    strictB (tabAt F k a) fun b => bAnd(Nat.blt b (nat_lit 26572), Nat.beq (tabAt F k b) p))

@[expose] noncomputable def cubeChunk (F : Nat → Nat) (k c : Nat) : Bool :=
  allN (nat_lit 2048) fun t =>
    (fun s => bIf(Nat.blt s (nat_lit 26572), cubeChk F k s, true))
      (Nat.add (Nat.mul (nat_lit 2048) c) t)

end CFSG.KC.D43

end
