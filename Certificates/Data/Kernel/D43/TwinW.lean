module

public import Certificates.Data.Kernel.D43.Twin
public import Certificates.Data.Kernel.Spor.ONVKW

public section

namespace CFSG.KC.D43

open CFSG.KC.Enum CFSG.KS.ON CFSG.KS.ONW

@[expose] noncomputable def chunkCnt (lo : Nat) : Nat :=
  nIf(Nat.blt (Nat.add lo (nat_lit 256)) (nat_lit 26573), nat_lit 256, Nat.sub (nat_lit 26572) lo)

@[expose] noncomputable def keyChunkW (KT : Nat → Nat) (L : List Nat) (T : Nat → Nat) (c : Nat) :
    Bool :=
  strictB (Nat.mul (nat_lit 256) c) fun lo => strictB (chunkCnt lo) fun cnt =>
    ptsV (key KT) (fun p => key KT (T p))
      (fun p x _ => bAnd(Nat.blt (T p) (nat_lit 26572), canon x)) lo (finP L cnt) cnt
      (nat_lit 0) (nat_lit 0)

end CFSG.KC.D43

end
