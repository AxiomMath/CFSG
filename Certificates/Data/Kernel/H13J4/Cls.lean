module

public import Certificates.Data.Kernel.SporSch.J4SSylow

public section

namespace CFSG.KS.H13J4

open CFSG.KC.Enum CFSG.KS CFSG.KS.SporSch.C11

@[expose] noncomputable def conjK (P Q B : Nat) : Nat := compK (compK P B) Q

@[expose] noncomputable def stepK (G GI T PAR GEN NX : Nat → Nat) (m n i : Nat) : Bool :=
  strictB (T i) fun t =>
    bAnd(bIf(Nat.beq i (nat_lit 0), true, strictB (PAR i) fun p => strictB (GEN i) fun g =>
        bAnd(Nat.blt p i, bAnd(Nat.blt g m, Nat.beq t (conjK (G g) (GI g) (T p))))),
      allN m fun g => strictB (NX (Nat.add (Nat.mul m i) g)) fun j =>
        bAnd(Nat.blt j n, Nat.beq (T j) (conjK (GI g) (G g) t)))

@[expose] noncomputable def stepAt (G GI T PAR GEN NX : Nat → Nat) (m n i : Nat) : Bool :=
  bIf(Nat.blt i n, stepK G GI T PAR GEN NX m n i, true)

end CFSG.KS.H13J4

end
