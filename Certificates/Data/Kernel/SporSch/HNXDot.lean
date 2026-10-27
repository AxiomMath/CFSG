module

public import Certificates.Data.Kernel.SporSch.HNXOrb

public section

namespace CFSG.KC.LL.HNX

open CFSG.KC.Loop CFSG.KC.LL

@[expose] noncomputable def spreadR (MR A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) A
    (fun i acc => strictN acc (fun a => sp1 a (fldW MR (Nat.mul (nat_lit 110656) i) (nat_lit 110656))
      (Nat.mul (nat_lit 10) (Nat.shiftLeft (nat_lit 1) (Nat.sub (nat_lit 7) i))))) (nat_lit 8)

@[expose] noncomputable def selT (Y S L1 t : Nat) : Nat :=
  Nat.shiftLeft (Nat.land Y (Nat.mul (Nat.land (Nat.shiftRight S t) L1) (nat_lit 8191))) t

@[expose] noncomputable def cntRows (P v c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.add acc (nIf(Nat.beq (Nat.mod (fldW P (Nat.add (Nat.mul (nat_lit 1729) r)
      (nat_lit 1716)) (nat_lit 13)) (nat_lit 5)) v, nat_lit 1, nat_lit 0))) c

@[expose] noncomputable def dotLeaf (T : Nat → Nat) (CM3 M MR L1 ONES G v b c : Nat) : Nat :=
  strictN (leafA (T b) (nat_lit 464) c M) (fun A =>
  strictN (mulC CM3 A G) (fun Y =>
  strictN (spreadR MR A) (fun S =>
  strictN (Nat.mul (Nat.add (selT Y S L1 (nat_lit 0)) (Nat.add (selT Y S L1 (nat_lit 1))
      (selT Y S L1 (nat_lit 2)))) ONES) (fun P => cntRows P v c))))

@[expose] noncomputable def dotSum (T : Nat → Nat) (CM3 M MR L1 ONES G v lo n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => strictN acc (fun a => Nat.add a
      (dotLeaf T CM3 M MR L1 ONES G v (Nat.add lo i) (CFSG.KS.SporSch.hnxC (Nat.add lo i))))) n

@[expose] noncomputable def dotConstsOK (MS REP ONES L1 MR : Nat) : Bool :=
  bAnd(Nat.beq REP (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 1729) r))) (nat_lit 64)),
  bAnd(Nat.beq ONES (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun k acc => Nat.lor acc (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 13) k))) (nat_lit 133)),
  bAnd(Nat.beq L1 (Nat.mul ONES REP),
  bAnd(Nat.beq (Nat.shiftRight MR (Nat.mul (nat_lit 110656) (nat_lit 8))) (nat_lit 0),
    Nat.rec (motive := fun _ => Bool) true
      (fun i ih => bAnd(Nat.beq (fldW MR (Nat.mul (nat_lit 110656) i) (nat_lit 110656))
        (Nat.mul (fldW MS (Nat.mul (nat_lit 1729) i) (nat_lit 1729)) REP), ih)) (nat_lit 8)))))

end CFSG.KC.LL.HNX

end
