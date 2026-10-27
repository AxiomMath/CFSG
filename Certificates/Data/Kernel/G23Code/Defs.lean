module

public import Certificates.Data.Kernel.LocLn.Defs
public import Certificates.Data.G23RecogNativeInputs
public import Certificates.Data.G23RecogWordsInputs

public section

namespace CFSG.KD.G23C

open CFSG.KC.Ord CFSG.KC.Loop CFSG.KD.LocLn CFSG.GH74.QTGen4.Recog.G23

@[expose] noncomputable def L : Nat := rep1 (nat_lit 8) (nat_lit 196)

@[expose] noncomputable def H : Nat := Nat.shiftLeft L (nat_lit 7)

@[expose] noncomputable def CM : Nat := Nat.mul (nat_lit 255) (rep1 (nat_lit 112) (nat_lit 14))

@[expose] noncomputable def RM : Nat := Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 112)) (nat_lit 1)

@[expose] noncomputable def ONE : Nat := rep1 (nat_lit 120) (nat_lit 14)

@[expose] noncomputable def LV : Nat := rep1 (nat_lit 8) (nat_lit 14)

@[expose] noncomputable def HV : Nat := Nat.shiftLeft LV (nat_lit 7)

@[expose] noncomputable def constsChk : Bool :=
  constsOK (nat_lit 3) (nat_lit 8) (nat_lit 112) (nat_lit 14) (nat_lit 5) L H CM RM ONE LV HV

@[expose] noncomputable def mul (A B : Nat) : Nat :=
  mulR (nat_lit 3) (nat_lit 8) (nat_lit 112) (nat_lit 14) (nat_lit 5) L H CM RM A B

@[expose] noncomputable def codeChk (l : List Nat) : Bool :=
  bAnd(Nat.beq (lenL l) (nat_lit 196), smallL l)

@[expose] noncomputable def invChk (i : Fin 6) : Bool :=
  bAnd(codeChk (eCode i), bAnd(codeChk (eInvCode i),
    Nat.beq (mul (pkL (eCode i)) (pkL (eInvCode i))) ONE))

@[expose] noncomputable def letP (l : Fin 6 × Bool) : Nat :=
  Bool.rec (motive := fun _ => Nat) (pkL (eInvCode l.1)) (pkL (eCode l.1)) l.2

@[expose] noncomputable def evalFrom (r : List (Fin 6 × Bool)) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun l _ ih a => strictN (mul a (letP l)) ih) r

@[expose] noncomputable def evalP (r : List (Fin 6 × Bool)) : Nat := evalFrom r ONE

@[expose] noncomputable def wordsChk (W : List (List (Fin 6 × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih => bAnd(Nat.beq (evalP r) ONE, ih)) W

end CFSG.KD.G23C

end
