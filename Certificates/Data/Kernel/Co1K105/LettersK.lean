module

public import Certificates.Data.Kernel.Co1BW
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo

public section

namespace CFSG.KD.Co1K105

open CFSG.KC.Loop CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KC.M1F2 CFSG.KLie.CT

#kc_repo #kc_json_gz CFSG.KD.Co1K105
  "Certificates/Data/Kernel/Co1K105/data/LettersK.json.gz" 92050 8435935923150853778
  (lkAI : Nat) (lkCI : Nat) (lkWI : List Nat) (lkQG : List Nat) (lkQL : List Nat)
  (lkCodes : List (Nat × Nat))

@[expose] noncomputable def lkQ (a : Nat) (QG : List Nat) (i : Nat) : Nat :=
  strictN (Nat.rec (motive := fun _ => Nat) oneK
    (fun j acc => strictN acc fun x => nIf(bit i j, mulWK x (getL oneK QG j), x)) (nat_lit 8))
    fun x => nIf(bit i (nat_lit 8), mulWK x a, x)

@[expose] noncomputable def lkWord (x y len code : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) oneK
    (fun k acc => strictN acc fun w => mulWK w (nIf(bit code k, y, x))) len

@[expose] noncomputable def lkC (A AI E0 E1 a : Nat) : Nat :=
  strictN (mulWK (mulWK oneK E0) E1) fun z =>
    strictN (mulWK (mulWK (mulWK A z) AI) a) fun r => mulWK (mulWK (mulWK oneK r) r) A

@[expose] noncomputable def lkHead (A AI E0 E1 a CI : Nat) : Bool :=
  strictB (lkC A AI E0 E1 a) fun c =>
    andB (Nat.beq (mulWK A AI) oneK) (andB (Nat.beq (mulWK c CI) oneK)
      (eqK (mulWK (mulWK c (mulWK (mulWK oneK E0) E1)) CI) a))

@[expose] noncomputable def lkRows (a : Nat) (QG : List Nat) (QL : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih i => strictB i fun i => andB (andB (canK x) (eqK x (lkQ a QG i))) (ih (Nat.succ i)))
    QL

@[expose] noncomputable def lkNe (x : Nat) (t : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => andB (notB (Nat.beq x y)) ih) t

@[expose] noncomputable def lkDist (QL : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x t ih => andB (lkNe x t) ih) QL

@[expose] noncomputable def lkGens (QG QL : List Nat) : Bool :=
  andB (Nat.beq (lenL QL) (nat_lit 512))
    (allN (nat_lit 8) fun j => eqK (getL (nat_lit 0) QL (pw2 j)) (getL oneK QG j))

@[expose] noncomputable def lkPack (QL : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.lor x (Nat.shiftLeft ih (nat_lit 576))) QL

@[expose] noncomputable def lkChunks (P : Nat → Nat → Bool) (ch : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih c => andB
      (allN (nat_lit 40) fun k => (fun p => bIf(Nat.blt p (nat_lit 512), P p (fget x k (nat_lit 9)), true))
        (Nat.add (Nat.mul (nat_lit 40) c) k))
      (ih (Nat.succ c))) ch

@[expose] noncomputable def lkLetter (QP : Nat) (ch : List Nat) (g gi : Nat) : Bool :=
  strictB QP fun QP => strictB g fun g => strictB gi fun gi =>
    andB (Nat.beq (mulWK g gi) oneK) (andB (Nat.beq (lenL ch) (nat_lit 13))
      (lkChunks (fun p j => eqK (mulWK (mulWK g (fget QP p (nat_lit 576))) gi)
        (fget QP j (nat_lit 576))) ch (nat_lit 0)))

@[expose] noncomputable def lkG (c CI X : Nat) : Nat := mulWK (mulWK c X) CI

@[expose] noncomputable def lkPair (L : List (Nat × Nat)) : Nat → Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => (nat_lit 0, nat_lit 0))
    (fun x _ ih j => Nat.rec (motive := fun _ => Nat × Nat) x (fun k _ => ih k) j) L

@[expose] noncomputable def lkGetLL (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih l => Nat.rec (motive := fun _ => List Nat) x (fun k _ => ih k) l) L

end CFSG.KD.Co1K105

end
