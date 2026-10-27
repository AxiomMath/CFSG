module

public import Certificates.Data.Kernel.FixBoundK.Member
public import Certificates.Data.Kernel.SortTree

public section

namespace CFSG.KC.FixBoundK.Triv

open CFSG.KLie.CT CFSG.KC.SortTree CFSG.KC.FixBoundK CFSG.KC.Loop

@[expose] noncomputable def syL : List Nat := [nat_lit 62, nat_lit 129, nat_lit 65, nat_lit 193,
  nat_lit 61, nat_lit 514, nat_lit 258, nat_lit 770, nat_lit 59, nat_lit 2052, nat_lit 1028,
  nat_lit 3076, nat_lit 55, nat_lit 2696, nat_lit 1352, nat_lit 4040, nat_lit 47, nat_lit 2896,
  nat_lit 1744, nat_lit 3472, nat_lit 31, nat_lit 2528, nat_lit 1952, nat_lit 3680]

@[expose] noncomputable def bmL : List Nat := [nat_lit 1118494, nat_lit 1118689, nat_lit 1121809,
  nat_lit 1171729, nat_lit 1970449, nat_lit 14749969, nat_lit 10928140, nat_lit 7118858,
  nat_lit 6996160, nat_lit 13017248, nat_lit 13421568, nat_lit 11184640]

@[expose] noncomputable def omK : Nat := nat_lit 16777215

@[expose] noncomputable def actK (cs : List Nat) (m : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih m => Nat.xor (nIf(Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1), c, nat_lit 0))
      (ih (Nat.shiftRight m (nat_lit 1)))) cs m

@[expose] noncomputable def synK (x : Nat) : Nat := actK syL x

@[expose] noncomputable def cwK (m : Nat) : Nat := actK bmL m

@[expose] noncomputable def compatK (x y : Nat) : Bool := Nat.beq (synK (Nat.land x y)) (nat_lit 0)

@[expose] noncomputable def exclK (x₁ x₂ : Nat) : Bool :=
  orB (Nat.beq x₂ (nat_lit 0)) (orB (Nat.beq x₂ omK)
    (orB (Nat.beq x₂ x₁) (Nat.beq x₂ (Nat.xor x₁ omK))))

@[expose] noncomputable def spanK (x₁ x₂ x₃ : Nat) : Bool :=
  orB (exclK x₁ x₃) (orB (Nat.beq x₃ x₂) (orB (Nat.beq x₃ (Nat.xor x₂ omK))
    (orB (Nat.beq x₃ (Nat.xor x₁ x₂)) (Nat.beq x₃ (Nat.xor (Nat.xor x₁ x₂) omK)))))

@[expose] noncomputable def sortK (x₁ : Nat) (k₁ : List Nat) (p : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun m _ ih p => bAnd(Nat.ble p m, bAnd(Nat.blt m (nat_lit 4096),
      bAnd(compatK x₁ (cwK m), ih (Nat.succ m))))) k₁ p

@[expose] noncomputable def trivRep (x₁ : Nat) (k₁ : List Nat) : Bool :=
  bAnd(sortK x₁ k₁ (nat_lit 0),
  bAnd(Nat.beq (sumBelow (nat_lit 4096) (nat_lit 64)
      (fun m => nIf(compatK x₁ (cwK m), nat_lit 1, nat_lit 0))) (lenS k₁),
    allS (fun m₂ => strictK (cwK m₂) fun x₂ => orB (exclK x₁ x₂)
      (allS (fun m₃ => strictK (cwK m₃) fun x₃ => orB (notB (compatK x₂ x₃)) (spanK x₁ x₂ x₃))
        k₁)) k₁))

@[expose] noncomputable def trivAt (reps : List Nat) (k1s : List (List Nat)) (i : Nat) : Bool :=
  trivRep (nthS (nat_lit 0) reps i) (nthS [] k1s i)

@[expose] noncomputable def pmK (G x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j ih => Nat.xor (nIf(bit x j, pw2 (fget G j (nat_lit 5)), nat_lit 0)) ih) (nat_lit 24)

@[expose] noncomputable def genK (GS GA k : Nat) : Nat :=
  nIf(Nat.blt k (nat_lit 10), fget GS k (nat_lit 120),
    fget GA (Nat.sub k (nat_lit 10)) (nat_lit 120))

@[expose] noncomputable def wordK (GS GA : Nat) (w : List Nat) (y : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k _ ih y => ih (pmK (genK GS GA k) y)) w y

@[expose] noncomputable def entK (GS GA : Nat) (reps : List Nat) (k : Nat) (e : Nat × List Nat) :
    Bool :=
  bAnd(Nat.blt e.1 (lenS reps), bAnd(allS (fun l => Nat.blt l (nat_lit 12)) e.2,
    strictK (wordK GS GA e.2 (nthS (nat_lit 0) reps e.1)) fun y =>
      strictK (cwK (Nat.shiftLeft k (nat_lit 1))) fun c =>
        orB (Nat.beq y c) (Nat.beq y (Nat.xor c omK))))

@[expose] noncomputable def runK (GS GA : Nat) (reps : List Nat) (n : Nat)
    (l : List (Nat × List Nat)) (k₀ : Nat) : Bool :=
  bAnd(Nat.beq (lenS l) n,
    List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
      (fun e _ ih k => bAnd(entK GS GA reps k e, ih (Nat.succ k))) l k₀)

@[expose] noncomputable def wsAt (GS GA : Nat) (reps : List Nat) (ws : List (List (Nat × List Nat)))
    (c : Nat) : Bool :=
  (fun r => runK GS GA reps (nIf(Nat.blt r (nat_lit 128), r, nat_lit 128)) (nthS [] ws c)
      (Nat.succ (Nat.mul (nat_lit 128) c)))
    (Nat.sub (nat_lit 2047) (Nat.mul (nat_lit 128) c))

end CFSG.KC.FixBoundK.Triv

end
