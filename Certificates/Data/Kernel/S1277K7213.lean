module

public import Certificates.Data.Kernel.S1277KML

public section

namespace CFSG.KC.C7213

open CFSG.Quasithin.H13.S127.Mod CFSG.KC.S1277ML CFSG.KC.S1277Gm

@[expose] noncomputable def forceM (X : Mc) (k : Mc → Bool) : Bool :=
  strictB X.c0 fun a => strictB X.c1 fun b => strictB X.c2 fun c => k ⟨a, b, c⟩

@[expose] noncomputable def isOne (B : Mc) : Bool :=
  andB (Nat.beq B.c0 (nat_lit 1)) (andB (Nat.beq B.c1 (nat_lit 4)) (Nat.beq B.c2 (nat_lit 16)))

@[expose] noncomputable def pw (A : Mc) (n : ℕ) : Mc → Bool :=
  Nat.rec (motive := fun _ => Mc → Bool) isOne (fun _ r B => forceM (mulF A B) r) n

@[expose] noncomputable def ndK (L : List ℕ) : ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun _ => true)
    (fun x _ r s => andB (andB (Nat.blt x (nat_lit 262144)) (notB (memS s x)))
      (strictB (insS s x) r)) L

@[expose] noncomputable def setK (L : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun s => s)
    (fun x _ r s => CFSG.KC.Enum.strictN (insS s x) r) L

@[expose] noncomputable def eltK (n : ℕ) : Bool :=
  andB (inGm (Mc.ofIdx n)) (pw (Mc.ofIdx n) (nat_lit 60) Mc.one)

@[expose] def v18 : List ℕ := [1, 2, 3, 4, 8, 12, 16, 21, 27, 30, 32, 39, 42, 45, 48, 54, 57, 63]

@[expose] noncomputable def colK (s : ℕ) : Bool :=
  allL (fun a => allL (fun b => allL (fun c =>
    orB (notB (inGm ⟨a, b, c⟩)) (memS s (mcIdx ⟨a, b, c⟩))) v18) v18) v18

@[expose] noncomputable def chk7213 (L : List ℕ) : Bool :=
  andB (ndK L 0) (andB (allL eltK L) (strictB (setK L 0) colK))

end CFSG.KC.C7213

end
