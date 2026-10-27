module

public import Certificates.Data.Kernel.KDenseP.Chunk

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.KDense

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def forceB (s : St) (k : St → Bool) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun f r => Prod.rec (motive := fun _ => Bool) (fun X r2 =>
    Prod.rec (motive := fun _ => Bool) (fun A W =>
      Bool.rec (motive := fun _ => Bool) false
        (strictB X (fun X' => strictB A (fun A' => strictB W (fun W' => k (true, X', A', W'))))) f)
      r2) r) s

@[expose] noncomputable def upd (T : Nat → St) (j : Nat) (r : St) (x : Nat) : St :=
  Bool.rec (motive := fun _ => St) (T x) r (Nat.beq x j)

@[expose] noncomputable def updD (D : Nat → Bool) (j x : Nat) : Bool := orB (Nat.beq x j) (D x)

@[expose] noncomputable def prodL (PR : Nat → Nat) (w k c : Nat) : Bool :=
  andB (notB (Nat.beq (f20 c (nat_lit 5)) (nat_lit 1))) (andB (Nat.beq (PR (f20 c (nat_lit 4))) k)
    (andB (Nat.blt (f20 c (nat_lit 3)) (f20 c (nat_lit 4))) (Nat.ble w (f20 c (nat_lit 4)))))

@[expose] noncomputable def rpl (run : Nat → St → St) (chk : (Nat → St) → Nat → Bool)
    (CH PR : Nat → Nat) (w : Nat) : List Nat → (Nat → St) → (Nat → Bool) → Bool :=
  List.rec (motive := fun _ => (Nat → St) → (Nat → Bool) → Bool) (fun _ _ => true)
    (fun k _ ih T D => (fun c => andB (D (f20 c (nat_lit 3)))
      (Bool.rec (motive := fun _ => Bool)
        (andB (D (f20 c (nat_lit 4))) (andB (chk T c) (ih T D)))
        (forceB (run c (T (f20 c (nat_lit 3))))
          (fun r => ih (upd T (f20 c (nat_lit 4)) r) (updD D (f20 c (nat_lit 4)))))
        (prodL PR w k c))) (CH k))

@[expose] noncomputable def grpL (run : Nat → St → St) (chk : (Nat → St) → Nat → Bool)
    (CH PR : Nat → Nat) (G : Nat → List Nat) (S0 : Nat → St) (w g : Nat) : Bool :=
  rpl run chk CH PR w (G g) S0 (fun x => Nat.blt x w)

@[expose] noncomputable def memB (k : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ acc => orB (Nat.beq a k) acc) l

@[expose] noncomputable def covL (GK : Nat → Nat) (G : Nat → List Nat) (ng : Nat) : Nat → Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun k acc => andB (andB (Nat.blt (GK k) ng) (memB k (G (GK k)))) acc)

end CFSG.KC.KDenseP

end
