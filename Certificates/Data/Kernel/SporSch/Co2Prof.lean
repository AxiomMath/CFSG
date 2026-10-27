module

public import Certificates.Data.Kernel.SporSch.Co2M

public section

namespace CFSG.KS.Co2P

open CFSG.KC.Enum CFSG.KS.Co2M

@[expose] noncomputable def mw (A B : ℕ) : ℕ := strictN A fun A => strictN B fun B => mmK A B

@[expose] noncomputable def isI (X : ℕ) : Bool := Nat.beq (Nat.mod X (Nat.pow 2 484)) I22

@[expose] noncomputable def isIZ (Z X : ℕ) : Bool :=
  bIf(isI X, true, Nat.beq (Nat.mod X (Nat.pow 2 484)) Z)

@[expose] noncomputable def fiK (p : ℕ → Bool) (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 0)
    (fun _ ih X => strictN X fun X => nIf(p X, nat_lit 0, Nat.succ (ih (mw X X)))) n

@[expose] noncomputable def cK (Z : ℕ) (n : ℕ) : ℕ → ℕ :=
  Nat.rec (motive := fun _ => ℕ → ℕ) (fun _ => nat_lit 0)
    (fun m ih X => strictN X fun X => nIf(isI X, nat_lit 0,
      strictN (mw X X) fun X2 => nIf(isIZ Z X, Nat.mul (nat_lit 8) (Nat.succ (fiK isI m X2)),
        Nat.add (ih X2) (nat_lit 9)))) n

@[expose] noncomputable def keyM (Y Z A B : ℕ) : ℕ := cK Z (nat_lit 6) (mw (mw B A) Y)

@[expose] noncomputable def incK (k : ℕ) : ℕ :=
  Nat.add (Nat.shiftLeft 1 (Nat.mul 16 (Nat.div k 8)))
    (Nat.shiftLeft 1 (Nat.mul 16 (Nat.add 7 (Nat.mod k 8))))

@[expose] noncomputable def hB (Y Z A : ℕ) : List ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun B _ ih acc => strictN (Nat.add acc (incK (keyM Y Z A B))) ih)

@[expose] noncomputable def hA (Y Z : ℕ) (T₁ : List ℕ) : List ℕ → ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun acc => acc)
    (fun A _ ih acc => strictN (hB Y Z A T₁ acc) ih)

@[expose] noncomputable def fieldK (H j : ℕ) : ℕ := Nat.land (Nat.shiftRight H (Nat.mul 16 j)) 65535

@[expose] noncomputable def rowK (H : ℕ) (row : List ℕ) : Bool :=
  allN 6 fun e => bAnd(Nat.beq (fieldK H e) (row.getD (Nat.add 6 e) 0),
    Nat.beq (fieldK H (Nat.add 7 e)) (row.getD e 0))

@[expose] noncomputable def profAll (ZM : ℕ) (YM : ℕ → ℕ) (T₀ T₁ : List ℕ) (tbl : List (List ℕ))
    (lo cnt : ℕ) : Bool :=
  strictB (Nat.mod ZM (Nat.pow 2 484)) fun Z => allN cnt fun i =>
    strictB (YM (Nat.add lo i)) fun Y => rowK (hA Y Z T₁ T₀ 0) (tbl.getD (Nat.add lo i) [])

end CFSG.KS.Co2P

end
