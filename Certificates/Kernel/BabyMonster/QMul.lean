module

public import Certificates.Data.CFSGNative.CTIB.Census
public import CFSG.Certificates.Kernel.BabyMonster.CensusSound
public import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelBM

open CFSG.KC.BM CFSG.Monster.B.CTIB.Native

@[expose] noncomputable def xorB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b (notB b) a

@[expose] noncomputable def testB (u n : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.shiftRight u n) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def cAtK (gj u j n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun m ih => xorB ih (andB (Nat.blt j m) (andB (testB u m) (testB gj m)))) n

@[expose] noncomputable def corrK (G : List Nat) (a b m : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false
    (fun m ih => Bool.rec (motive := fun _ => Bool) ih (xorB ih (cAtK (nthN G m) a m (nat_lit 22)))
      (testB b m)) m

@[expose] noncomputable def qmulK (G : List Nat) (a b : Nat) : Nat :=
  Nat.lor (Nat.mod (Nat.xor a b) (Nat.pow (nat_lit 2) (nat_lit 22)))
    (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.pow (nat_lit 2) (nat_lit 22))
      (xorB (xorB (testB a (nat_lit 22)) (testB b (nat_lit 22))) (corrK G a b (nat_lit 22))))

@[expose] noncomputable def squaresK (G : List Nat) : Bool :=
  andB (Nat.beq (qmulK G 1 1) 0) (andB (Nat.beq (qmulK G 3 3) 0) (andB (Nat.beq (qmulK G 7 7) 0)
    (andB (Nat.beq (qmulK G 17 17) (Nat.pow 2 22)) (Nat.beq (qmulK G 19 19) (Nat.pow 2 22)))))

theorem xorB_eq (a b : Bool) : xorB a b = (a ^^ b) := by
  cases a <;> cases b <;> rfl

theorem andB_eq (a b : Bool) : andB a b = (a && b) := by
  cases a <;> rfl

theorem testB_eq (u n : Nat) : testB u n = u.testBit n := by
  rw [testB, Nat.testBit]
  have e1 : Nat.land (Nat.shiftRight u n) 1 = (u >>> n) % 2 := Nat.and_one_is_mod _
  have e2 : (1 &&& (u >>> n)) = (u >>> n) % 2 := Nat.one_and_eq_mod_two _
  rw [e1, e2]
  rcases Nat.mod_two_eq_zero_or_one (u >>> n) with h | h <;> rw [h] <;> rfl

theorem blt_eq (j m : Nat) : Nat.blt j m = decide (j < m) := by
  rw [Bool.eq_iff_iff, Nat.blt_eq, decide_eq_true_iff]

theorem nthN_eq_getD : ∀ (G : List Nat) (j : Nat), nthN G j = G.toArray.getD j 0
  | [], j => by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
    rfl
  | x :: G, 0 => by
    rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray]
    rfl
  | x :: G, j + 1 => by
    have e : nthN (x :: G) (j + 1) = nthN G j := rfl
    rw [e, nthN_eq_getD G j, Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
      List.getElem?_toArray, List.getElem?_toArray, List.getElem?_cons_succ]

theorem cAtK_eq (gj u j : Nat) : ∀ n, cAtK gj u j n = cAtN gj u j n
  | 0 => rfl
  | n + 1 => by
    have e : cAtK gj u j (n + 1) =
        xorB (cAtK gj u j n) (andB (Nat.blt j n) (andB (testB u n) (testB gj n))) := rfl
    rw [e, cAtK_eq gj u j n, cAtN, xorB_eq, andB_eq, andB_eq, blt_eq, testB_eq, testB_eq,
      Bool.and_assoc]

theorem corrK_eq (G : List Nat) (a b : Nat) : ∀ m, corrK G a b m = corrN G.toArray a b m
  | 0 => rfl
  | m + 1 => by
    have e : corrK G a b (m + 1) = Bool.rec (motive := fun _ => Bool) (corrK G a b m)
        (xorB (corrK G a b m) (cAtK (nthN G m) a m 22)) (testB b m) := rfl
    rw [e, corrN, corrK_eq G a b m, testB_eq, xorB_eq, cAtK_eq, nthN_eq_getD]
    cases b.testBit m <;> rfl

theorem qmulK_eq (G : List Nat) (a b : Nat) : qmulK G a b = qmul G.toArray a b := by
  rw [qmulK, qmul, xorB_eq, xorB_eq, testB_eq, testB_eq, corrK_eq]
  unfold corr
  cases (a.testBit 22 ^^ b.testBit 22) ^^ corrN G.toArray a b 22 <;> rfl

theorem squaresOK_true : squaresOK () = true := by
  have h : squaresK CFSG.Monster.B.Bin.gramRows = true := by quickRfl
  rw [squaresK] at h
  obtain ⟨h1, h⟩ := CFSG.KC.BM.andB_eq_true h
  obtain ⟨h2, h⟩ := CFSG.KC.BM.andB_eq_true h
  obtain ⟨h3, h⟩ := CFSG.KC.BM.andB_eq_true h
  obtain ⟨h4, h5⟩ := CFSG.KC.BM.andB_eq_true h
  rw [squaresOK, gArr, ← qmulK_eq, ← qmulK_eq, ← qmulK_eq, ← qmulK_eq, ← qmulK_eq,
    Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3,
    Nat.eq_of_beq_eq_true h4, Nat.eq_of_beq_eq_true h5]
  rfl

end CertificateChecks.KernelBM

end
