module

public import Certificates.Data.Kernel.N6ModClass
public import Certificates.Data.Kernel.N7ModClass

public section

namespace CFSG.KernelN6F

open CFSG.CGT.T75JM CFSG.CGT.T75M23 CFSG.KernelN6 CFSG.KernelN7

@[expose] noncomputable def bitF (v i x : ℕ) : ℕ :=
  Bool.rec (motive := fun _ => ℕ) x 0 (Nat.beq (Nat.land 1 (Nat.shiftRight v i)) 0)

theorem bitF_eq (v i x : ℕ) : bitF v i x = if v.testBit i = true then x else 0 := by
  unfold bitF Nat.testBit
  cases h : Nat.beq (Nat.land 1 (Nat.shiftRight v i)) 0
  · have h' : (1 &&& v >>> i != 0) = true := by
      simp only [bne, Bool.not_eq_true']
      exact h
    simp only [h', ite_true]
  · have h' : (1 &&& v >>> i != 0) = false := by
      simp only [bne, Bool.not_eq_false']
      exact h
    simp only [h']
    rfl

@[expose] noncomputable def applyCF (c : Cols) (v : ℕ) : ℕ :=
  Nat.xor (Nat.xor (Nat.xor (bitF v 0 c.c0) (bitF v 1 c.c1)) (bitF v 2 c.c2)) (bitF v 3 c.c3)

theorem applyCF_eq (c : Cols) (v : ℕ) : applyCF c v = applyC c v := by
  simp only [applyCF, applyC, bitF_eq]
  rfl

@[expose] noncomputable def compCF (c d : Cols) : Cols :=
  ⟨applyCF c d.c0, applyCF c d.c1, applyCF c d.c2, applyCF c d.c3⟩

theorem compCF_eq (c d : Cols) : compCF c d = compC c d := by
  simp only [compCF, compC, applyCF_eq]

@[expose] noncomputable def powCF (c : Cols) (n : ℕ) : Cols :=
  Nat.rec (motive := fun _ => Cols) idC (fun _ ih => compCF c ih) n

theorem powCF_eq (c : Cols) : ∀ n, powCF c n = powC c n
  | 0 => rfl
  | n + 1 => by
    rw [show powCF c (n + 1) = compCF c (powCF c n) from rfl, compCF_eq, powCF_eq c n]
    rfl

@[expose] noncomputable def unpackCF (m : ℕ) : Cols :=
  ⟨Nat.mod m 16, Nat.mod (Nat.div m 16) 16, Nat.mod (Nat.div m 256) 16, Nat.mod (Nat.div m 4096) 16⟩

theorem unpackCF_eq (m : ℕ) : unpackCF m = unpackC m := rfl

@[expose] noncomputable def isInvCF (X : Cols) : Bool :=
  eqC (compCF X X) idC && !eqC X idC

@[expose] noncomputable def isInvBF (m : ℕ) : Bool := isInvCF (unpackCF m)

theorem isInvBF_fun : isInvBF = isInvB := by
  funext m
  simp only [isInvBF, isInvCF, isInvB, unpackCF_eq, compCF_eq]

@[expose] noncomputable def relCBF (X Y : Cols) : Bool :=
  eqC (compCF X X) idC && !eqC X idC && eqC (powCF Y 4) idC && eqC (powCF (compCF X Y) 5) idC &&
    eqC (powCF (compCF X (compCF Y Y)) 5) idC

@[expose] noncomputable def relBF (r n : ℕ) : Bool := relCBF (repC r) (unpackCF n)

theorem relBF_fun (r : ℕ) : relBF r = relB r := by
  funext n
  simp only [relBF, relB, relCBF, relCB, unpackCF_eq, compCF_eq, powCF_eq]

@[expose] noncomputable def relCB7F (X Y : Cols) : Bool :=
  eqC (compCF X X) idC && !eqC X idC && eqC (powCF Y 5) idC &&
    eqC (powCF (compCF X (compCF Y (compCF X (powCF Y 4)))) 3) idC &&
    eqC (powCF (compCF (powCF Y 4) X) 7) idC &&
    eqC (compCF X (compCF Y (compCF X (compCF (powCF (compCF Y (compCF X (compCF (powCF Y 4)
      (compCF X Y)))) 2) (compCF Y (compCF X (powCF Y 4))))))) idC

@[expose] noncomputable def relB7F (r n : ℕ) : Bool := relCB7F (repC7 r) (unpackCF n)

theorem relB7F_fun (r : ℕ) : relB7F r = relB7 r := by
  funext n
  simp only [relB7F, relB7, relCB7F, relCB7, unpackCF_eq, compCF_eq, powCF_eq]

theorem andT {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]
  rfl

theorem eqNL_append : ∀ {A C B D : List ℕ}, eqNL A C = true → eqNL B D = true →
    eqNL (A ++ B) (C ++ D) = true
  | [], [], _, _, _, h => h
  | _ :: _, _ :: _, _, _, h1, h2 => by
    simp only [eqNL, Bool.and_eq_true] at h1
    simp only [List.cons_append, eqNL, Bool.and_eq_true]
    exact ⟨h1.1, eqNL_append h1.2 h2⟩
  | [], _ :: _, _, _, h, _ => by simp [eqNL] at h
  | _ :: _, [], _, _, h, _ => by simp [eqNL] at h

theorem eqNL_chunk {p : ℕ → Bool} {M : List ℕ} {a m k d c : ℕ}
    (h1 : eqNL ((List.range' a m).filter p) ((M.drop d).take c) = true)
    (h2 : eqNL ((List.range' (a + m) k).filter p) (M.drop (d + c)) = true) :
    eqNL ((List.range' a (m + k)).filter p) (M.drop d) = true := by
  rw [← List.range'_append_1, List.filter_append, ← List.take_append_drop c (M.drop d),
    List.drop_drop]
  exact eqNL_append h1 h2

end CFSG.KernelN6F

end
