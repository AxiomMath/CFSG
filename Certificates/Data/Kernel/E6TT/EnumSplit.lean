module

public import Certificates.Data.Kernel.E6TT.Enum
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictN strictB)

theorem strictN_eq' (y : Nat) (k : Nat → Nat) : strictN y k = k y := by
  cases y <;> rfl

theorem sumP_succS (n : Nat) (f : Nat → Nat) (p : Nat) :
    sumP (n + 1) f p = nIf(Nat.beq (Nat.land p 127) 0, 0,
      Nat.add (f (Nat.sub (Nat.land p 127) 1)) (sumP n f (Nat.shiftRight p 7))) := by
  show strictN p (fun p => strictN (Nat.land p 127) fun e =>
      nIf(Nat.beq e 0, 0, strictN (Nat.sub e 1) fun a =>
        Nat.add (f a) (sumP n f (Nat.shiftRight p 7)))) = _
  rw [strictN_eq', strictN_eq', strictN_eq']

theorem sumP_add_le (f : Nat → Nat) : ∀ (a b p : Nat),
    sumP (a + b) f p ≤ sumP a f p + sumP b f (Nat.shiftRight p (7 * a))
  | 0, b, p => by
    rw [Nat.zero_add, Nat.mul_zero]
    show sumP b f p ≤ 0 + sumP b f (p >>> 0)
    rw [Nat.zero_add, Nat.shiftRight_zero]
    exact Nat.le_refl _
  | a + 1, b, p => by
    rw [show a + 1 + b = (a + b) + 1 by omega, sumP_succS, sumP_succS]
    cases Nat.beq (Nat.land p 127) 0
    · have ih := sumP_add_le f a b (Nat.shiftRight p 7)
      have e : Nat.shiftRight (Nat.shiftRight p 7) (7 * a) = Nat.shiftRight p (7 * (a + 1)) := by
        show (p >>> 7) >>> (7 * a) = p >>> (7 * (a + 1))
        rw [← Nat.shiftRight_add, Nat.mul_succ, Nat.add_comm]
      rw [e] at ih
      show Nat.add _ (sumP (a + b) f _) ≤ Nat.add _ (sumP a f _) + _
      simp only [Nat.add_eq]
      omega
    · exact Nat.zero_le _

theorem sumP_zero_of_parts {f : Nat → Nat} {p : Nat} (a b c : Nat) (hc : a + b = c)
    (h1 : Nat.beq (sumP a f p) 0 = true) (h2 : Nat.beq (sumP b f (Nat.shiftRight p (7 * a))) 0 = true) :
    Nat.beq (sumP c f p) 0 = true := by
  subst hc
  have h := sumP_add_le f a b p
  rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2] at h
  rw [Nat.le_zero.1 h]
  rfl

@[expose] noncomputable def enumBody (GR N1 N2 N3 N4 N5 : Nat)
    (leaf : Nat → Nat → Nat → Nat → Nat → Nat → Nat) (a0 : Nat) : Nat :=
    sumP (nat_lit 20) (fun a2 =>
      strictN (Nat.lor (lm a0) (lm a2)) fun m1 =>
      sumP (nat_lit 20) (fun a3 =>
        nIf(zt (rowOf GR a3) (lm a0),
          sumP (nat_lit 20) (fun a1 =>
            nIf(zt (rowOf GR a1) m1,
              strictN (Nat.lor m1 (lm a1)) fun m4 =>
              strictN (Nat.lor m4 (lm a3)) fun m5 =>
              sumP (nat_lit 20) (fun a4 =>
                nIf(zt (rowOf GR a4) m4,
                  sumP (nat_lit 20) (fun a5 =>
                    nIf(zt (rowOf GR a5) m5, leaf a0 a1 a2 a3 a4 a5, nat_lit 0))
                    (slotOf N5 a4),
                  nat_lit 0))
                (slotOf N4 a3),
              nat_lit 0))
            (slotOf N1 a3),
          nat_lit 0))
        (slotOf N3 a2))
      (slotOf N2 a0)

theorem enumK_eq (GR L0 N1 N2 N3 N4 N5 : Nat) (leaf : Nat → Nat → Nat → Nat → Nat → Nat → Nat) :
    enumK GR L0 N1 N2 N3 N4 N5 leaf = sumP 72 (enumBody GR N1 N2 N3 N4 N5 leaf) L0 := rfl

end CFSG.KC.E6TT

end
