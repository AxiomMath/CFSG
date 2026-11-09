module

public import Certificates.Data.Kernel.Co1B

public section

namespace CFSG.KC.Co1B

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KLie.CT

@[expose] noncomputable def stepsPre (RS RIS : List Nat) (derivs : List (List Int)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih k => andB (Nat.beq (getL oneK RS k) (wordK (takeK k RS) (takeK k RIS) w)) (ih (Nat.succ k)))
    derivs

theorem andB_eq_true' {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> simp [andB]

theorem stepsK_append (RS RIS : List Nat) : ∀ (d1 d2 : List (List Int)) (k : Nat),
    stepsPre RS RIS d1 k = true → stepsK RS RIS d2 (k + d1.length) = true →
    stepsK RS RIS (d1 ++ d2) k = true
  | [], _, _, _, h2 => h2
  | w :: d1, d2, k, h1, h2 => by
    have h1' : andB (Nat.beq (getL oneK RS k) (wordK (takeK k RS) (takeK k RIS) w))
        (stepsPre RS RIS d1 (Nat.succ k)) = true := h1
    rw [andB_eq_true'] at h1'
    show andB (Nat.beq (getL oneK RS k) (wordK (takeK k RS) (takeK k RIS) w))
      (stepsK RS RIS (d1 ++ d2) (Nat.succ k)) = true
    rw [andB_eq_true']
    refine ⟨h1'.1, stepsK_append RS RIS d1 d2 (Nat.succ k) h1'.2 ?_⟩
    have e : Nat.succ k + d1.length = k + (w :: d1).length := by
      simp only [List.length_cons]
      omega
    rw [e]
    exact h2

theorem stepsK_cut (RS RIS : List Nat) (D : List (List Int)) (k c : Nat) (hc : c ≤ D.length)
    (h1 : stepsPre RS RIS (D.take c) k = true) (h2 : stepsK RS RIS (D.drop c) (k + c) = true) :
    stepsK RS RIS D k = true := by
  have hl : (D.take c).length = c := List.length_take_of_le hc
  have := stepsK_append RS RIS (D.take c) (D.drop c) k h1 (by rw [hl]; exact h2)
  rwa [List.take_append_drop] at this

end CFSG.KC.Co1B

end
