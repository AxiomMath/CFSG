module

public import Certificates.Data.Kernel.B45M12.Mask

public section

namespace CFSG.KC.B45M12

open CFSG.Quasithin.H.Mathieu (actM)
open CFSG.Quasithin.B45Mat (mulM idM)

@[expose] noncomputable def actMK (cs : List ℕ) : ℕ → ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun _ => 0)
    (fun c _ r m => Nat.xor (cond (Nat.beq (Nat.land m 1) 1) c 0) (r (Nat.shiftRight m 1))) cs

@[expose] noncomputable def mapK (f : ℕ → ℕ) (l : List ℕ) : List ℕ :=
  List.rec (motive := fun _ => List ℕ) [] (fun x _ r => f x :: r) l

@[expose] noncomputable def mulMK (A B : List ℕ) : List ℕ := mapK (actMK A) B

theorem actM_eq_actMK : ∀ (cs : List ℕ) (m : ℕ), actM cs m = actMK cs m
  | [], _ => rfl
  | c :: cs, m => by
    have e : actMK (c :: cs) m = (cond (Nat.beq (m &&& 1) 1) c 0) ^^^ actMK cs (m >>> 1) := rfl
    rw [e, actM, Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow, pow_one, actM_eq_actMK cs (m / 2)]
    rcases Nat.mod_two_eq_zero_or_one m with h | h <;> rw [h] <;> rfl

theorem mulM_eq_mulMK (A : List ℕ) : ∀ B : List ℕ, mulM A B = mulMK A B
  | [] => rfl
  | b :: B => by
    have e : mulMK A (b :: B) = actMK A b :: mulMK A B := rfl
    rw [e, ← mulM_eq_mulMK A B, ← actM_eq_actMK]
    rfl

@[expose] noncomputable def subStepK (m : ℕ) (B P T KB : List ℕ) : Bool :=
  eqL (mulMK P KB) T && eqM m KB (mulMK B T)

@[expose] noncomputable def subKK (m d : ℕ) (B P : List ℕ) (KT : List (List ℕ × List ℕ)) : Bool :=
  Nat.ble B.length d && Nat.ble P.length m && eqM d (mulMK P B) (idM d) &&
    KT.all fun p => Nat.ble p.1.length m && subStepK m B P p.2 (mulMK p.1 B)

theorem subK_eq_subKK (m d : ℕ) (B P : List ℕ) (KT : List (List ℕ × List ℕ)) :
    subK m d B P KT = subKK m d B P KT := by
  simp only [subK, subKK, subStep, subStepK, mulM_eq_mulMK]

end CFSG.KC.B45M12

end
