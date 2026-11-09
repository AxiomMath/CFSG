module

public import Certificates.Data.Kernel.B45M12.Four

public section

namespace CFSG.KC.B45M12

@[expose] noncomputable def smulK (s₀ s₁ : Bool) (c : ℕ × ℕ) : ℕ × ℕ :=
  Bool.rec (motive := fun _ => ℕ × ℕ)
    (Bool.rec (motive := fun _ => ℕ × ℕ) (0, 0) (c.2, Nat.xor c.1 c.2) s₁)
    (Bool.rec (motive := fun _ => ℕ × ℕ) c (Nat.xor c.1 c.2, c.1) s₁) s₀

@[expose] noncomputable def actF4G (cs : List (ℕ × ℕ)) : ℕ → ℕ → ℕ × ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ → ℕ × ℕ) (fun _ _ => (0, 0))
    (fun c _ r a b =>
      (fun s t => (Nat.xor s.1 t.1, Nat.xor s.2 t.2))
        (smulK (Nat.beq (Nat.land a 1) 1) (Nat.beq (Nat.land b 1) 1) c)
        (r (Nat.shiftRight a 1) (Nat.shiftRight b 1))) cs

@[expose] noncomputable def actF4K (cs : List (ℕ × ℕ)) (x : ℕ × ℕ) : ℕ × ℕ := actF4G cs x.1 x.2

theorem smulP_eq_smulK (s₀ s₁ : Bool) (c : ℕ × ℕ) : smulP s₀ s₁ c = smulK s₀ s₁ c := by
  cases s₀ <;> cases s₁ <;> rfl

theorem actF4_eq_actF4G : ∀ (cs : List (ℕ × ℕ)) (x : ℕ × ℕ), actF4 cs x = actF4G cs x.1 x.2
  | [], _ => rfl
  | c :: cs, x => by
    have e : actF4G (c :: cs) x.1 x.2 =
        xorP (smulK (Nat.beq (x.1 &&& 1) 1) (Nat.beq (x.2 &&& 1) 1) c)
          (actF4G cs (x.1 >>> 1) (x.2 >>> 1)) := rfl
    rw [e, actF4, actF4_eq_actF4G cs, smulP_eq_smulK, Nat.and_one_is_mod, Nat.and_one_is_mod,
      Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow, pow_one]

theorem actF4_eq_actF4K : actF4 = actF4K :=
  funext fun cs => funext fun x => actF4_eq_actF4G cs x

end CFSG.KC.B45M12

end
