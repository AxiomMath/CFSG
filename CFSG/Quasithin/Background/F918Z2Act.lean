module

public import Mathlib.Data.Matrix.Basis

public section

namespace CFSG.Quasithin.SwapModel

open scoped Matrix

section Generic

variable {M N₁ N₂ : Type*} [AddCommGroup M] [Ring N₁] [Ring N₂]

theorem end_add_apply (f g : AddMonoid.End M) (m : M) : (f + g) m = f m + g m := rfl

theorem end_neg_apply (f : AddMonoid.End M) (m : M) : (-f) m = -f m := rfl

theorem eq_of_intertwine (act₁ : N₁ →+* AddMonoid.End M) (act₂ : N₂ →+* AddMonoid.End M)
    (hact₂ : Function.Injective act₂) (φ : M ≃+ M) {a : N₁} {b b' : N₂}
    (hb : ∀ m, φ (act₁ a m) = act₂ b (φ m)) (hb' : ∀ m, φ (act₁ a m) = act₂ b' (φ m)) :
    b = b' := by
  apply hact₂
  ext n
  obtain ⟨m, rfl⟩ := φ.surjective n
  rw [← hb, ← hb']

theorem exists_ringHom_of_intertwine (act₁ : N₁ →+* AddMonoid.End M)
    (act₂ : N₂ →+* AddMonoid.End M) (hact₂ : Function.Injective act₂) (φ : M ≃+ M)
    {S : Set N₁} (hS : AddSubgroup.closure S = ⊤)
    (hex : ∀ a ∈ S, ∃ b : N₂, ∀ m, φ (act₁ a m) = act₂ b (φ m)) :
    ∃ γ : N₁ →+* N₂, ∀ a m, φ (act₁ a m) = act₂ (γ a) (φ m) := by
  have huniq : ∀ a b b', (∀ m, φ (act₁ a m) = act₂ b (φ m)) →
      (∀ m, φ (act₁ a m) = act₂ b' (φ m)) → b = b' := fun a b b' hb hb' =>
    eq_of_intertwine act₁ act₂ hact₂ φ hb hb'
  let H : AddSubgroup N₁ :=
    { carrier := {a | ∃ b : N₂, ∀ m, φ (act₁ a m) = act₂ b (φ m)}
      zero_mem' := ⟨0, fun m => by simp⟩
      add_mem' := by
        rintro a a' ⟨b, hb⟩ ⟨b', hb'⟩
        exact ⟨b + b', fun m => by simp [end_add_apply, hb m, hb' m]⟩
      neg_mem' := by
        rintro a ⟨b, hb⟩
        exact ⟨-b, fun m => by simp [end_neg_apply, hb m]⟩ }
  have hH : ∀ a, ∃ b : N₂, ∀ m, φ (act₁ a m) = act₂ b (φ m) := by
    intro a
    have hle : AddSubgroup.closure S ≤ H := (AddSubgroup.closure_le H).mpr fun a ha => hex a ha
    rw [hS] at hle
    exact hle (AddSubgroup.mem_top a)
  choose γ hγ using hH
  refine ⟨{ toFun := γ
            map_one' := huniq 1 _ 1 (hγ 1) (fun m => by simp)
            map_mul' := fun a a' => huniq (a * a') _ _ (hγ _) (fun m => ?_)
            map_zero' := huniq 0 _ 0 (hγ 0) (fun m => by simp)
            map_add' := fun a a' => huniq (a + a') _ _ (hγ _) (fun m => ?_) }, hγ⟩
  · show φ (act₁ (a * a') m) = act₂ (γ a * γ a') (φ m)
    rw [map_mul, map_mul]
    show φ (act₁ a (act₁ a' m)) = act₂ (γ a) (act₂ (γ a') (φ m))
    rw [hγ a, hγ a']
  · show φ (act₁ (a + a') m) = act₂ (γ a + γ a') (φ m)
    rw [map_add, map_add, end_add_apply, end_add_apply, map_add, hγ a m, hγ a' m]

theorem injective_of_intertwine (act₁ : N₁ →+* AddMonoid.End M) (act₂ : N₂ →+* AddMonoid.End M)
    (hact₁ : Function.Injective act₁) (φ : M ≃+ M) {γ : N₁ →+* N₂}
    (hγ : ∀ a m, φ (act₁ a m) = act₂ (γ a) (φ m)) : Function.Injective γ := by
  intro a a' h
  apply hact₁
  ext m
  apply φ.injective
  rw [hγ, hγ, h]

end Generic

section Actions

variable (F : Type) [Field F] (d r : ℕ)

@[expose] def leftAct : Matrix (Fin d) (Fin d) F →+* AddMonoid.End (Matrix (Fin d) (Fin r) F) where
  toFun A := AddMonoidHom.mk' (fun M => A * M) (fun M N => Matrix.mul_add A M N)
  map_one' := AddMonoidHom.ext fun M => by
    show (1 : Matrix (Fin d) (Fin d) F) * M = M
    exact Matrix.one_mul M
  map_mul' A B := AddMonoidHom.ext fun M => by
    show (A * B) * M = A * (B * M)
    exact Matrix.mul_assoc A B M
  map_zero' := AddMonoidHom.ext fun M => by
    show (0 : Matrix (Fin d) (Fin d) F) * M = 0
    exact Matrix.zero_mul M
  map_add' A B := AddMonoidHom.ext fun M => by
    show (A + B) * M = A * M + B * M
    exact Matrix.add_mul A B M

@[expose] def rightAct : Matrix (Fin r) (Fin r) F →+* AddMonoid.End (Matrix (Fin d) (Fin r) F) where
  toFun B := AddMonoidHom.mk' (fun M => M * Bᵀ) (fun M N => Matrix.add_mul M N Bᵀ)
  map_one' := AddMonoidHom.ext fun M => by
    show M * (1 : Matrix (Fin r) (Fin r) F)ᵀ = M
    rw [Matrix.transpose_one, Matrix.mul_one]
  map_mul' A B := AddMonoidHom.ext fun M => by
    show M * (A * B)ᵀ = (M * Bᵀ) * Aᵀ
    rw [Matrix.transpose_mul, Matrix.mul_assoc]
  map_zero' := AddMonoidHom.ext fun M => by
    show M * (0 : Matrix (Fin r) (Fin r) F)ᵀ = 0
    rw [Matrix.transpose_zero, Matrix.mul_zero]
  map_add' A B := AddMonoidHom.ext fun M => by
    show M * (A + B)ᵀ = M * Aᵀ + M * Bᵀ
    rw [Matrix.transpose_add, Matrix.mul_add]

variable {F d r}

theorem leftAct_apply (A : Matrix (Fin d) (Fin d) F) (M : Matrix (Fin d) (Fin r) F) :
    leftAct F d r A M = A * M := rfl

theorem rightAct_apply (B : Matrix (Fin r) (Fin r) F) (M : Matrix (Fin d) (Fin r) F) :
    rightAct F d r B M = M * Bᵀ := rfl

theorem leftAct_injective (hr : 0 < r) : Function.Injective (leftAct F d r) := by
  intro A A' h
  ext i k
  have := congrArg (fun f : AddMonoid.End (Matrix (Fin d) (Fin r) F) =>
    f (Matrix.single k ⟨0, hr⟩ (1 : F)) i ⟨0, hr⟩) h
  simpa [leftAct_apply] using this

theorem rightAct_injective (hd : 0 < d) : Function.Injective (rightAct F d r) := by
  intro B B' h
  ext j k
  have := congrArg (fun f : AddMonoid.End (Matrix (Fin d) (Fin r) F) =>
    f (Matrix.single ⟨0, hd⟩ k (1 : F)) ⟨0, hd⟩ j) h
  simpa [rightAct_apply] using this

end Actions

end CFSG.Quasithin.SwapModel
