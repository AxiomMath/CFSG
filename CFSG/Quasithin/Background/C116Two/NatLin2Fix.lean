module

public import CFSG.Quasithin.Background.C116Two.NatLin2Defs

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

private theorem fixSemi_exists_trace {F : Type} [Field F] (σ : F ≃+* F) (hσ1 : σ ≠ 1)
    (hσ2 : ∀ c, σ (σ c) = c) : ∃ d : F, d ≠ 0 ∧ σ d = -d ∧ ∃ l : F, l + σ l = 1 := by
  obtain ⟨a, ha⟩ : ∃ a : F, σ a ≠ a := by
    by_contra h
    push Not at h
    exact hσ1 (RingEquiv.ext fun a => h a)
  have hd0 : a - σ a ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
  have hσd : σ (a - σ a) = -(a - σ a) := by
    rw [map_sub, hσ2, neg_sub]
  refine ⟨a - σ a, hd0, hσd, a / (a - σ a), ?_⟩
  rw [map_div₀, hσd, div_neg, ← sub_eq_add_neg, ← sub_div, div_self hd0]

private theorem fixSemi_card_neg_eq {F M : Type} [Field F] [AddCommGroup M] [Module F M] [Finite M]
    (σ : F ≃+* F) (Ψ : M →+ M) (hΨ : ∀ (c : F) (x : M), Ψ (c • x) = σ c • Ψ x)
    {d : F} (hd0 : d ≠ 0) (hσd : σ d = -d) :
    Nat.card {x : M // Ψ x = -x} = Nat.card {x : M // Ψ x = x} := by
  apply le_antisymm
  · refine Nat.card_le_card_of_injective (fun y => ⟨d • y.1, ?_⟩) ?_
    · rw [hΨ, hσd, y.2]
      simp
    · intro y1 y2 h
      apply Subtype.ext
      apply smul_right_injective M hd0
      exact congrArg Subtype.val h
  · refine Nat.card_le_card_of_injective (fun c => ⟨d • c.1, ?_⟩) ?_
    · rw [hΨ, hσd, c.2, neg_smul]
    · intro c1 c2 h
      apply Subtype.ext
      apply smul_right_injective M hd0
      exact congrArg Subtype.val h

private theorem fixSemi_card_ker_add {M : Type} [AddCommGroup M] (Ψ : M →+ M) :
    Nat.card (AddMonoidHom.id M + Ψ).ker = Nat.card {x : M // Ψ x = -x} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [AddMonoidHom.mem_ker, AddMonoidHom.add_apply, AddMonoidHom.id_apply, add_comm,
    add_eq_zero_iff_eq_neg]

private theorem fixSemi_card_ker_sub {M : Type} [AddCommGroup M] (Ψ : M →+ M) :
    Nat.card (AddMonoidHom.ker (Ψ - AddMonoidHom.id M)) = Nat.card {x : M // Ψ x = x} := by
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro x
  rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]

private theorem fixSemi_range_add {F M : Type} [Field F] [AddCommGroup M] [Module F M]
    (σ : F ≃+* F) (Ψ : M →+ M) (hΨ : ∀ (c : F) (x : M), Ψ (c • x) = σ c • Ψ x)
    (hΨ2 : ∀ x, Ψ (Ψ x) = x) {l : F} (hl : l + σ l = 1) :
    (AddMonoidHom.id M + Ψ).range = AddMonoidHom.ker (Ψ - AddMonoidHom.id M) := by
  ext y
  rw [AddMonoidHom.mem_range, AddMonoidHom.mem_ker]
  constructor
  · rintro ⟨x, rfl⟩
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, AddMonoidHom.add_apply]
    rw [map_add, hΨ2]
    abel
  · intro hy
    simp only [AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero] at hy
    refine ⟨l • y, ?_⟩
    simp only [AddMonoidHom.add_apply, AddMonoidHom.id_apply]
    rw [hΨ, hy, ← add_smul, hl, one_smul]

private theorem card_sq_fix_of_semilinear {F M : Type} [Field F] [AddCommGroup M] [Module F M]
    [Finite M] (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : ∀ c, σ (σ c) = c)
    (Ψ : M →+ M) (hΨ : ∀ (c : F) (x : M), Ψ (c • x) = σ c • Ψ x) (hΨ2 : ∀ x, Ψ (Ψ x) = x) :
    Nat.card {x : M // Ψ x = x} ^ 2 = Nat.card M := by
  obtain ⟨d, hd0, hσd, l, hl⟩ := fixSemi_exists_trace σ hσ1 hσ2
  have h1 := AddSubgroup.card_ker_mul_card_range (AddMonoidHom.id M + Ψ)
  rw [fixSemi_range_add σ Ψ hΨ hΨ2 hl, fixSemi_card_ker_add, fixSemi_card_ker_sub,
    fixSemi_card_neg_eq σ Ψ hΨ hd0 hσd] at h1
  rw [sq, h1]

private def fixSemiRestrict {F : Type} [Field F] (φ : MulAut (Multiplicative (Fin 2 → F)))
    (ℓ : Submodule F (Fin 2 → F)) (hℓ : ∀ x ∈ ℓ, addMap φ x ∈ ℓ) : ℓ →+ ℓ where
  toFun x := ⟨addMap φ x.1, hℓ x.1 x.2⟩
  map_zero' := Subtype.ext (by simp [addMap])
  map_add' x y := Subtype.ext (addMap_add φ x.1 y.1)

private theorem fixSemiRestrict_semi {F : Type} [Field F] {σ : F ≃+* F}
    {φ : MulAut (Multiplicative (Fin 2 → F))} (hφ : IsSemilinear σ φ)
    (ℓ : Submodule F (Fin 2 → F)) (hℓ : ∀ x ∈ ℓ, addMap φ x ∈ ℓ) (c : F) (x : ℓ) :
    fixSemiRestrict φ ℓ hℓ (c • x) = σ c • fixSemiRestrict φ ℓ hℓ x :=
  Subtype.ext (hφ c x.1)

private theorem fixSemiRestrict_sq {F : Type} [Field F] (φ : MulAut (Multiplicative (Fin 2 → F)))
    (hφ2 : φ * φ = 1) (ℓ : Submodule F (Fin 2 → F)) (hℓ : ∀ x ∈ ℓ, addMap φ x ∈ ℓ) (x : ℓ) :
    fixSemiRestrict φ ℓ hℓ (fixSemiRestrict φ ℓ hℓ x) = x := by
  apply Subtype.ext
  have h : addMap (φ * φ) x.1 = addMap 1 x.1 := congrArg (fun g => addMap g x.1) hφ2
  rw [addMap_mul, addMap_one] at h
  exact h

theorem card_fixed_semilinear_involution {F : Type} [Field F] [Fintype F]
    (σ : F ≃+* F) (hσ1 : σ ≠ 1) (hσ2 : ∀ c, σ (σ c) = c)
    (φ : MulAut (Multiplicative (Fin 2 → F))) (hφ : IsSemilinear σ φ) (hφ2 : φ * φ = 1)
    (ℓ : Submodule F (Fin 2 → F)) (hℓ : ∀ x ∈ ℓ, addMap φ x ∈ ℓ) :
    Nat.card {x : Fin 2 → F // x ∈ ℓ ∧ addMap φ x = x} ^ 2 = Nat.card ℓ := by
  have key := card_sq_fix_of_semilinear σ hσ1 hσ2 (fixSemiRestrict φ ℓ hℓ)
    (fixSemiRestrict_semi hφ ℓ hℓ) (fixSemiRestrict_sq φ hφ2 ℓ hℓ)
  have hequiv : Nat.card {x : Fin 2 → F // x ∈ ℓ ∧ addMap φ x = x} =
      Nat.card {x : ℓ // fixSemiRestrict φ ℓ hℓ x = x} := by
    apply Nat.card_congr
    exact
      { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
        invFun := fun y => ⟨y.1.1, y.1.2, congrArg Subtype.val y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hequiv]
  exact key

end CFSG.Quasithin.C116Two
