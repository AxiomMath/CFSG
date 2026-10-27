module

public import CFSG.RankThree.PartOne.SRC.KernelPlusOne

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.SL2MinimalFaithful Subgroup


theorem rank_four_of_cover_SL2_three_one {p : ℕ} [Fact p.Prime] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] [CharP F₁ p] [CharP F₂ p] (hF₁ : Nat.card F₁ = p ^ 3)
    (hF₂ : Nat.card F₂ = p) (hp2 : p ≠ 2) {W : Type} [Group W] [Finite W]
    (ρ : W →* SpecialLinearGroup (Fin 2) F₁ × SpecialLinearGroup (Fin 2) F₂)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  by_cases hK : ρ.ker = ⊥
  ·
    have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).mp hK
    let e : W ≃* SpecialLinearGroup (Fin 2) F₁ × SpecialLinearGroup (Fin 2) F₂ :=
      MulEquiv.ofBijective ρ ⟨hinj, hρ⟩
    let τ : Multiplicative F₁ × Multiplicative F₂ →*
        SpecialLinearGroup (Fin 2) F₁ × SpecialLinearGroup (Fin 2) F₂ :=
      unipotentHom.prodMap unipotentHom
    have hτinj : Function.Injective τ := by
      intro x y h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext (unipotentHom_injective h1) (unipotentHom_injective h2)
    let τ' : Multiplicative F₁ × Multiplicative F₂ →* W := e.symm.toMonoidHom.comp τ
    have hτ'inj : Function.Injective τ' := e.symm.injective.comp hτinj
    have hpow : ∀ a : Multiplicative F₁ × Multiplicative F₂, a ^ p = 1 := by
      intro a
      refine Prod.ext ?_ ?_
      · show a.1 ^ p = 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
      · show a.2 ^ p = 1
        apply Multiplicative.toAdd.injective
        rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
    refine ⟨τ'.range, 4, le_rfl, isElementaryAbelian_range τ' hpow, ?_⟩
    rw [← Nat.card_congr (MonoidHom.ofInjective hτ'inj).toEquiv, Nat.card_prod,
      Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd, hF₁, hF₂]
    ring
  ·
    let A : Subgroup W := ((MonoidHom.snd _ _).comp ρ).ker
    let ρ₁ : A →* SpecialLinearGroup (Fin 2) F₁ := (MonoidHom.fst _ _).comp (ρ.comp A.subtype)
    have hρ₁s : Function.Surjective ρ₁ := by
      intro a
      obtain ⟨w, hw⟩ := hρ (a, 1)
      exact ⟨⟨w, by simp [A, hw]⟩, by simp [ρ₁, hw]⟩
    have hρ₁k : ∀ x : A, x ∈ ρ₁.ker → (x : W) ∈ ρ.ker := by
      intro x hx
      have hx1 : (ρ (x : W)).1 = 1 := hx
      have hx2 : (ρ (x : W)).2 = 1 := x.2
      exact Prod.ext hx1 hx2
    have hker₁ : IsPGroup p ρ₁.ker := by
      intro x
      have hx1 : ρ ((x : A) : W) = 1 := hρ₁k x x.2
      obtain ⟨k, hk⟩ := hker ⟨((x : A) : W), hx1⟩
      exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : W)) hk))⟩
    have hK₁ : ρ₁.ker ≠ ⊥ := by
      intro h
      apply hK
      rw [eq_bot_iff]
      intro w hw
      have hwA : w ∈ A := by
        have : (ρ w).2 = 1 := by rw [MonoidHom.mem_ker.mp hw]; rfl
        exact this
      have : (⟨w, hwA⟩ : A) ∈ ρ₁.ker := by
        change (ρ w).1 = 1
        rw [MonoidHom.mem_ker.mp hw]; rfl
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    obtain ⟨E, k, hk, hE, hc⟩ := exists_elementaryAbelian_of_nontrivial_kernel_SL2 hF₁ hp2
      (le_refl 3) ρ₁ hρ₁s hker₁ hK₁
    refine ⟨E.map A.subtype, k, hk, isElementaryAbelian_map' A.subtype hE, ?_⟩
    rw [Subgroup.card_map_of_injective A.subtype_injective, hc]

end CFSG.RankThree.PartOne.SRC
