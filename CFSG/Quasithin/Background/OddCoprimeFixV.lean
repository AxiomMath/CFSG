module

public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

theorem commV_inf_fixV_eq_bot_of_odd_card (hV : ∀ v : V, v ^ 2 = 1) (P : Subgroup (MulAut V))
    (hodd : Odd (Nat.card P)) : commV P ⊓ fixV P = ⊥ := by
  classical
  have : Finite P := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero (by
    rintro h; rw [h] at hodd; exact absurd hodd (by decide))).ne'
  have : Fintype P := Fintype.ofFinite P
  let N : V →* V :=
    { toFun := fun v => ∏ σ : P, (σ : MulAut V) v
      map_one' := by simp
      map_mul' := fun v w => by
        simp only [map_mul]
        exact Finset.prod_mul_distrib }
  have hNinv : ∀ (τ : P) (v : V), N ((τ : MulAut V) v) = N v := by
    intro τ v
    show ∏ σ : P, (σ : MulAut V) ((τ : MulAut V) v) = ∏ σ : P, (σ : MulAut V) v
    exact Fintype.prod_equiv (Equiv.mulRight τ) _ _ (fun σ => by simp)
  have hNker : commV P ≤ N.ker := by
    rw [commV, Subgroup.closure_le]
    rintro _ ⟨σ, hσ, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
    have := hNinv ⟨σ, hσ⟩ v
    simp only at this
    rw [this, mul_inv_cancel]
  rw [eq_bot_iff]
  intro c ⟨hc1, hc2⟩
  have hNc : N c = c ^ Nat.card P := by
    show ∏ σ : P, (σ : MulAut V) c = c ^ Nat.card P
    have : ∀ σ : P, (σ : MulAut V) c = c := fun σ => hc2 σ σ.2
    simp only [this, Finset.prod_const, Finset.card_univ, Nat.card_eq_fintype_card]
  have h1 : N c = 1 := hNker hc1
  obtain ⟨m, hm⟩ := hodd
  have hc : c ^ Nat.card P = c := by
    rw [hm, pow_succ, pow_mul, hV c, one_pow, one_mul]
  exact Subgroup.mem_bot.2 (by rw [← hc, ← hNc, h1])

end CFSG.Quasithin
