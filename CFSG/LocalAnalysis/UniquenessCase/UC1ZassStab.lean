module

public import CFSG.LocalAnalysis.UniquenessCase.UC1ZassFpf

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Zass

section Stab

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M] {G : Type*} [Group G]
  [Finite G]

@[expose] def stab (ρ : Representation K G M) (W : Submodule K M) : Subgroup G where
  carrier := {g | ∀ x ∈ W, ρ g x ∈ W}
  mul_mem' := by
    intro g h hg hh x hx
    rw [map_mul, Module.End.mul_apply]
    exact hg _ (hh x hx)
  one_mem' := by
    intro x hx
    simpa using hx
  inv_mem' := by
    intro g hg x hx
    have hpow : ∀ k : ℕ, ∀ x ∈ W, ρ (g ^ k) x ∈ W := by
      intro k
      induction k with
      | zero => intro x hx; simpa using hx
      | succ k ih =>
        intro x hx
        rw [pow_succ, map_mul, Module.End.mul_apply]
        exact ih _ (hg x hx)
    have h1 : g⁻¹ = g ^ (orderOf g - 1) := by
      refine inv_eq_of_mul_eq_one_right ?_
      rw [← pow_succ', Nat.sub_add_cancel (orderOf_pos g), pow_orderOf_eq_one]
    rw [h1]
    exact hpow _ x hx

theorem mem_stab {ρ : Representation K G M} {W : Submodule K M} {g : G} :
    g ∈ stab ρ W ↔ ∀ x ∈ W, ρ g x ∈ W :=
  Iff.rfl

end Stab

section Unique

variable {A : Type*} [CommSemiring A] {G : Type*} [Group G] {M : Type*} [AddCommGroup M]
  [Module A M] {ρ : Representation A G M}

theorem Fpf.eq_of_orderOf_eq_two [Nontrivial M] (hf : Fpf ρ) {g h : G} (hg : orderOf g = 2)
    (hh : orderOf h = 2) : g = h := by
  by_contra hne
  obtain ⟨v, hv⟩ := exists_ne (0 : M)
  have hgh : g * h⁻¹ ≠ 1 := fun h1 => hne (mul_inv_eq_one.mp h1)
  refine hv (hf (g * h⁻¹) hgh v ?_)
  have hinv : orderOf h⁻¹ = 2 := by rw [orderOf_inv, hh]
  rw [map_mul, Module.End.mul_apply, hf.apply_eq_neg hinv, map_neg, hf.apply_eq_neg hg, neg_neg]

end Unique

end CFSG.LocalAnalysis.UniquenessCase.UCK.Zass
