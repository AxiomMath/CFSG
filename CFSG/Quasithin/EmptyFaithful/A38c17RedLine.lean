module

public import CFSG.Quasithin.EmptyFaithful.A38c17Defs
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.Quasithin.A38c17

open Matrix CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [Finite K] [CharP K p]

omit [Fact p.Prime] [Field K] [Finite K] [CharP K p] in
theorem su3_card_eq_pow_one_sq (hK : Nat.card K = p ^ 2) : Nat.card K = (p ^ 1) ^ 2 := by
  rwa [pow_one]

theorem su3_preserves_form (hK : Nat.card K = p ^ 2) {A : GL (Fin 3) K}
    (hA : A ∈ StatedSU 3 p K) (u v : Fin 3 → K) :
    (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3).β ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ u)
      ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
        (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3).β u v :=
  statedSU_preserves (su3_card_eq_pow_one_sq hK) (by rwa [pow_one]) u v

omit [Fact p.Prime] [Finite K] [CharP K p] in
theorem su3_eigenvector_of_line (M : Subgroup ↥(StatedSU 3 p K)) {W : Submodule K (Fin 3 → K)}
    (hW1 : Module.finrank K W = 1)
    (hW : ∀ g ∈ M, ∀ w ∈ W, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ g ∈ M, ∃ c : K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.mp hW1
  refine ⟨v.1, fun h => hv0 (Subtype.ext h), fun g hg => ?_⟩
  obtain ⟨c, hc⟩ := hv ⟨((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v.1, hW g hg v.1 v.2⟩
  exact ⟨c, congrArg Subtype.val hc.symm⟩

theorem su3_perp_invariant (hK : Nat.card K = p ^ 2) (M : Subgroup ↥(StatedSU 3 p K))
    {W : Submodule K (Fin 3 → K)}
    (hW : ∀ g ∈ M, ∀ w ∈ W, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W) :
    ∀ g ∈ M, ∀ x ∈ (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3).perp W,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈
        (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3).perp W := by
  intro g hg x hx w hw
  have h1 := hW g⁻¹ (M.inv_mem hg) w hw
  have h2 := su3_preserves_form hK g.2
    (((g⁻¹ : ↥(StatedSU 3 p K)) : GL (Fin 3) K) *ᵥ w) x
  have h3 : ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((g⁻¹ : ↥(StatedSU 3 p K)) : GL (Fin 3) K) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
    simp
  rw [h3] at h2
  rw [h2]
  exact hx _ h1

theorem su3_exists_invariant_line (hK : Nat.card K = p ^ 2)
    (M : Subgroup ↥(StatedSU 3 p K)) (hred : ¬ IsIrreducibleSU3 M) :
    ∃ v : Fin 3 → K, v ≠ 0 ∧ ∀ g ∈ M, ∃ c : K,
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v = c • v := by
  unfold IsIrreducibleSU3 at hred
  push Not at hred
  obtain ⟨W, hW, hbot, htop⟩ := hred
  have hlt : Module.finrank K W < 3 := by
    have := Submodule.finrank_lt htop
    simpa using this
  have hne : Module.finrank K W ≠ 0 := fun h0 => hbot (Submodule.finrank_eq_zero.mp h0)
  have h12 : Module.finrank K W = 1 ∨ Module.finrank K W = 2 := by omega
  rcases h12 with h1 | h2
  · exact su3_eigenvector_of_line M h1 hW
  · refine su3_eigenvector_of_line M
      (W := (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3).perp W) ?_ (su3_perp_invariant hK M hW)
    have := (unitaryForm p 1 (su3_card_eq_pow_one_sq hK) 3).finrank_perp W
    rw [Module.finrank_fin_fun, h2] at this
    omega

end CFSG.Quasithin.A38c17
