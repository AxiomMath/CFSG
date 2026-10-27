module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped Pointwise

theorem sec7ctr_exists_conj_of_sylow {H : Type*} [Group H] [Finite H] {P₁ P₂ : Subgroup H}
    {e m : ℕ} (hm : Odd m) (hH : Nat.card H = 2 ^ e * m) (h₁ : Nat.card ↥P₁ = 2 ^ e)
    (h₂ : Nat.card ↥P₂ = 2 ^ e) : ∃ g : H, ∀ x : H, x ∈ P₂ ↔ g⁻¹ * x * g ∈ P₁ := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm0 : m ≠ 0 := hm.pos.ne'
  have hm2 : ¬ 2 ∣ m := hm.not_two_dvd_nat
  have h2e : 2 ^ e ≠ 0 := by positivity
  have hfac : (Nat.card H).factorization 2 = e := by
    rw [hH, Nat.factorization_mul h2e hm0, Finsupp.add_apply,
      Nat.factorization_pow_self Nat.prime_two, Nat.factorization_eq_zero_of_not_dvd hm2,
      add_zero]
  have hc₁ : Nat.card ↥P₁ = 2 ^ (Nat.card H).factorization 2 := by
    rw [hfac]
    exact h₁
  have hc₂ : Nat.card ↥P₂ = 2 ^ (Nat.card H).factorization 2 := by
    rw [hfac]
    exact h₂
  obtain ⟨S₁, hS₁⟩ : ∃ S : Sylow 2 H, (S : Subgroup H) = P₁ :=
    ⟨Sylow.ofCard P₁ hc₁, rfl⟩
  obtain ⟨S₂, hS₂⟩ : ∃ S : Sylow 2 H, (S : Subgroup H) = P₂ :=
    ⟨Sylow.ofCard P₂ hc₂, rfl⟩
  have hfin : Finite (Sylow 2 H) :=
    Finite.of_injective (SetLike.coe : Sylow 2 H → Set H) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H S₁ S₂
  have hP : P₂ = MulAut.conj g • P₁ := by
    rw [← hS₁, ← hS₂, ← Sylow.coe_subgroup_smul, hg]
  refine ⟨g, fun x => ?_⟩
  rw [hP, Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply]

end CFSG.RankThree.GF2n.Stroth80
