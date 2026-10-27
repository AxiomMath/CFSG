module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13

namespace A5Syl

open scoped Pointwise

@[expose] def V₀ : Subgroup (alternatingGroup (Fin 5)) where
  carrier := {x | x.1 4 = 4 ∧ x * x = 1}
  mul_mem' {a b} ha hb := by
    revert a b
    decide +kernel
  one_mem' := by decide +kernel
  inv_mem' {a} ha := by
    revert a
    decide +kernel

instance : DecidablePred (· ∈ V₀) := fun x =>
  inferInstanceAs (Decidable (x.1 4 = 4 ∧ x * x = 1))

theorem card_V₀ : Nat.card V₀ = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

@[expose] def c₀ : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide +kernel)⟩

theorem c₀_mem_normalizer : c₀ ∈ Subgroup.normalizer (V₀ : Set (alternatingGroup (Fin 5))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  revert x
  decide +kernel

theorem orderOf_c₀ : orderOf c₀ = 3 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)

theorem card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

theorem exists_orderOf_three (P : Subgroup (alternatingGroup (Fin 5))) (hP : Nat.card P = 4) :
    ∃ g ∈ Subgroup.normalizer (P : Set (alternatingGroup (Fin 5))), orderOf g = 3 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfac : (Nat.card (alternatingGroup (Fin 5))).factorization 2 = 2 := by
    rw [card_alt5]
    decide +kernel
  let S₀ : Sylow 2 (alternatingGroup (Fin 5)) := Sylow.ofCard V₀ (by rw [card_V₀, hfac]; norm_num)
  let S : Sylow 2 (alternatingGroup (Fin 5)) := Sylow.ofCard P (by rw [hP, hfac]; norm_num)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (alternatingGroup (Fin 5)) S₀ S
  have hord : orderOf (g * c₀ * g⁻¹) = 3 := by
    have h1 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c₀
    rw [orderOf_c₀] at h1
    rw [← h1]
    rfl
  refine ⟨g * c₀ * g⁻¹, ?_, hord⟩
  have hPmem : ∀ x, x ∈ P ↔ g⁻¹ * x * g ∈ V₀ := by
    intro x
    have h1 : (P : Subgroup (alternatingGroup (Fin 5))) =
        MulAut.conj g • (V₀ : Subgroup (alternatingGroup (Fin 5))) := by
      have h2 := congrArg (fun Q : Sylow 2 (alternatingGroup (Fin 5)) =>
        (Q : Subgroup (alternatingGroup (Fin 5)))) hg
      simp only [S, S₀, Sylow.coe_ofCard, Sylow.coe_subgroup_smul] at h2
      exact h2.symm
    rw [h1, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    show (MulAut.conj g)⁻¹ x ∈ V₀ ↔ _
    rw [MulAut.conj_inv_apply]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hPmem, hPmem]
  have h1 := Subgroup.mem_normalizer_iff.mp c₀_mem_normalizer (g⁻¹ * x * g)
  have e : g⁻¹ * (g * c₀ * g⁻¹ * x * (g * c₀ * g⁻¹)⁻¹) * g = c₀ * (g⁻¹ * x * g) * c₀⁻¹ := by
    group
  rw [e]
  exact h1

end A5Syl

end CFSG.Quasithin.H13
