module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv

theorem exists_mem_inf_alternatingGroup_smul_ne {Δ : Type*} [Fintype Δ] [DecidableEq Δ]
    {K : Subgroup (Perm Δ)} (hK : MulAction.IsPretransitive ↥K Δ) (h3 : 3 ≤ Nat.card Δ)
    (α : Δ) : ∃ k ∈ K ⊓ alternatingGroup Δ, k α ≠ α := by
  by_contra hcon
  have hle : (alternatingGroup Δ).subgroupOf K ≤ MulAction.stabilizer ↥K α := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    rw [MulAction.mem_stabilizer_iff]
    by_contra hne
    exact hcon ⟨(k : Perm Δ), Subgroup.mem_inf.2 ⟨k.2, hk⟩, hne⟩
  have h1 : (MulAction.stabilizer ↥K α).index ∣ ((alternatingGroup Δ).subgroupOf K).index :=
    Subgroup.index_dvd_of_le hle
  rw [MulAction.index_stabilizer_of_transitive] at h1
  have h2 : ((alternatingGroup Δ).subgroupOf K).index ≤ 2 := by
    have h' : (alternatingGroup Δ).relIndex K = Nat.card (Subgroup.map Equiv.Perm.sign K) :=
      Subgroup.relIndex_ker K (Equiv.Perm.sign : Perm Δ →* ℤˣ)
    have h4 : Nat.card (Subgroup.map (Equiv.Perm.sign : Perm Δ →* ℤˣ) K) ≤ Nat.card ℤˣ :=
      Subgroup.card_le_card_group _
    have h5 : Nat.card ℤˣ = 2 := by
      rw [Nat.card_eq_fintype_card]
      rfl
    calc ((alternatingGroup Δ).subgroupOf K).index = (alternatingGroup Δ).relIndex K := rfl
      _ = Nat.card (Subgroup.map Equiv.Perm.sign K) := h'
      _ ≤ Nat.card ℤˣ := h4
      _ = 2 := h5
  have h6 : 0 < ((alternatingGroup Δ).subgroupOf K).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have := Nat.le_of_dvd h6 h1
  omega

end CFSG.LocalAnalysis.WeakClosure81
