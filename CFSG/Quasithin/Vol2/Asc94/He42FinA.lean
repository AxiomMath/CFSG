module

public import CFSG.Quasithin.Vol2.Asc94.He42Fin

public section

namespace CFSG.Quasithin.A94.He42Fin

open Equiv

private theorem he42fa_mem_stab0_iff (g : Perm (Fin 5)) :
    g ∈ Stab0 ↔ g ∈ alternatingGroup (Fin 5) ∧ g 0 = 0 := by
  simp only [Stab0, Subgroup.mem_inf, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]

private theorem he42fa_orderOf_eq_three_iff (c : Perm (Fin 5)) :
    orderOf c = 3 ↔ c ^ 3 = 1 ∧ c ≠ 1 := by
  constructor
  · intro h
    refine ⟨by rw [← h]; exact pow_orderOf_eq_one c, ?_⟩
    intro h1
    subst h1
    rw [orderOf_one] at h
    exact absurd h (by decide)
  · rintro ⟨h3, h1⟩
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact orderOf_eq_prime h3 h1

private theorem he42fa_inverting_finite :
    ∀ c : Perm (Fin 5), c 0 = 0 → c ^ 3 = 1 → c ≠ 1 → Equiv.Perm.sign c = 1 →
      ∃ τ : Perm (Fin 5), Equiv.Perm.sign τ = 1 ∧ τ * τ = 1 ∧ τ * c * τ⁻¹ = c⁻¹ ∧ τ 0 ≠ 0 := by
  decide +kernel

private theorem he42fa_centralizer_finite :
    ∀ c : Perm (Fin 5), c ^ 3 = 1 → c ≠ 1 → Equiv.Perm.sign c = 1 →
      ∀ τ : Perm (Fin 5), Equiv.Perm.sign τ = 1 → τ * c = c * τ → τ = 1 ∨ τ = c ∨ τ = c * c := by
  decide +kernel

private theorem he42fa_stab0_transitive_finite :
    ∀ i j : Fin 5, i ≠ 0 → j ≠ 0 →
      ∃ σ : Perm (Fin 5), Equiv.Perm.sign σ = 1 ∧ σ 0 = 0 ∧ σ i = j := by
  decide +kernel

private theorem he42fa_exists_stab0_apply (i j : Fin 5) (hi : i ≠ 0) (hj : j ≠ 0) :
    ∃ σ ∈ Stab0, σ i = j := by
  obtain ⟨σ, h1, h2, h3⟩ := he42fa_stab0_transitive_finite i j hi hj
  exact ⟨σ, (he42fa_mem_stab0_iff σ).mpr ⟨Equiv.Perm.mem_alternatingGroup.mpr h1, h2⟩, h3⟩

theorem exists_inverting_involution (c : Perm (Fin 5)) (hc : c ∈ alternatingGroup (Fin 5))
    (hc0 : c 0 = 0) (hc3 : orderOf c = 3) :
    ∃ τ : Perm (Fin 5), τ ∈ alternatingGroup (Fin 5) ∧ τ * τ = 1 ∧ τ * c * τ⁻¹ = c⁻¹ ∧
      τ 0 ≠ 0 := by
  obtain ⟨h3, h1⟩ := (he42fa_orderOf_eq_three_iff c).mp hc3
  obtain ⟨τ, hτ, hτ2, hinv, hτ0⟩ :=
    he42fa_inverting_finite c hc0 h3 h1 (Equiv.Perm.mem_alternatingGroup.mp hc)
  exact ⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hτ, hτ2, hinv, hτ0⟩

theorem mem_zpowers_of_commute_order_three (c τ : Perm (Fin 5))
    (hc : c ∈ alternatingGroup (Fin 5)) (hτ : τ ∈ alternatingGroup (Fin 5)) (h3 : orderOf c = 3)
    (hcomm : τ * c = c * τ) : τ ∈ Subgroup.zpowers c := by
  obtain ⟨h3', h1⟩ := (he42fa_orderOf_eq_three_iff c).mp h3
  rcases he42fa_centralizer_finite c h3' h1 (Equiv.Perm.mem_alternatingGroup.mp hc) τ
      (Equiv.Perm.mem_alternatingGroup.mp hτ) hcomm with h | h | h
  · subst h
    exact Subgroup.one_mem _
  · subst h
    exact Subgroup.mem_zpowers _
  · subst h
    exact mul_mem (Subgroup.mem_zpowers _) (Subgroup.mem_zpowers _)

theorem stab0_maximal (X : Subgroup (Perm (Fin 5))) (hX : X ≤ alternatingGroup (Fin 5))
    (hS : Stab0 ≤ X) : X = Stab0 ∨ X = alternatingGroup (Fin 5) := by
  by_cases h : X ≤ Stab0
  · exact Or.inl (le_antisymm h hS)
  · right
    have hex : ∃ σ ∈ X, σ ∉ Stab0 := by
      by_contra hcon
      exact h (fun x hx => by_contra fun hx' => hcon ⟨x, hx, hx'⟩)
    obtain ⟨σ, hσX, hσS⟩ := hex
    have hσA : σ ∈ alternatingGroup (Fin 5) := hX hσX
    have hσ0 : σ 0 ≠ 0 := fun h0 => hσS ((he42fa_mem_stab0_iff σ).mpr ⟨hσA, h0⟩)
    refine le_antisymm hX fun τ hτA => ?_
    by_cases hτ0 : τ 0 = 0
    · exact hS ((he42fa_mem_stab0_iff τ).mpr ⟨hτA, hτ0⟩)
    · obtain ⟨a, haS, ha⟩ := he42fa_exists_stab0_apply (σ 0) (τ 0) hσ0 hτ0
      obtain ⟨haA, -⟩ := (he42fa_mem_stab0_iff a).mp haS
      have hbS : σ⁻¹ * a⁻¹ * τ ∈ Stab0 := by
        refine (he42fa_mem_stab0_iff _).mpr ⟨?_, ?_⟩
        · exact mul_mem (mul_mem (inv_mem hσA) (inv_mem haA)) hτA
        · simp [Equiv.Perm.mul_apply, Equiv.Perm.inv_def, ← ha]
      have key : a * σ * (σ⁻¹ * a⁻¹ * τ) ∈ X :=
        mul_mem (mul_mem (hS haS) hσX) (hS hbS)
      rwa [show a * σ * (σ⁻¹ * a⁻¹ * τ) = τ by group] at key

end CFSG.Quasithin.A94.He42Fin
