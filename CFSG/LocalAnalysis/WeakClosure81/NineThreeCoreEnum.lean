module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeW0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nine3_exists_enum (hc : Nine3Choice V T A K S X p g x)
    (h35 : Nat.card ↥(nineDelta V S) = 3 ∨ Nat.card ↥(nineDelta V S) = 5) :
    ∃ (n : ℕ) (B : Fin (n + 1) → Subgroup G) (σ : Equiv.Perm (Fin (n + 1))),
      (n = 2 ∨ n = 4) ∧ Nat.card ↥(nineOmegaIn V K S) = n ∧ B 0 = V ∧ B 1 = A ∧
      Function.Injective B ∧ (∀ k, B k ∈ nineDelta V S) ∧ (∀ D ∈ nineDelta V S, ∃ k, B k = D) ∧
      (∀ k, k ≠ 0 → B k ∈ nineOmegaIn V K S) ∧ (∀ k, conjSubgroup (B k) g = B (σ k)) ∧
      σ 0 = 1 ∧ σ 1 = 0 := by
  classical
  obtain ⟨m, hΩcard, hΔcard⟩ := hc.core.card_nineOmegaIn
  have h2m : 2 ^ m = 2 ∨ 2 ^ m = 4 := by
    rcases h35 with h | h <;> omega
  let n := 2 ^ m
  have hn : n = 2 ∨ n = 4 := h2m
  have hDcard : Nat.card ↥(nineDelta V S) = n + 1 := hΔcard
  have hΩn : Nat.card ↥(nineOmegaIn V K S) = n := hΩcard
  let v : ↥(nineDelta V S) := ⟨V, hc.core.V_mem_nineDelta⟩
  let a : ↥(nineDelta V S) := ⟨A, hc.core.A_mem_nineDelta⟩
  have hva : v ≠ a := by
    intro h
    exact hc.core.ne (congrArg Subtype.val h).symm
  let e₀ : Fin (n + 1) ≃ ↥(nineDelta V S) := (Finite.equivFinOfCardEq hDcard).symm
  let τ₁ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 (e₀.symm v)
  let e₁ : Fin (n + 1) ≃ ↥(nineDelta V S) := τ₁.trans e₀
  have he₁0 : e₁ 0 = v := by
    simp [e₁, τ₁]
  have h01 : (0 : Fin (n + 1)) ≠ 1 := by
    haveI : NeZero n := ⟨by omega⟩
    exact Fin.zero_ne_one' (n := n)
  have hne : e₁.symm a ≠ 0 := by
    intro h
    have h1 : e₁ 0 = a := by rw [← Equiv.apply_symm_apply e₁ a, h]
    exact hva (he₁0.symm.trans h1)
  let τ₂ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 1 (e₁.symm a)
  let e₂ : Fin (n + 1) ≃ ↥(nineDelta V S) := τ₂.trans e₁
  have he₂1 : e₂ 1 = a := by
    simp [e₂, τ₂]
  have hτ₂0 : τ₂ 0 = 0 := Equiv.swap_apply_of_ne_of_ne h01 hne.symm
  have he₂0 : e₂ 0 = v := by
    simp [e₂, hτ₂0, he₁0]
  let π : Equiv.Perm ↥(nineDelta V S) :=
    { toFun := fun d => ⟨conjSubgroup (d : Subgroup G) g, hc.conj_mem_nineDelta d.2⟩
      invFun := fun d => ⟨conjSubgroup (d : Subgroup G) g⁻¹, hc.conj_inv_mem_nineDelta d.2⟩
      left_inv := fun d => by
        apply Subtype.ext
        simp only
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, mul_inv_cancel,
          CFSG.Quasithin.conjSubgroup_one]
      right_inv := fun d => by
        apply Subtype.ext
        simp only
        rw [CFSG.Quasithin.conjSubgroup_conjSubgroup, inv_mul_cancel,
          CFSG.Quasithin.conjSubgroup_one] }
  let σ : Equiv.Perm (Fin (n + 1)) := (e₂.trans π).trans e₂.symm
  let B : Fin (n + 1) → Subgroup G := fun k => (e₂ k : Subgroup G)
  have hB0 : B 0 = V := by simp [B, he₂0, v]
  have hB1 : B 1 = A := by simp [B, he₂1, a]
  have hBinj : Function.Injective B := fun i j h => e₂.injective (Subtype.ext h)
  have hBmem : ∀ k, B k ∈ nineDelta V S := fun k => (e₂ k).2
  have hBsurj : ∀ D ∈ nineDelta V S, ∃ k, B k = D := by
    intro D hD
    exact ⟨e₂.symm ⟨D, hD⟩, by simp [B]⟩
  have hBΩ : ∀ k, k ≠ 0 → B k ∈ nineOmegaIn V K S := by
    intro k hk
    rcases (hc.core.mem_nineDelta_iff.mp (hBmem k)) with hV | hΩ
    · exact absurd (hBinj (hV.trans hB0.symm)) hk
    · exact hΩ
  have hBσ : ∀ k, conjSubgroup (B k) g = B (σ k) := by
    intro k
    show conjSubgroup (e₂ k : Subgroup G) g = (e₂ (σ k) : Subgroup G)
    have hσ : σ k = e₂.symm (π (e₂ k)) := rfl
    rw [hσ, Equiv.apply_symm_apply]
    rfl
  have hσ0 : σ 0 = 1 := hBinj (by rw [← hBσ 0, hB0, hc.V_g, hB1])
  have hσ1 : σ 1 = 0 := hBinj (by rw [← hBσ 1, hB1, hc.A_g, hB0])
  exact ⟨n, B, σ, hn, hΩn, hB0, hB1, hBinj, hBmem, hBsurj, hBΩ, hBσ, hσ0, hσ1⟩

end CFSG.LocalAnalysis.WeakClosure81
