module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Monster.B.E6.StdF4Radical

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem exists_eigen_of_involution {W : Submodule ℂ V} (hW : W ≠ ⊥) {S : Module.End ℂ V}
    (hS : S * S = 1) (hSW : ∀ w ∈ W, S w ∈ W) :
    ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ ∃ w ∈ W, w ≠ 0 ∧ S w = ε • w := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hW
  have hSS : S (S w) = w := by
    rw [← Module.End.mul_apply, hS, Module.End.one_apply]
  by_cases h : S w + w = 0
  · refine ⟨-1, Or.inr rfl, w, hw, hw0, ?_⟩
    rw [neg_one_smul]
    exact eq_neg_of_add_eq_zero_left h
  · refine ⟨1, Or.inl rfl, S w + w, W.add_mem (hSW w hw) hw, h, ?_⟩
    rw [one_smul, map_add, hSS, add_comm]

@[expose] def eigenIn (W : Submodule ℂ V) (S : Module.End ℂ V) (ε : ℂ) : Submodule ℂ V :=
  W ⊓ Module.End.eigenspace S ε

theorem mem_eigenIn {W : Submodule ℂ V} {S : Module.End ℂ V} {ε : ℂ} {w : V} :
    w ∈ eigenIn W S ε ↔ w ∈ W ∧ S w = ε • w := by
  rw [eigenIn, Submodule.mem_inf, Module.End.mem_eigenspace_iff]

theorem exists_common_eigen : ∀ (Ts : List (Module.End ℂ V)), (∀ T ∈ Ts, T * T = 1) →
    (∀ T ∈ Ts, ∀ T' ∈ Ts, T * T' = T' * T) → ∀ (W : Submodule ℂ V), W ≠ ⊥ →
    (∀ T ∈ Ts, ∀ w ∈ W, T w ∈ W) → ∃ w ∈ W, w ≠ 0 ∧ ∀ T ∈ Ts, T w = w ∨ T w = -w
  | [], _, _, W, hW, _ => by
    obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff W).1 hW
    exact ⟨w, hw, hw0, fun T hT => absurd hT List.not_mem_nil⟩
  | T :: Ts, hinv, hcomm, W, hW, hTW => by
    obtain ⟨ε, hε, w₀, hw₀, hw₀0, hTw₀⟩ :=
      exists_eigen_of_involution hW (hinv T (List.mem_cons_self ..)) (hTW T (List.mem_cons_self ..))
    have hW' : eigenIn W T ε ≠ ⊥ :=
      (Submodule.ne_bot_iff _).2 ⟨w₀, mem_eigenIn.2 ⟨hw₀, hTw₀⟩, hw₀0⟩
    have hinv' : ∀ T' ∈ Ts, T' * T' = 1 := fun T' h => hinv T' (List.mem_cons_of_mem _ h)
    have hcomm' : ∀ T₁ ∈ Ts, ∀ T₂ ∈ Ts, T₁ * T₂ = T₂ * T₁ := fun T₁ h₁ T₂ h₂ =>
      hcomm T₁ (List.mem_cons_of_mem _ h₁) T₂ (List.mem_cons_of_mem _ h₂)
    have hTW' : ∀ T' ∈ Ts, ∀ w ∈ eigenIn W T ε, T' w ∈ eigenIn W T ε := by
      intro T' hT' w hw
      rw [mem_eigenIn] at hw ⊢
      refine ⟨hTW T' (List.mem_cons_of_mem _ hT') w hw.1, ?_⟩
      have hc := hcomm T (List.mem_cons_self ..) T' (List.mem_cons_of_mem _ hT')
      rw [← Module.End.mul_apply, hc, Module.End.mul_apply, hw.2, map_smul]
    obtain ⟨w, hw, hw0, hTs⟩ := exists_common_eigen Ts hinv' hcomm' _ hW' hTW'
    rw [mem_eigenIn] at hw
    refine ⟨w, hw.1, hw0, fun T' hT' => ?_⟩
    rcases List.mem_cons.1 hT' with rfl | hT'
    · rcases hε with rfl | rfl
      · left
        rw [hw.2, one_smul]
      · right
        rw [hw.2, neg_one_smul]
    · exact hTs T' hT'

end CFSG.Monster.B.E6.StdF4Radical
