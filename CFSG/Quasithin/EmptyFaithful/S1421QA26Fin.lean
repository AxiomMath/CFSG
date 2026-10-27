module

public import CFSG.Quasithin.Background.G6Natural
public import CFSG.GH74.GLS.IVK.A7.Core
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.QA26

open Equiv Equiv.Perm CFSG.GH74.GLS.IVK

@[expose] def vecS (s : List (Fin 7)) : G6.PermMod 7 :=
  Multiplicative.ofAdd (fun i => if i ∈ s then (1 : ZMod 2) else 0)

@[expose] def vA : G6.PermMod 7 := vecS [0, 1, 2, 3]

@[expose] def vB : G6.PermMod 7 := vecS [4, 5]

@[expose] def vC : G6.PermMod 7 := vecS [0, 1, 2, 3, 4, 5]

@[expose] def IsEven7 (w : G6.PermMod 7) : Prop := ∑ i, Multiplicative.toAdd w i = 0

instance (w : G6.PermMod 7) : Decidable (IsEven7 w) := by unfold IsEven7; infer_instance

theorem permAct_mul_apply (σ τ : Perm (Fin 7)) (w : G6.PermMod 7) :
    G6.permAct 7 (σ * τ) w = G6.permAct 7 σ (G6.permAct 7 τ w) := by
  rw [map_mul]; rfl

theorem permAct_one_apply (w : G6.PermMod 7) : G6.permAct 7 1 w = w := by
  rw [map_one]; rfl

theorem permAct_inv_apply (g : Perm (Fin 7)) (w : G6.PermMod 7) :
    G6.permAct 7 g⁻¹ (G6.permAct 7 g w) = w := by
  rw [← permAct_mul_apply, inv_mul_cancel, permAct_one_apply]

theorem permAct_apply_inv (g : Perm (Fin 7)) (w : G6.PermMod 7) :
    G6.permAct 7 g (G6.permAct 7 g⁻¹ w) = w := by
  rw [← permAct_mul_apply, mul_inv_cancel, permAct_one_apply]

theorem vA_even : IsEven7 vA := by decide

theorem vA_ne_one : vA ≠ 1 := by decide

set_option maxRecDepth 100000 in
theorem P0_fix : ∀ σ ∈ A7.P0list, G6.permAct 7 σ vA = vA ∧ G6.permAct 7 σ vB = vB ∧
    G6.permAct 7 σ vC = vC := by
  intro σ hσ
  rw [A7.mem_P0list_iff] at hσ
  rcases hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

set_option maxRecDepth 100000 in
theorem P0_fixed_space_gen : ∀ w : G6.PermMod 7, IsEven7 w →
    G6.permAct 7 (A7.r * A7.f0) w = w → G6.permAct 7 (A7.s * A7.f0) w = w →
    w = 1 ∨ w = vA ∨ w = vB ∨ w = vC := by
  decide +kernel

theorem P0_fixed_space : ∀ w : G6.PermMod 7, IsEven7 w →
    (∀ σ ∈ A7.P0list, G6.permAct 7 σ w = w) → w = 1 ∨ w = vA ∨ w = vB ∨ w = vC := by
  intro w hw h
  refine P0_fixed_space_gen w hw (h _ ?_) (h _ ?_)
  · exact A7.mem_P0list_iff.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact A7.mem_P0list_iff.2 (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))

set_option maxRecDepth 100000 in
theorem no_five_fix_aux : ∀ σ : Perm (Fin 7), (∀ i : Fin 7, (i.val < 4) = ((σ⁻¹ i).val < 4)) →
    σ ^ 5 = 1 → σ ≠ 1 → False := by
  decide +kernel

theorem no_five_fix_vA (σ : Perm (Fin 7)) (h5 : σ ^ 5 = 1) (h1 : σ ≠ 1) :
    G6.permAct 7 σ vA ≠ vA := by
  intro h
  refine no_five_fix_aux σ (fun i => ?_) h5 h1
  have hi := congrArg (fun x : G6.PermMod 7 => Multiplicative.toAdd x i) h
  simp only [G6.permAct_apply, vA, vecS, toAdd_ofAdd] at hi
  have key : ∀ j : Fin 7, ((if j ∈ [0, 1, 2, 3] then (1 : ZMod 2) else 0) = 1) ↔ j.val < 4 := by
    decide
  apply propext
  rw [← key i, ← key (σ⁻¹ i), hi]

@[expose] def cB : Perm (Fin 7) := c[0, 1, 2, 3, 6]

@[expose] def cC : Perm (Fin 7) := c[0, 1, 2, 3, 4]

set_option maxRecDepth 100000 in
theorem cB_facts : cB ^ 5 = 1 ∧ cB ≠ 1 ∧ sign cB = 1 ∧ G6.permAct 7 cB vB = vB := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cC_facts : cC ^ 5 = 1 ∧ cC ≠ 1 ∧ sign cC = 1 ∧ G6.permAct 7 cC vC = vC := by
  decide +kernel

theorem exists_fixed_four {P : Subgroup (Perm (Fin 7))} (hPA : P ≤ alternatingGroup (Fin 7))
    (hP8 : Nat.card P = 8) :
    ∃ w : G6.PermMod 7, IsEven7 w ∧ w ≠ 1 ∧ (∀ σ ∈ P, G6.permAct 7 σ w = w) ∧
      (∀ σ : Perm (Fin 7), σ ^ 5 = 1 → σ ≠ 1 → G6.permAct 7 σ w ≠ w) ∧
      ∀ w' : G6.PermMod 7, IsEven7 w' → w' ≠ 1 → w' ≠ w → (∀ σ ∈ P, G6.permAct 7 σ w' = w') →
        ∃ σ ∈ alternatingGroup (Fin 7), σ ^ 5 = 1 ∧ σ ≠ 1 ∧ G6.permAct 7 σ w' = w' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP2 : IsPGroup 2 P := IsPGroup.of_card (n := 3) (by rw [hP8]; norm_num)
  obtain ⟨T, hPT⟩ := hP2.exists_le_sylow
  obtain ⟨g, hg⟩ := A7.exists_conj_T0 T
  have hmap := A7.T_inf_A7_eq_map hg
  have hcardT : Nat.card ↥((T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7)) = 8 := by
    rw [hmap, Subgroup.card_map_of_injective (MulAut.conj g).injective, A7.card_T0_inf_A7]
  have hPle : P ≤ (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) := le_inf hPT hPA
  have hPeq : P = (T : Subgroup (Perm (Fin 7))) ⊓ alternatingGroup (Fin 7) :=
    Subgroup.eq_of_le_of_card_ge hPle (by rw [hcardT, hP8])
  have hmem : ∀ x : Perm (Fin 7), x ∈ P ↔ g⁻¹ * x * g ∈ A7.P0list := by
    intro x
    rw [hPeq]
    exact A7.mem_T_inf_A7 hg x
  have hconj : ∀ (σ : Perm (Fin 7)) (w : G6.PermMod 7), G6.permAct 7 σ (G6.permAct 7 g w) =
      G6.permAct 7 g (G6.permAct 7 (g⁻¹ * σ * g) w) := by
    intro σ w
    rw [← permAct_mul_apply, ← permAct_mul_apply]
    congr 2
    group
  refine ⟨G6.permAct 7 g vA, G6.permAct_mem_coreMod g vA_even, ?_, ?_, ?_, ?_⟩
  · intro h
    apply vA_ne_one
    have := congrArg (G6.permAct 7 g⁻¹) h
    rw [permAct_inv_apply] at this
    rw [this]
    rw [map_one]
  · intro σ hσ
    rw [hconj]
    congr 1
    exact (P0_fix _ ((hmem σ).1 hσ)).1
  · intro σ h5 h1 h
    apply no_five_fix_vA (g⁻¹ * σ * g)
    · have : (g⁻¹ * σ * g) ^ 5 = g⁻¹ * σ ^ 5 * g := by
        have := conj_pow (a := g⁻¹) (b := σ) (i := 5)
        simpa using this
      rw [this, h5]
      group
    · intro hc
      apply h1
      have : σ = g * (g⁻¹ * σ * g) * g⁻¹ := by group
      rw [this, hc]
      group
    · have := congrArg (G6.permAct 7 g⁻¹) h
      rw [hconj, permAct_inv_apply, permAct_inv_apply] at this
      exact this
  · intro w' hw'e hw'1 hw'ne hfix
    set w₀ := G6.permAct 7 g⁻¹ w' with hw₀
    have hw₀e : IsEven7 w₀ := G6.permAct_mem_coreMod g⁻¹ hw'e
    have hw₀1 : w₀ ≠ 1 := by
      intro h
      apply hw'1
      have := congrArg (G6.permAct 7 g) h
      rw [hw₀, permAct_apply_inv, map_one] at this
      exact this
    have hw₀A : w₀ ≠ vA := by
      intro h
      apply hw'ne
      have := congrArg (G6.permAct 7 g) h
      rw [hw₀, permAct_apply_inv] at this
      exact this
    have hw₀fix : ∀ σ ∈ A7.P0list, G6.permAct 7 σ w₀ = w₀ := by
      intro σ₀ hσ₀
      have hσP : g * σ₀ * g⁻¹ ∈ P := by
        rw [hmem]
        have : g⁻¹ * (g * σ₀ * g⁻¹) * g = σ₀ := by group
        rw [this]
        exact hσ₀
      have h1 := hfix _ hσP
      have h2 : G6.permAct 7 (g * σ₀ * g⁻¹) w' = G6.permAct 7 g (G6.permAct 7 σ₀ w₀) := by
        rw [hw₀, ← permAct_mul_apply, ← permAct_mul_apply]
      rw [h2] at h1
      have h3 := congrArg (G6.permAct 7 g⁻¹) h1
      rw [permAct_inv_apply] at h3
      rw [h3, hw₀]
    rcases P0_fixed_space w₀ hw₀e hw₀fix with h | h | h | h
    · exact absurd h hw₀1
    · exact absurd h hw₀A
    · obtain ⟨h5, h1, hs, hf⟩ := cB_facts
      refine ⟨g * cB * g⁻¹, ?_, ?_, ?_, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_inv, hs, mul_one, Int.units_mul_self]
      · have := conj_pow (a := g) (b := cB) (i := 5)
        rw [this, h5]
        group
      · intro hc
        apply h1
        have : cB = g⁻¹ * (g * cB * g⁻¹) * g := by group
        rw [this, hc]
        group
      · have h2 : G6.permAct 7 (g * cB * g⁻¹) w' = G6.permAct 7 g (G6.permAct 7 cB w₀) := by
          rw [hw₀, ← permAct_mul_apply, ← permAct_mul_apply]
        rw [h2, h, hf, ← h, hw₀, permAct_apply_inv]
    · obtain ⟨h5, h1, hs, hf⟩ := cC_facts
      refine ⟨g * cC * g⁻¹, ?_, ?_, ?_, ?_⟩
      · rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_mul,
        Equiv.Perm.sign_inv, hs, mul_one, Int.units_mul_self]
      · have := conj_pow (a := g) (b := cC) (i := 5)
        rw [this, h5]
        group
      · intro hc
        apply h1
        have : cC = g⁻¹ * (g * cC * g⁻¹) * g := by group
        rw [this, hc]
        group
      · have h2 : G6.permAct 7 (g * cC * g⁻¹) w' = G6.permAct 7 g (G6.permAct 7 cC w₀) := by
          rw [hw₀, ← permAct_mul_apply, ← permAct_mul_apply]
        rw [h2, h, hf, ← h, hw₀, permAct_apply_inv]

end CFSG.Quasithin.QA26
