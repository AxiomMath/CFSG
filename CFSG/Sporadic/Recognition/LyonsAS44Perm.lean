module

public import Mathlib.Algebra.Group.Action.Defs

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

section Stabilizer

variable {Γ : Type*} {Ω : Type*} [Group Γ] [MulAction Γ Ω]

private theorem smul_injective_aux (g : Γ) : Function.Injective (fun x : Ω => g • x) :=
  fun x y h => by simpa using congrArg (fun z => g⁻¹ • z) h

private theorem stab_three_trans {a₀ c : Ω} {u : Γ} (hu : u • a₀ = c)
    (h3 : ∀ a b : Fin 3 → Ω, (∀ i, a i ≠ a₀) → (∀ i, b i ≠ a₀) → Function.Injective a →
      Function.Injective b → ∃ g : Γ, g • a₀ = a₀ ∧ ∀ i, g • a i = b i)
    (a b : Fin 3 → Ω) (ha : ∀ i, a i ≠ c) (hb : ∀ i, b i ≠ c) (hai : Function.Injective a)
    (hbi : Function.Injective b) : ∃ g : Γ, g • c = c ∧ ∀ i, g • a i = b i := by
  subst hu
  obtain ⟨g, hg, hgab⟩ := h3 (fun i => u⁻¹ • a i) (fun i => u⁻¹ • b i)
    (fun i h => ha i (inv_smul_eq_iff.mp h)) (fun i h => hb i (inv_smul_eq_iff.mp h))
    ((smul_injective_aux u⁻¹).comp hai) ((smul_injective_aux u⁻¹).comp hbi)
  refine ⟨u * g * u⁻¹, ?_, fun i => ?_⟩
  · rw [mul_smul, mul_smul, inv_smul_smul, hg]
  · rw [mul_smul, mul_smul, hgab i, smul_inv_smul]

private theorem stab_sharp {a₀ c : Ω} {u : Γ} (hu : u • a₀ = c)
    (hsharp : ∀ g : Γ, g • a₀ = a₀ → ∀ a : Fin 3 → Ω, (∀ i, a i ≠ a₀) → Function.Injective a →
      (∀ i, g • a i = a i) → g = 1)
    {g : Γ} (hg : g • c = c) (a : Fin 3 → Ω) (ha : ∀ i, a i ≠ c) (hai : Function.Injective a)
    (hfix : ∀ i, g • a i = a i) : g = 1 := by
  subst hu
  have h1 : u⁻¹ * g * u = 1 := by
    refine hsharp _ ?_ (fun i => u⁻¹ • a i) (fun i h => ha i (inv_smul_eq_iff.mp h))
      ((smul_injective_aux u⁻¹).comp hai) fun i => ?_
    · rw [mul_smul, mul_smul, hg, inv_smul_smul]
    · rw [mul_smul, mul_smul, smul_inv_smul, hfix i]
  have h2 := congrArg (fun x => u * x * u⁻¹) h1
  simpa [mul_assoc] using h2

end Stabilizer

private theorem succ_injective_aux : Function.Injective (Fin.succ : Fin 3 → Fin 4) :=
  fun _ _ h => Fin.succ_inj.mp h

theorem exists_unique_of_stabilizer_sharp {Γ : Type*} {Ω : Type*} [Group Γ] [MulAction Γ Ω]
    (a₀ : Ω) (htrans : ∀ b : Ω, ∃ g : Γ, g • a₀ = b)
    (h3 : ∀ a b : Fin 3 → Ω, (∀ i, a i ≠ a₀) → (∀ i, b i ≠ a₀) → Function.Injective a →
      Function.Injective b → ∃ g : Γ, g • a₀ = a₀ ∧ ∀ i, g • a i = b i)
    (hsharp : ∀ g : Γ, g • a₀ = a₀ → ∀ a : Fin 3 → Ω, (∀ i, a i ≠ a₀) → Function.Injective a →
      (∀ i, g • a i = a i) → g = 1) :
    ∀ a b : Fin 4 → Ω, Function.Injective a → Function.Injective b →
      ∃! g : Γ, ∀ i, g • a i = b i := by
  intro a b ha hb
  obtain ⟨ua, hua⟩ := htrans (a 0)
  obtain ⟨ub, hub⟩ := htrans (b 0)
  have hex : ∃ g : Γ, ∀ i, g • a i = b i := by
    have h10 : (ub * ua⁻¹) • a 0 = b 0 := by
      rw [mul_smul, inv_smul_eq_iff.mpr hua.symm, hub]
    have hne : ∀ i : Fin 3, (ub * ua⁻¹) • a i.succ ≠ b 0 := fun i h =>
      Fin.succ_ne_zero i (ha (smul_injective_aux (ub * ua⁻¹) (h.trans h10.symm)))
    have hne' : ∀ i : Fin 3, b i.succ ≠ b 0 := fun i h => Fin.succ_ne_zero i (hb h)
    obtain ⟨g₂, hg₂, hg₂'⟩ := stab_three_trans hub h3 (fun i => (ub * ua⁻¹) • a i.succ)
      (fun i => b i.succ) hne hne'
      ((smul_injective_aux (ub * ua⁻¹)).comp (ha.comp succ_injective_aux))
      (hb.comp succ_injective_aux)
    refine ⟨g₂ * (ub * ua⁻¹), fun i => ?_⟩
    induction i using Fin.cases with
    | zero => rw [mul_smul, h10, hg₂]
    | succ j => rw [mul_smul]; exact hg₂' j
  obtain ⟨g, hg⟩ := hex
  refine ⟨g, hg, fun g' hg' => ?_⟩
  have hfix : ∀ i, (g⁻¹ * g') • a i = a i := fun i => by
    rw [mul_smul, hg' i, inv_smul_eq_iff.mpr (hg i).symm]
  have h1 : g⁻¹ * g' = 1 :=
    stab_sharp hua hsharp (hfix 0) (fun i => a i.succ) (fun i h => Fin.succ_ne_zero i (ha h))
      (ha.comp succ_injective_aux) fun i => hfix i.succ
  simpa [mul_assoc] using congrArg (fun x => g * x) h1

end CFSG.Sporadic.Recognition.LyonsSims
