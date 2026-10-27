module

public import CFSG.LocalAnalysis.StandardType.GGForkCellsDefs

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section NullPos

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

theorem ggAttachNullPos_false_of_cert (C : Matrix Λ Λ ℤ) (k : Λ) (y : Option Λ → ℤ)
    (h1 : ∀ i, 0 ≤ ∑ j, ggAttachCartan C k i j * y j)
    (h2 : ∃ i, 0 < ∑ j, ggAttachCartan C k i j * y j) : ¬ GGAttachNullPos C k := by
  rintro ⟨n, hpos, hnull⟩
  have hT0 : ∑ i, y i * (∑ j, (n j : ℤ) * ggAttachCartan C k j i) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hnull i, mul_zero]
  have hT : (∑ i, y i * (∑ j, (n j : ℤ) * ggAttachCartan C k j i))
      = ∑ j, (n j : ℤ) * (∑ i, ggAttachCartan C k j i * y i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  have hpos_sum : 0 < ∑ j, (n j : ℤ) * (∑ i, ggAttachCartan C k j i * y i) := by
    apply Finset.sum_pos'
    · intro j _
      exact mul_nonneg (by exact_mod_cast Nat.zero_le (n j)) (h1 j)
    · obtain ⟨i0, hi0⟩ := h2
      exact ⟨i0, Finset.mem_univ _, mul_pos (by exact_mod_cast hpos i0) hi0⟩
  rw [hT] at hT0
  linarith

theorem ggAttachCartan_submatrix_optionCongr {Λ' : Type} [DecidableEq Λ'] {C : Matrix Λ Λ ℤ}
    {C' : Matrix Λ' Λ' ℤ} (e : Λ' ≃ Λ) (hC : ∀ i j, C (e i) (e j) = C' i j) {k : Λ} {k' : Λ'}
    (hk : k = e k') :
    (ggAttachCartan C k).submatrix (Equiv.optionCongr e) (Equiv.optionCongr e) =
      ggAttachCartan C' k' := by
  subst hk
  ext i j
  rcases i with _ | i <;> rcases j with _ | j <;>
    simp [Matrix.submatrix_apply, Equiv.optionCongr_apply, Equiv.apply_eq_iff_eq, hC]

theorem GGAttachNullPos.of_equiv {Λ' : Type} [Fintype Λ'] [DecidableEq Λ'] {C : Matrix Λ Λ ℤ}
    {C' : Matrix Λ' Λ' ℤ} (e : Λ' ≃ Λ) (hC : ∀ i j, C (e i) (e j) = C' i j) {k : Λ} {k' : Λ'}
    (hk : k = e k') (h : GGAttachNullPos C k) : GGAttachNullPos C' k' := by
  obtain ⟨n, hpos, hnull⟩ := h
  refine ⟨fun j => n (Equiv.optionCongr e j), fun j => hpos _, fun i => ?_⟩
  have hsub : ∀ j i : Option Λ', ggAttachCartan C' k' j i =
      ggAttachCartan C k (Equiv.optionCongr e j) (Equiv.optionCongr e i) := by
    intro j i
    have hji := congr_fun (congr_fun (ggAttachCartan_submatrix_optionCongr e hC hk) j) i
    simpa only [Matrix.submatrix_apply] using hji.symm
  simp only [hsub]
  rw [Equiv.sum_comp (Equiv.optionCongr e)
      (fun j : Option Λ => (n j : ℤ) * ggAttachCartan C k j (Equiv.optionCongr e i))]
  exact hnull (Equiv.optionCongr e i)

end NullPos

structure GGForkMatrix {Λ : Type*} [DecidableEq Λ] (C : Matrix Λ Λ ℤ) (b c : Λ) : Prop where
  ne : b ≠ c
  diag : ∀ i, C i i = 2
  bL : ∀ i, i ≠ b → C b i = if i = c then -1 else 0
  bR : ∀ i, i ≠ b → C i b = if i = c then -1 else 0

theorem GGForkPairing.toMatrix {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    {Λ : Type*} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V} {ha : V} {αa : Module.Dual (ZMod p) V}
    (hF : GGForkPairing C b c h α ha αa) : GGForkMatrix C b c :=
  ⟨hF.ne, hF.diag, hF.bL, hF.bR⟩

@[expose] def GGLeafPos {m : ℕ} (C₀ : Matrix (Fin m) (Fin m) ℤ) (i k : Fin m) : Prop :=
  i ≠ k ∧ (∀ j, j ≠ i → C₀ i j = if j = k then -1 else 0) ∧
    (∀ j, j ≠ i → C₀ j i = if j = k then -1 else 0)

instance {m : ℕ} (C₀ : Matrix (Fin m) (Fin m) ℤ) (i k : Fin m) : Decidable (GGLeafPos C₀ i k) := by
  unfold GGLeafPos
  infer_instance

theorem GGForkMatrix.leafPos {Λ : Type} [DecidableEq Λ] {C : Matrix Λ Λ ℤ} {b c : Λ}
    (hF : GGForkMatrix C b c) {m : ℕ} {C₀ : Matrix (Fin m) (Fin m) ℤ} (e : Fin m ≃ Λ)
    (hC : ∀ i j, C (e i) (e j) = C₀ i j) : GGLeafPos C₀ (e.symm b) (e.symm c) := by
  refine ⟨fun h => hF.ne (e.symm.injective h), ?_, ?_⟩
  · intro j hj
    have hjb : e j ≠ b := fun h => hj (by rw [← e.symm_apply_apply j, h])
    rw [← hC (e.symm b) j, e.apply_symm_apply, hF.bL (e j) hjb]
    exact if_congr (Equiv.eq_symm_apply e).symm rfl rfl
  · intro j hj
    have hjb : e j ≠ b := fun h => hj (by rw [← e.symm_apply_apply j, h])
    rw [← hC j (e.symm b), e.apply_symm_apply, hF.bR (e j) hjb]
    exact if_congr (Equiv.eq_symm_apply e).symm rfl rfl

@[expose] def GGForkAffineCell {Λ : Type} (C : Matrix Λ Λ ℤ) (b : Λ) : Prop :=
  (∃ e : Fin 6 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 6 i j) ∧ b = e 1) ∨
  (∃ e : Fin 7 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 7 i j) ∧ b = e 0) ∨
  (∃ e : Fin 8 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.E 8 i j) ∧ b = e 7) ∨
  (∃ e : Fin 8 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.D 8 i j) ∧ b = e 7) ∨
  (∃ e : Fin 4 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∧ b = e 0) ∨
  (∃ e : Fin 4 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ i j) ∧ b = e 3) ∨
  (∃ e : Fin 4 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i) ∧ b = e 0) ∨
  (∃ e : Fin 4 ≃ Λ, (∀ i j, C (e i) (e j) = CartanMatrix.F₄ j i) ∧ b = e 3)

end CFSG.StandardType
