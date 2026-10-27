module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

public section

namespace CFSG.Quasithin.H13

section Commutant

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

noncomputable def ob5E (b : Module.Basis (Fin 2) F W) : W →ₗ[F] W :=
  b.constr F ![b 0, b 1 + b 0]

noncomputable def ob5Dg (b : Module.Basis (Fin 2) F W) (μ : F) : W →ₗ[F] W :=
  b.constr F ![μ • b 0, μ⁻¹ • b 1]

noncomputable def ob5Wr (b : Module.Basis (Fin 2) F W) : W →ₗ[F] W :=
  b.constr F ![b 1, -b 0]

theorem ob5_pair_indep (b : Module.Basis (Fin 2) F W) (s t : F) (h : s • b 0 + t • b 1 = 0) :
    s = 0 ∧ t = 0 := by
  have hli : LinearIndependent F ![b 0, b 1] := by
    convert b.linearIndependent using 1
    ext i
    fin_cases i <;> rfl
  exact (LinearIndependent.pair_iff.mp hli) s t h

theorem ob5_pair_eq (b : Module.Basis (Fin 2) F W) {s t s' t' : F}
    (h : s • b 0 + t • b 1 = s' • b 0 + t' • b 1) : s = s' ∧ t = t' := by
  have h' : (s - s') • b 0 + (t - t') • b 1 =
      (s • b 0 + t • b 1) - (s' • b 0 + t' • b 1) := by
    simp only [sub_smul]
    abel
  rw [h, sub_self] at h'
  obtain ⟨h1, h2⟩ := ob5_pair_indep b _ _ h'
  exact ⟨sub_eq_zero.mp h1, sub_eq_zero.mp h2⟩

theorem ob5_exists_pair (b : Module.Basis (Fin 2) F W) (v : W) :
    ∃ c0 c1 : F, v = c0 • b 0 + c1 • b 1 := by
  have := b.sum_repr v
  rw [Fin.sum_univ_two] at this
  exact ⟨_, _, this.symm⟩

theorem ob5E_zero (b : Module.Basis (Fin 2) F W) : ob5E b (b 0) = b 0 := by
  simp [ob5E, Module.Basis.constr_basis]

theorem ob5E_apply (b : Module.Basis (Fin 2) F W) (c0 c1 : F) :
    ob5E b (c0 • b 0 + c1 • b 1) = (c0 + c1) • b 0 + c1 • b 1 := by
  have h1 : ob5E b (b 1) = b 1 + b 0 := by simp [ob5E, Module.Basis.constr_basis]
  rw [map_add, map_smul, map_smul, ob5E_zero, h1]
  simp only [smul_add, add_smul]
  abel

theorem ob5Dg_apply (b : Module.Basis (Fin 2) F W) (μ : F) (c0 c1 : F) :
    ob5Dg b μ (c0 • b 0 + c1 • b 1) = (c0 * μ) • b 0 + (c1 * μ⁻¹) • b 1 := by
  have h0 : ob5Dg b μ (b 0) = μ • b 0 := by simp [ob5Dg, Module.Basis.constr_basis]
  have h1 : ob5Dg b μ (b 1) = μ⁻¹ • b 1 := by simp [ob5Dg, Module.Basis.constr_basis]
  rw [map_add, map_smul, map_smul, h0, h1, smul_smul, smul_smul]

theorem ob5Dg_zero (b : Module.Basis (Fin 2) F W) (μ : F) : ob5Dg b μ (b 0) = μ • b 0 := by
  simp [ob5Dg, Module.Basis.constr_basis]

theorem ob5Dg_one (b : Module.Basis (Fin 2) F W) (μ : F) : ob5Dg b μ (b 1) = μ⁻¹ • b 1 := by
  simp [ob5Dg, Module.Basis.constr_basis]

theorem ob5Wr_zero (b : Module.Basis (Fin 2) F W) : ob5Wr b (b 0) = b 1 := by
  simp [ob5Wr, Module.Basis.constr_basis]

theorem ob5Wr_apply (b : Module.Basis (Fin 2) F W) (c0 c1 : F) :
    ob5Wr b (c0 • b 0 + c1 • b 1) = (-c1) • b 0 + c0 • b 1 := by
  have h1 : ob5Wr b (b 1) = -b 0 := by simp [ob5Wr, Module.Basis.constr_basis]
  rw [map_add, map_smul, map_smul, ob5Wr_zero, h1]
  simp only [smul_neg, neg_smul]
  abel

theorem ob5_commutant_scalar (b : Module.Basis (Fin 2) F W) (φ : W →+ W)
    (he : ∀ w, φ (ob5E b w) = ob5E b (φ w))
    (hd : ∀ μ : F, μ ≠ 0 → ∀ w, φ (ob5Dg b μ w) = ob5Dg b μ (φ w))
    (hw : ∀ w, φ (ob5Wr b w) = ob5Wr b (φ w)) :
    ∃ α : F, ∀ w, φ w = α • w := by
  obtain ⟨c0, c1, hc⟩ := ob5_exists_pair b (φ (b 0))
  have hE : φ (b 0) = ob5E b (φ (b 0)) := by
    have := he (b 0)
    rwa [ob5E_zero] at this
  have hc1 : c1 = 0 := by
    have h1 : c0 • b 0 + c1 • b 1 = (c0 + c1) • b 0 + c1 • b 1 := by
      calc c0 • b 0 + c1 • b 1 = φ (b 0) := hc.symm
        _ = ob5E b (φ (b 0)) := hE
        _ = ob5E b (c0 • b 0 + c1 • b 1) := by rw [← hc]
        _ = (c0 + c1) • b 0 + c1 • b 1 := ob5E_apply b c0 c1
    have h2 := (ob5_pair_eq b h1).1
    have h3 : c0 + c1 = c0 + 0 := by rw [add_zero]; exact h2.symm
    exact add_left_cancel h3
  have hφb0 : φ (b 0) = c0 • b 0 := by rw [hc, hc1, zero_smul, add_zero]
  have hφb1 : φ (b 1) = c0 • b 1 := by
    have h1 := hw (b 0)
    rw [ob5Wr_zero, hφb0] at h1
    rw [h1]
    have := ob5Wr_apply b c0 0
    simpa using this
  have hA : ∀ μ : F, φ (μ • b 0) = (c0 * μ) • b 0 := by
    intro μ
    by_cases hμ : μ = 0
    · subst hμ
      simp
    · have h1 := hd μ hμ (b 0)
      rw [ob5Dg_zero, hφb0] at h1
      rw [h1]
      have := ob5Dg_apply b μ c0 0
      simpa using this
  have hB : ∀ ν : F, φ (ν • b 1) = (c0 * ν) • b 1 := by
    intro ν
    by_cases hν : ν = 0
    · subst hν
      simp
    · have h1 := hd ν⁻¹ (inv_ne_zero hν) (b 1)
      rw [ob5Dg_one, hφb1, inv_inv] at h1
      rw [h1]
      have := ob5Dg_apply b ν⁻¹ 0 c0
      simpa [inv_inv, mul_comm] using this
  refine ⟨c0, fun w => ?_⟩
  obtain ⟨u0, u1, rfl⟩ := ob5_exists_pair b w
  rw [map_add, hA, hB, smul_add, smul_smul, smul_smul]

end Commutant

end CFSG.Quasithin.H13
