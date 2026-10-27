module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.Data.ZMod.Basic

public section

namespace CFSG.Sporadic.J4.QT

open Matrix

@[expose] def IndepF {ι : Type*} [Fintype ι] (v : ι → (Fin 112 → ZMod 2)) : Prop :=
  ∀ g : ι → ZMod 2, ∑ k, g k • v k = 0 → ∀ k, g k = 0

theorem IndepF.card_le {ι : Type*} [Fintype ι] {v : ι → (Fin 112 → ZMod 2)} (h : IndepF v) :
    Fintype.card ι ≤ 112 := by
  have hli : LinearIndependent (ZMod 2) v := Fintype.linearIndependent_iff.2 h
  have := hli.fintype_card_le_finrank
  simpa using this

theorem rank_obstruction {E G Z Zi : Matrix (Fin 112) (Fin 112) (ZMod 2)} (hZZi : Z * Zi = 1)
    (hconj : Z * G = E * Z) {a b : ℕ} (fs : Fin a → (Fin 112 → ZMod 2))
    (xs : Fin b → (Fin 112 → ZMod 2)) (hf : ∀ k, fs k ᵥ* E = fs k) (hfi : IndepF fs)
    (hxi : IndepF (fun k => xs k ᵥ* (G - 1))) (hab : 112 < a + b) : False := by
  classical
  have hinj : ∀ v : Fin 112 → ZMod 2, v ᵥ* Z = 0 → v = 0 := by
    intro v hv
    have h1 : (v ᵥ* Z) ᵥ* Zi = 0 := by rw [hv]; simp
    rwa [Matrix.vecMul_vecMul, hZZi, Matrix.vecMul_one] at h1
  have hg : ∀ k, (fs k ᵥ* Z) ᵥ* (G - 1) = 0 := by
    intro k
    rw [Matrix.vecMul_sub, Matrix.vecMul_one, Matrix.vecMul_vecMul, hconj,
      ← Matrix.vecMul_vecMul, hf k, sub_self]
  let v : Fin b ⊕ Fin a → (Fin 112 → ZMod 2) := Sum.elim xs (fun k => fs k ᵥ* Z)
  have hlin : IndepF v := by
    intro c hc
    rw [Fintype.sum_sum_type] at hc
    simp only [v, Sum.elim_inl, Sum.elim_inr] at hc
    have h1 := congrArg (Matrix.vecMulLinear (G - 1)) hc
    rw [map_add, map_sum, map_sum, map_zero] at h1
    simp only [map_smul, Matrix.vecMulLinear_apply, hg, smul_zero, Finset.sum_const_zero,
      add_zero] at h1
    have hb : ∀ k, c (Sum.inl k) = 0 := hxi _ h1
    have h2 : ∑ k, c (Sum.inr k) • (fs k ᵥ* Z) = 0 := by
      simp only [hb, zero_smul, Finset.sum_const_zero, zero_add] at hc
      exact hc
    have h3 : (∑ k, c (Sum.inr k) • fs k) ᵥ* Z = 0 := by
      have : ∑ k, c (Sum.inr k) • (fs k ᵥ* Z) = (∑ k, c (Sum.inr k) • fs k) ᵥ* Z := by
        rw [Matrix.sum_vecMul]
        simp [Matrix.smul_vecMul]
      rw [← this]; exact h2
    have h4 := hfi _ (hinj _ h3)
    intro i
    rcases i with i | i
    · exact hb i
    · exact h4 i
  have := hlin.card_le
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

theorem kernel_span {B Binv Φ : Matrix (Fin 112) (Fin 112) (ZMod 2)} {s : ℕ}
    (hBinv : Binv * B = 1)
    (hΨ : ∀ i j : Fin 112, (B * Φ) i j = if s ≤ i.val ∧ j.val = i.val - s then 1 else 0)
    (z : Fin 112 → ZMod 2) (hz : z ᵥ* Φ = 0) :
    ∃ c : Fin 112 → ZMod 2, z = c ᵥ* B ∧ ∀ i : Fin 112, s ≤ i.val → c i = 0 := by
  obtain ⟨c, hc⟩ : ∃ c : Fin 112 → ZMod 2, c = z ᵥ* Binv := ⟨_, rfl⟩
  have hzc : z = c ᵥ* B := by
    rw [hc, Matrix.vecMul_vecMul, hBinv, Matrix.vecMul_one]
  refine ⟨c, hzc, ?_⟩
  intro i hi
  have h1 : c ᵥ* (B * Φ) = 0 := by
    rw [← Matrix.vecMul_vecMul, ← hzc]; exact hz
  have hj : i.val - s < 112 := by omega
  have h2 := congrFun h1 ⟨i.val - s, hj⟩
  simp only [Matrix.vecMul, dotProduct, hΨ, Pi.zero_apply] at h2
  rw [Finset.sum_eq_single i] at h2
  · simpa [hi] using h2
  · intro i' _ hne
    by_cases h' : s ≤ i'.val ∧ i'.val - s = i.val - s
    · exfalso
      apply hne
      apply Fin.ext
      omega
    · have h'' : ¬ (s ≤ i'.val ∧ i.val - s = i'.val - s) := fun h => h' ⟨h.1, h.2.symm⟩
      simp [h'']
  · intro h; exact absurd (Finset.mem_univ i) h

end CFSG.Sporadic.J4.QT
