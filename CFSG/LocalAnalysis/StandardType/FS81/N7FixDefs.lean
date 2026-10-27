module

public import CFSG.LocalAnalysis.StandardType.FS81.N7Split
public import CFSG.LocalAnalysis.StandardType.FS81.SpMatAlg
import CFSG.LocalAnalysis.StandardType.FS81.OddCoreOrthRows

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def e0 : Fin 8 → ZMod 3 := Pi.single 0 1

@[expose] def sgn (S : Finset (Fin 8)) : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  Matrix.diagonal fun i => if i ∈ S then -1 else 1

@[expose] def E6set : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  {M | ∃ S : Finset (Fin 8), 0 ∉ S ∧ S.card = 6 ∧ M = sgn S}

@[expose] def F1set : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  {M | ∃ S : Finset (Fin 8), 0 ∉ S ∧ Even S.card ∧ M = sgn S}

structure N7Setup (X : Type) [Group X] [Finite X] where
  ρ : X →* Matrix (Fin 8) (Fin 8) (ZMod 3)
  ρ_inj : Function.Injective ρ
  surj_H : ∀ M ∈ evenFix0 7, ∃ x, ρ x = M
  norm_iff : ∀ x : X, ρ x ∈ evenFix0 7 ↔ ∃ c : ZMod 3, ρ x *ᵥ e0 = c • e0
  odd_core : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥
  not_inv : ∃ x : X, ¬ ∃ c : ZMod 3, ρ x *ᵥ e0 = c • e0

theorem evenFix0_mulVec_e0 {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ evenFix0 7) :
    M *ᵥ e0 = e0 := by
  obtain ⟨σ, s, -, ⟨hσ0, hs0, -⟩, rfl⟩ := hM
  exact spMat_mulVec_e0 (n := 7) hσ0 hs0

namespace N7Setup

variable {X : Type} [Group X] [Finite X] (S : N7Setup X)

@[expose] def H : Subgroup X where
  carrier := {x | S.ρ x *ᵥ e0 = e0}
  mul_mem' {x y} hx hy := by
    show S.ρ (x * y) *ᵥ e0 = e0
    rw [map_mul, ← Matrix.mulVec_mulVec]
    have hy' : S.ρ y *ᵥ e0 = e0 := hy
    have hx' : S.ρ x *ᵥ e0 = e0 := hx
    rw [hy', hx']
  one_mem' := by
    show S.ρ 1 *ᵥ e0 = e0
    rw [map_one, Matrix.one_mulVec]
  inv_mem' {x} hx := by
    show S.ρ x⁻¹ *ᵥ e0 = e0
    have hx' : S.ρ x *ᵥ e0 = e0 := hx
    calc S.ρ x⁻¹ *ᵥ e0 = S.ρ x⁻¹ *ᵥ (S.ρ x *ᵥ e0) := by rw [hx']
      _ = (S.ρ x⁻¹ * S.ρ x) *ᵥ e0 := by rw [Matrix.mulVec_mulVec]
      _ = e0 := by rw [← map_mul, inv_mul_cancel, map_one, Matrix.one_mulVec]

theorem mem_H_iff (x : X) : x ∈ S.H ↔ S.ρ x ∈ evenFix0 7 := by
  constructor
  · intro hx
    have hx' : S.ρ x *ᵥ e0 = e0 := hx
    exact (S.norm_iff x).2 ⟨1, by rw [hx', one_smul]⟩
  · intro hx
    exact evenFix0_mulVec_e0 hx

end N7Setup

theorem q2nN7_sgn_eq_spMat (S : Finset (Fin 8)) :
    sgn S = spMat 1 (fun i => if i ∈ S then -1 else 1) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [sgn, spMat_apply]
  · simp [sgn, spMat_apply, Matrix.diagonal_apply_ne _ h, h]

theorem q2nN7_sgn_mul (S T : Finset (Fin 8)) : sgn S * sgn T = sgn (symmDiff S T) := by
  unfold sgn
  rw [Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;> simp [hS, hT, Finset.mem_symmDiff] <;> decide

theorem q2nN7_sgn_empty : sgn ∅ = 1 := by
  simp [sgn, Matrix.diagonal_one]

theorem q2nN7_sgn_mul_self (S : Finset (Fin 8)) : sgn S * sgn S = 1 := by
  rw [q2nN7_sgn_mul, symmDiff_self, Finset.bot_eq_empty, q2nN7_sgn_empty]

theorem q2nN7_sgn_comm (S T : Finset (Fin 8)) : sgn S * sgn T = sgn T * sgn S := by
  rw [q2nN7_sgn_mul, q2nN7_sgn_mul, symmDiff_comm]

theorem q2nN7_sgn_injective : Function.Injective sgn := by
  intro S T h
  ext i
  have h1 := congrFun (congrFun h i) i
  simp only [sgn, Matrix.diagonal_apply_eq] at h1
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T
  · exact iff_of_true hS hT
  · rw [if_pos hS, if_neg hT] at h1
    exact absurd h1 (by decide)
  · rw [if_neg hS, if_pos hT] at h1
    exact absurd h1 (by decide)
  · exact iff_of_false hS hT

theorem q2nN7_spMat_mul_sgn (σ : Equiv.Perm (Fin 8)) (s : Fin 8 → ZMod 3) (S : Finset (Fin 8)) :
    spMat σ s * sgn S = sgn (S.map σ.toEmbedding) * spMat σ s := by
  ext i j
  simp only [sgn, Matrix.mul_diagonal, Matrix.diagonal_mul, spMat_apply]
  by_cases h : i = σ j
  · subst h
    by_cases hj : j ∈ S <;> simp [hj, mul_comm]
  · simp [h]

theorem q2nN7_sgn_mulVec (S : Finset (Fin 8)) (v : Fin 8 → ZMod 3) :
    sgn S *ᵥ v = fun i => if i ∈ S then -v i else v i := by
  funext i
  simp only [sgn, Matrix.mulVec_diagonal]
  by_cases h : i ∈ S
  · simp only [h, if_true]
    exact neg_one_mul _
  · simp [h]

theorem q2nN7_sgn_mem_evenFix0 {S : Finset (Fin 8)} (h0 : (0 : Fin 8) ∉ S) (he : Even S.card) :
    sgn S ∈ evenFix0 7 := by
  rw [q2nN7_sgn_eq_spMat]
  exact sgnOn_mem_evenFix0 (n := 7) S h0 he

end CFSG.StandardType.FrameRoute.FS81

end
