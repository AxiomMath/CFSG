module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open Matrix

variable {K : Type} [Field K]

@[expose] def krylov (m : Matrix (Fin 3) (Fin 3) K) (e : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  Matrix.of fun i j => ((![e, m *ᵥ e, m *ᵥ (m *ᵥ e)] : Fin 3 → Fin 3 → K) j) i

@[expose] def pol (m : Matrix (Fin 3) (Fin 3) K) (a : Fin 3 → K) : Matrix (Fin 3) (Fin 3) K :=
  a 0 • (1 : Matrix (Fin 3) (Fin 3) K) + a 1 • m + a 2 • (m * m)

theorem krylov_mulVec (m : Matrix (Fin 3) (Fin 3) K) (e a : Fin 3 → K) :
    krylov m e *ᵥ a = a 0 • e + a 1 • (m *ᵥ e) + a 2 • (m *ᵥ (m *ᵥ e)) := by
  funext i
  simp [krylov, Matrix.mulVec, dotProduct, Fin.sum_univ_three, add_assoc]
  ring

theorem pol_mulVec (m : Matrix (Fin 3) (Fin 3) K) (e a : Fin 3 → K) :
    pol m a *ᵥ e = krylov m e *ᵥ a := by
  rw [krylov_mulVec, pol, Matrix.add_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
    Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]

theorem pol_commute (m : Matrix (Fin 3) (Fin 3) K) (a : Fin 3 → K) : pol m a * m = m * pol m a := by
  simp only [pol, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc]

theorem pol_mul (m : Matrix (Fin 3) (Fin 3) K) (a b : Fin 3 → K) :
    pol m a * pol m b = pol m b * pol m a := by
  simp only [pol, Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
    Matrix.mul_one, Matrix.mul_assoc]
  module

variable {m : Matrix (Fin 3) (Fin 3) K} {e : Fin 3 → K}

theorem krylov_surjective (h : IsUnit (krylov m e).det) (v : Fin 3 → K) :
    ∃ a, krylov m e *ᵥ a = v :=
  ⟨(krylov m e)⁻¹ *ᵥ v, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ h, Matrix.one_mulVec]⟩

theorem krylov_injective (h : IsUnit (krylov m e).det) {a b : Fin 3 → K}
    (hab : krylov m e *ᵥ a = krylov m e *ᵥ b) : a = b := by
  have h1 : (krylov m e)⁻¹ *ᵥ (krylov m e *ᵥ a) = a := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  have h2 : (krylov m e)⁻¹ *ᵥ (krylov m e *ᵥ b) = b := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ h, Matrix.one_mulVec]
  rw [← h1, ← h2, hab]

theorem pol_injective (h : IsUnit (krylov m e).det) {a b : Fin 3 → K} (hab : pol m a = pol m b) :
    a = b := by
  apply krylov_injective h
  rw [← pol_mulVec, ← pol_mulVec, hab]

theorem eq_pol_of_commute (h : IsUnit (krylov m e).det) {c : Matrix (Fin 3) (Fin 3) K}
    (hc : c * m = m * c) : ∃ a, c = pol m a := by
  obtain ⟨a, ha⟩ := krylov_surjective h (c *ᵥ e)
  have hdm : (c - pol m a) * m = m * (c - pol m a) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, hc, pol_commute]
  have hde : (c - pol m a) *ᵥ e = 0 := by
    rw [Matrix.sub_mulVec, pol_mulVec, ha, sub_self]
  have hd1 : (c - pol m a) *ᵥ (m *ᵥ e) = 0 := by
    rw [Matrix.mulVec_mulVec, hdm, ← Matrix.mulVec_mulVec, hde, Matrix.mulVec_zero]
  have hd2 : (c - pol m a) *ᵥ (m *ᵥ (m *ᵥ e)) = 0 := by
    rw [Matrix.mulVec_mulVec, hdm, ← Matrix.mulVec_mulVec, hd1, Matrix.mulVec_zero]
  have hd : ∀ v, (c - pol m a) *ᵥ v = 0 := by
    intro v
    obtain ⟨b, rfl⟩ := krylov_surjective h v
    rw [krylov_mulVec, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      Matrix.mulVec_smul, hde, hd1, hd2]
    simp
  have h0 : c - pol m a = 0 := by
    ext i j
    have := congrFun (hd (Pi.single j 1)) i
    simpa [Matrix.mulVec_single] using this
  exact ⟨a, sub_eq_zero.1 h0⟩

theorem commute_of_commute (h : IsUnit (krylov m e).det) {c₁ c₂ : Matrix (Fin 3) (Fin 3) K}
    (h₁ : c₁ * m = m * c₁) (h₂ : c₂ * m = m * c₂) : c₁ * c₂ = c₂ * c₁ := by
  obtain ⟨a, rfl⟩ := eq_pol_of_commute h h₁
  obtain ⟨b, rfl⟩ := eq_pol_of_commute h h₂
  exact pol_mul m a b

end CFSG.RankThree.PartOne.KFOUT3
