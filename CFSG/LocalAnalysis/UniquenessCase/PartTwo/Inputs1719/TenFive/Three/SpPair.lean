module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Invol.SpHeis

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open Matrix
open CFSG.Open (StatedProj StatedSp)
open CFSG.GH74.GLS.IVK.Proofs2.Lemma41dL3 (Heis)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (formJ)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive (unipSp coe_unipSp)

variable {r : ℕ} {K : Type} [Field K]

private theorem one_add_mul_one_add_comm {X Y : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hXY : X * Y = 0) (hYX : Y * X = 0) :
    (1 + X) * (1 + Y) = (1 + Y) * (1 + X) := by
  have h1 : (1 + X) * (1 + Y) = 1 + X + Y := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hXY, add_zero]
  have h2 : (1 + Y) * (1 + X) = 1 + Y + X := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.one_mul, hYX, add_zero]
  rw [h1, h2]
  abel

private theorem heis_zero_zero_smul {A B P Q : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (c : K) :
    ((⟨0, 0, c⟩ : Heis K).a • A + (⟨0, 0, c⟩ : Heis K).b • B +
        (⟨0, 0, c⟩ : Heis K).c • P +
        ((⟨0, 0, c⟩ : Heis K).a * (⟨0, 0, c⟩ : Heis K).b -
          (⟨0, 0, c⟩ : Heis K).c) • Q) = c • (P - Q) := by
  simp only [zero_smul, zero_mul, zero_sub, zero_add, add_zero]
  rw [smul_sub, sub_eq_add_neg, neg_smul]

private theorem heisM_mul_heisM_eq_zero {N₁ N₂ N₃ N₄ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h13 : N₁ * N₃ = 0) (h14 : N₁ * N₄ = 0) (h23 : N₂ * N₃ = 0) (h24 : N₂ * N₄ = 0)
    (x y : Heis K) :
    (x.a • N₁ + x.b • N₂ + x.c • (N₁ * N₂) + (x.a * x.b - x.c) • (N₂ * N₁)) *
      (y.a • N₃ + y.b • N₄ + y.c • (N₃ * N₄) + (y.a * y.b - y.c) • (N₄ * N₃)) = 0 := by
  have hP3 : (N₁ * N₂) * N₃ = 0 := by rw [Matrix.mul_assoc, h23, Matrix.mul_zero]
  have hP4 : (N₁ * N₂) * N₄ = 0 := by rw [Matrix.mul_assoc, h24, Matrix.mul_zero]
  have hQ3 : (N₂ * N₁) * N₃ = 0 := by rw [Matrix.mul_assoc, h13, Matrix.mul_zero]
  have hQ4 : (N₂ * N₁) * N₄ = 0 := by rw [Matrix.mul_assoc, h14, Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc, h13, h14, h23, h24, hP3, hP4, hQ3, hQ4, smul_zero,
    zero_mul, add_zero]

private theorem heisM_mul_heisM_eq_zero' {N₁ N₂ N₃ N₄ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (h31 : N₃ * N₁ = 0) (h32 : N₃ * N₂ = 0) (h41 : N₄ * N₁ = 0) (h42 : N₄ * N₂ = 0)
    (x y : Heis K) :
    (y.a • N₃ + y.b • N₄ + y.c • (N₃ * N₄) + (y.a * y.b - y.c) • (N₄ * N₃)) *
      (x.a • N₁ + x.b • N₂ + x.c • (N₁ * N₂) + (x.a * x.b - x.c) • (N₂ * N₁)) = 0 := by
  have hR1 : (N₃ * N₄) * N₁ = 0 := by rw [Matrix.mul_assoc, h41, Matrix.mul_zero]
  have hR2 : (N₃ * N₄) * N₂ = 0 := by rw [Matrix.mul_assoc, h42, Matrix.mul_zero]
  have hS1 : (N₄ * N₃) * N₁ = 0 := by rw [Matrix.mul_assoc, h31, Matrix.mul_zero]
  have hS2 : (N₄ * N₃) * N₂ = 0 := by rw [Matrix.mul_assoc, h32, Matrix.mul_zero]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
    ← Matrix.mul_assoc, h31, h32, h41, h42, hR1, hR2, hS1, hS2, smul_zero,
    zero_mul, add_zero]

theorem exists_heis_pair_projectiveSp (hr : 1 ≤ r)
    {N₁ N₂ N₃ N₄ : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K}
    (hs₁ : N₁ᵀ * formJ r K + formJ r K * N₁ = 0) (hs₂ : N₂ᵀ * formJ r K + formJ r K * N₂ = 0)
    (hs₃ : N₃ᵀ * formJ r K + formJ r K * N₃ = 0) (hs₄ : N₄ᵀ * formJ r K + formJ r K * N₄ = 0)
    (h₁ : N₁ * N₁ = 0) (h₂ : N₂ * N₂ = 0) (h₃ : N₃ * N₃ = 0) (h₄ : N₄ * N₄ = 0)
    (h₁₂₁ : N₁ * N₂ * N₁ = 0) (h₂₁₂ : N₂ * N₁ * N₂ = 0)
    (h₃₄₃ : N₃ * N₄ * N₃ = 0) (h₄₃₄ : N₄ * N₃ * N₄ = 0)
    (h₁₂ : N₁ * N₂ ≠ 0) (hPQ : N₁ * N₂ ≠ N₂ * N₁)
    (h₃₄ : N₃ * N₄ ≠ 0) (hPQ' : N₃ * N₄ ≠ N₄ * N₃)
    (h13 : N₁ * N₃ = 0) (h14 : N₁ * N₄ = 0) (h23 : N₂ * N₃ = 0) (h24 : N₂ * N₄ = 0)
    (h31 : N₃ * N₁ = 0) (h32 : N₃ * N₂ = 0) (h41 : N₄ * N₁ = 0) (h42 : N₄ * N₂ = 0)
    (hcen : N₁ * N₂ - N₂ * N₁ = N₃ * N₄ - N₄ * N₃) :
    ∃ ι₁ ι₂ : Heis K →* StatedProj (StatedSp r K), Function.Injective ι₁ ∧
      Function.Injective ι₂ ∧ (∀ x y, Commute (ι₁ x) (ι₂ y)) ∧
      (∀ c : K, ι₁ ⟨0, 0, c⟩ = ι₂ ⟨0, 0, c⟩) ∧
      ι₁ ⟨1, 0, 0⟩ = proj r K (unipSp N₁ hs₁ h₁) ∧ ι₂ ⟨1, 0, 0⟩ = proj r K (unipSp N₃ hs₃ h₃) ∧
      ∀ (c : K) (hs : (c • (N₁ * N₂ - N₂ * N₁))ᵀ * formJ r K +
          formJ r K * (c • (N₁ * N₂ - N₂ * N₁)) = 0)
        (hN : c • (N₁ * N₂ - N₂ * N₁) * (c • (N₁ * N₂ - N₂ * N₁)) = 0),
        ι₁ ⟨0, 0, c⟩ = proj r K (unipSp (c • (N₁ * N₂ - N₂ * N₁)) hs hN) := by
  classical
  obtain ⟨φ₁, hφ₁inj, hφ₁mat⟩ :=
    exists_heisSp (r := r) (K := K) hr hs₁ hs₂ h₁ h₂ h₁₂₁ h₂₁₂ h₁₂ hPQ
  obtain ⟨φ₂, hφ₂inj, hφ₂mat⟩ :=
    exists_heisSp (r := r) (K := K) hr hs₃ hs₄ h₃ h₄ h₃₄₃ h₄₃₄ h₃₄ hPQ'
  refine ⟨(proj r K).comp φ₁, (proj r K).comp φ₂, hφ₁inj, hφ₂inj, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    have hcomm : φ₁ x * φ₂ y = φ₂ y * φ₁ x := by
      apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
        hφ₁mat x, hφ₂mat y]
      exact one_add_mul_one_add_comm
        (heisM_mul_heisM_eq_zero h13 h14 h23 h24 x y)
        (heisM_mul_heisM_eq_zero' h31 h32 h41 h42 x y)
    rw [commute_iff_eq]
    simp only [MonoidHom.comp_apply]
    rw [← map_mul, ← map_mul, hcomm]
  · intro c
    have hcenSp : φ₁ ⟨0, 0, c⟩ = φ₂ ⟨0, 0, c⟩ := by
      apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
      rw [hφ₁mat ⟨0, 0, c⟩, hφ₂mat ⟨0, 0, c⟩,
        heis_zero_zero_smul (A := N₁) (B := N₂) (P := N₁ * N₂) (Q := N₂ * N₁) c,
        heis_zero_zero_smul (A := N₃) (B := N₄) (P := N₃ * N₄) (Q := N₄ * N₃) c, hcen]
    exact congrArg (proj r K) hcenSp
  · apply congrArg (proj r K)
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [hφ₁mat ⟨1, 0, 0⟩, coe_unipSp]
    simp
  · apply congrArg (proj r K)
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [hφ₂mat ⟨1, 0, 0⟩, coe_unipSp]
    simp
  · intro c hs hN
    apply congrArg (proj r K)
    apply CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.statedSp_ext
    rw [hφ₁mat ⟨0, 0, c⟩, coe_unipSp,
      heis_zero_zero_smul (A := N₁) (B := N₂) (P := N₁ * N₂) (Q := N₂ * N₁) c]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
