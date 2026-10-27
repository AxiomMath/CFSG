module

public import CFSG.RankThree.PartOne.KC.UnitaryCrossPrimeModel
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom)

theorem uc22s218_u4_exists_hyp_double {K₀ : Type} [Field K₀] {f₀ : ℕ}
    (h₀ : UnitaryFieldData 2 f₀ K₀) :
    ∃ B : Matrix (Fin 4) (HypIndex 2 0) K₀,
      IsGramHypTransport (r := 2) (ε := 0) h₀ (idGram K₀ 4) B ∧
      ∀ a b : K₀, ∃ d : HypIndex 2 0 → K₀, diagonal ![a, a, b, b] * B = B * diagonal d := by
  obtain ⟨W, hW⟩ : ∃ W : Matrix (Fin 2) (HypIndex 1 0) K₀,
      IsGramHypTransport (r := 1) (ε := 0) h₀ (1 : Matrix (Fin 2) (Fin 2) K₀) W :=
    exists_isGramHypTransport (r := 1) (ε := 0) h₀ 1 (by simp) (by simp)
  have h00 := congrFun (congrFun hW (.inl 0)) (.inl 0)
  have h01 := congrFun (congrFun hW (.inl 0)) (.inr (.inr 0))
  have h10 := congrFun (congrFun hW (.inr (.inr 0))) (.inl 0)
  have h11 := congrFun (congrFun hW (.inr (.inr 0))) (.inr (.inr 0))
  simp [mul_apply, Fin.sum_univ_two, hypGram_apply] at h00 h01 h10 h11
  refine ⟨fromCols !![W 0 (.inl 0), 0; W 1 (.inl 0), 0; 0, W 0 (.inl 0); 0, W 1 (.inl 0)]
      (fromCols (0 : Matrix (Fin 4) (Fin 0) K₀)
        !![W 0 (.inr (.inr 0)), 0; W 1 (.inr (.inr 0)), 0; 0, W 0 (.inr (.inr 0));
          0, W 1 (.inr (.inr 0))]), ?_, ?_⟩
  · unfold IsGramHypTransport
    ext x y
    rcases x with i | k | i <;> rcases y with j | l | j <;> try exact Fin.elim0 ‹Fin 0›
    all_goals
      fin_cases i <;> fin_cases j <;>
        simp [mul_apply, Fin.sum_univ_four, hypGram_apply]
    all_goals first | exact h00 | exact h01 | exact h10 | exact h11
  · intro a b
    refine ⟨Sum.elim ![a, b] (Sum.elim finZeroElim ![a, b]), ?_⟩
    ext i x
    rcases x with j | k | j <;> try exact Fin.elim0 ‹Fin 0›
    all_goals
      fin_cases i <;> fin_cases j <;>
        simp [diagonal_mul, mul_diagonal, mul_comm]

theorem uc22s218_u4_hyp_frame {K₀ : Type} [Field K₀] {f₀ : ℕ} (h₀ : UnitaryFieldData 2 f₀ K₀)
    (P : GL (Fin 4) K₀) (hP : P ∈ primeFormUnitary h₀ (idGram K₀ 4)) (a b : K₀ˣ) :
    ∃ (T : Matrix (Fin 4) (HypIndex 2 0) K₀)
      (_ : IsGramHypTransport (r := 2) (ε := 0) h₀ (idGram K₀ 4) T) (d : HypIndex 2 0 → K₀),
      gramHypInv (r := 2) (ε := 0) h₀ (idGram K₀ 4) T *
        ((P * diagHom 4 ![a, a, b, b] * P⁻¹ : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) * T =
        diagonal d := by
  obtain ⟨B, hB, hBd⟩ := uc22s218_u4_exists_hyp_double h₀
  obtain ⟨d, hd⟩ := hBd a b
  have hT : IsGramHypTransport (r := 2) (ε := 0) h₀ (idGram K₀ 4)
      ((P : Matrix (Fin 4) (Fin 4) K₀) * B) := by
    unfold IsGramHypTransport
    rw [barTranspose_mul_mul, mem_primeFormUnitary.mp hP]
    exact hB
  refine ⟨_, hT, d, ?_⟩
  have hdiag : (fun i => ((![a, a, b, b] i : K₀ˣ) : K₀)) = ![(a : K₀), a, b, b] := by
    funext i
    fin_cases i <;> rfl
  have hMT : ((P * diagHom 4 ![a, a, b, b] * P⁻¹ : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀) *
      ((P : Matrix (Fin 4) (Fin 4) K₀) * B) =
        (P : Matrix (Fin 4) (Fin 4) K₀) * B * diagonal d := by
    rw [Units.val_mul, Units.val_mul, coe_diagHom, hdiag, Matrix.mul_assoc _ B, ← hd]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc ((P⁻¹ : GL (Fin 4) K₀) : Matrix (Fin 4) (Fin 4) K₀), Units.inv_mul,
      Matrix.one_mul]
  rw [Matrix.mul_assoc, hMT, ← Matrix.mul_assoc, gramHypInv_mul hT, Matrix.one_mul]

end CFSG.LocalAnalysis.UniquenessCase.UC22
