module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne

open Matrix

@[expose] def symplecticFourGram (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, 0, 1; 0, 0, 1, 0; 0, -1, 0, 0; -1, 0, 0, 0]

@[expose] def symplecticFourS (K : Type) [Field K] : Subgroup (GL (Fin 4) K) where
  carrier := {g | (g : Matrix (Fin 4) (Fin 4) K)ᵀ * symplecticFourGram K * g =
    symplecticFourGram K}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, Units.val_mul, Matrix.transpose_mul] at hg hh ⊢
    calc (h : Matrix (Fin 4) (Fin 4) K)ᵀ * (g : Matrix (Fin 4) (Fin 4) K)ᵀ *
          symplecticFourGram K * ((g : Matrix (Fin 4) (Fin 4) K) * h) =
        (h : Matrix (Fin 4) (Fin 4) K)ᵀ * ((g : Matrix (Fin 4) (Fin 4) K)ᵀ *
          symplecticFourGram K * g) * h := by simp only [Matrix.mul_assoc]
      _ = symplecticFourGram K := by rw [hg, hh]
  one_mem' := by simp
  inv_mem' := by
    intro g hg
    simp only [Set.mem_ofPred_eq] at hg ⊢
    have h1 : (g : Matrix (Fin 4) (Fin 4) K) * ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ * symplecticFourGram K *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) =
        ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)ᵀ *
          ((g : Matrix (Fin 4) (Fin 4) K)ᵀ * symplecticFourGram K * g) *
          ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) := by rw [hg]
      _ = ((g : Matrix (Fin 4) (Fin 4) K) * ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K))ᵀ *
          symplecticFourGram K * ((g : Matrix (Fin 4) (Fin 4) K) *
            ((g⁻¹ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)) := by
        rw [Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = symplecticFourGram K := by rw [h1, transpose_one, Matrix.one_mul, Matrix.mul_one]

theorem mem_symplecticFourS_iff {K : Type} [Field K] {g : GL (Fin 4) K} :
    g ∈ symplecticFourS K ↔
      (g : Matrix (Fin 4) (Fin 4) K)ᵀ * symplecticFourGram K * g = symplecticFourGram K :=
  Iff.rfl

@[expose] def symplecticFourZ (K : Type) [Field K] : Subgroup (symplecticFourS K) where
  carrier := {g | ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = 1 ∨
    ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = -1}
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_ofPred_eq, Subgroup.coe_mul, Units.val_mul] at hg hh ⊢
    rcases hg with hg | hg <;> rcases hh with hh | hh <;> rw [hg, hh] <;> simp
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro g hg
    have hgg : g * g = 1 :=
      Subtype.ext (Units.ext (by rcases hg with hg | hg <;> simp [hg]))
    rw [inv_eq_of_mul_eq_one_right hgg]
    exact hg

instance symplecticFourZ_normal (K : Type) [Field K] : (symplecticFourZ K).Normal where
  conj_mem := by
    intro n hn g
    have hcomm : g * n = n * g :=
      Subtype.ext (Units.ext (by rcases hn with hn | hn <;> simp [hn]))
    rwa [hcomm, mul_inv_cancel_right]

@[expose] def symplecticFourE14 (K : Type) [Field K] : Matrix (Fin 4) (Fin 4) K :=
  Matrix.single 0 3 1

@[expose] def symplecticFourTransvection (K : Type) [Field K] (c : K) : symplecticFourS K :=
  ⟨⟨1 + c • symplecticFourE14 K, 1 - c • symplecticFourE14 K,
    by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, symplecticFourE14, Matrix.single_apply,
          Matrix.one_apply],
    by
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, symplecticFourE14, Matrix.single_apply,
          Matrix.one_apply]⟩,
    by
      change (1 + c • symplecticFourE14 K)ᵀ * symplecticFourGram K *
        (1 + c • symplecticFourE14 K) = symplecticFourGram K
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_four, symplecticFourGram, symplecticFourE14,
          Matrix.single_apply, Matrix.one_apply]⟩

theorem coe_symplecticFourTransvection (K : Type) [Field K] (c : K) :
    (((symplecticFourTransvection K c : symplecticFourS K) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = 1 + c • symplecticFourE14 K :=
  rfl

end CFSG.RankThree.PartOne
