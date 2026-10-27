module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18U54InvRankDual
public import CFSG.GH74.KGroups.FieldGF
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.GH74.KGroups

@[expose] def idx51 : HypIndex 2 1 → Fin 5
  | .inl i => ⟨i.1, by omega⟩
  | .inr (.inl _) => 2
  | .inr (.inr i) => ⟨i.1 + 3, by omega⟩

@[expose] def tab16 (M : Matrix (Fin 5) (Fin 5) ℕ) : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16 :=
  fun a b => GF16.ofNat' (M (idx51 a) (idx51 b))

@[expose] def bar16 (c : GF16) : GF16 := c ^ 4

@[expose] def D16 : Fin 3 → Matrix (HypIndex 2 1) (HypIndex 2 1) GF16 :=
  ![tab16 !![0, 0, 0, 3, 0; 0, 14, 0, 0, 2; 0, 0, 1, 0, 0; 9, 0, 0, 9, 0; 0, 14, 0, 0, 0],
    tab16 !![9, 0, 0, 3, 0; 0, 14, 0, 0, 2; 0, 0, 1, 0, 0; 9, 0, 0, 0, 0; 0, 14, 0, 0, 0],
    tab16 !![1, 0, 0, 0, 0; 0, 14, 0, 0, 2; 0, 0, 8, 0, 0; 0, 0, 0, 1, 0; 0, 14, 0, 0, 0]]

@[expose] def G16 : Fin 4 → Matrix (HypIndex 2 1) (HypIndex 2 1) GF16 :=
  ![tab16 !![1, 0, 0, 1, 0; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1],
    tab16 !![2, 0, 3, 6, 0; 0, 1, 0, 0, 0; 1, 0, 0, 2, 0; 1, 0, 1, 3, 0; 0, 0, 0, 0, 1],
    tab16 !![1, 0, 0, 0, 0; 0, 3, 2, 0, 6; 0, 1, 0, 0, 3; 0, 0, 0, 1, 0; 0, 1, 1, 0, 2],
    tab16 !![1, 0, 0, 0, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1]]

@[expose] def Dprod16 (c : Fin 3 → ZMod 5) : Matrix (HypIndex 2 1) (HypIndex 2 1) GF16 :=
  D16 0 ^ (c 0).val * D16 1 ^ (c 1).val * D16 2 ^ (c 2).val

@[expose] def mu16 (i : Fin 4) : GF16 := if i = 3 then GF16.ofNat' 15 else 1

theorem D16_unitary (j : Fin 3) :
    ((D16 j).map bar16)ᵀ * hypGram 2 1 GF16 * D16 j = hypGram 2 1 GF16 := by
  fin_cases j <;> decide +kernel

theorem D16_det (j : Fin 3) : (D16 j).det = 1 := by
  fin_cases j <;> decide +kernel

theorem G16_unitary (i : Fin 4) :
    ((G16 i).map bar16)ᵀ * hypGram 2 1 GF16 * G16 i = hypGram 2 1 GF16 := by
  fin_cases i <;> decide +kernel

theorem G16_det (i : Fin 4) : (G16 i).det = 1 := by
  fin_cases i <;> decide +kernel

theorem D16_comm (j j' : Fin 3) : D16 j * D16 j' = D16 j' * D16 j := by
  fin_cases j <;> fin_cases j' <;> decide +kernel

theorem D16_pow_five (j : Fin 3) : D16 j ^ 5 = 1 := by
  fin_cases j <;> decide +kernel

theorem G16_mul_self (i : Fin 4) : G16 i * G16 i = 1 := by
  fin_cases i <;> decide +kernel

theorem G16_conj (i : Fin 4) (j : Fin 3) :
    G16 i * D16 j * G16 i =
      Matrix.scalar (HypIndex 2 1) (mu16 i) * Dprod16 (Amap i (Pi.single j 1)) := by
  fin_cases i <;> fin_cases j <;> decide +kernel

theorem mu16_norm (i : Fin 4) : mu16 i * bar16 (mu16 i) = 1 := by
  fin_cases i <;> decide +kernel

theorem mu16_pow_five (i : Fin 4) : mu16 i ^ 5 = 1 := by
  fin_cases i <;> decide +kernel

theorem mu16_ne_zero (i : Fin 4) : mu16 i ≠ 0 := by
  fin_cases i <;> decide +kernel

theorem scal16_unitary (i : Fin 4) :
    ((Matrix.scalar (HypIndex 2 1) (mu16 i)).map bar16)ᵀ * hypGram 2 1 GF16 *
      Matrix.scalar (HypIndex 2 1) (mu16 i) = hypGram 2 1 GF16 := by
  fin_cases i <;> decide +kernel

theorem scal16_det (i : Fin 4) : (Matrix.scalar (HypIndex 2 1) (mu16 i)).det = 1 := by
  fin_cases i <;> decide +kernel

theorem G16_zero : G16 0 = 1 + Matrix.single (.inl 0) (.inr (.inr 0)) 1 := by
  decide +kernel

theorem G16_zero_mul_three : G16 0 * G16 3 =
    1 + (Matrix.single (.inl 0) (.inr (.inr 0)) 1 + Matrix.single (.inl 1) (.inr (.inr 1)) 1) := by
  decide +kernel

theorem Dprod16_cS_entry : Dprod16 cS (.inl 0) (.inr (.inr 0)) ≠ 0 := by
  decide +kernel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank
