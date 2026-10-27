module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank

namespace S153E61B

section Finite

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem matrix_invol_conj : ∀ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A * A = 1 → A ≠ 1 →
    ∃ C : Matrix (Fin 3) (Fin 3) (ZMod 2), C.det = 1 ∧
      C * A = !![1, 1, 0; 0, 1, 0; 0, 0, 1] * C := by
  decide +kernel

theorem exists_conj_J (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) (hA : A ≠ 1) (hA2 : A * A = 1) :
    ∃ c : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)).det = 1 ∧
      ((c * A * c⁻¹ : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        !![1, 1, 0; 0, 1, 0; 0, 0, 1] := by
  obtain ⟨C, hdet, hC⟩ := matrix_invol_conj (A : Matrix (Fin 3) (Fin 3) (ZMod 2))
    (by rw [← Units.val_mul, hA2]; rfl) (fun h => hA (Units.ext h))
  have hne : C.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  obtain ⟨c, hc⟩ : ∃ c : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2),
      (c : Matrix (Fin 3) (Fin 3) (ZMod 2)) = C :=
    ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero C hne, rfl⟩
  refine ⟨c, hc ▸ hdet, ?_⟩
  rw [Units.val_mul, Units.val_mul, hc, hC, mul_assoc, ← hc, Units.mul_inv, mul_one]

theorem statedSL_invol_conj (A B : ↥(StatedSL 3 (ZMod 2))) (hA : A ≠ 1) (hA2 : A * A = 1)
    (hB : B ≠ 1) (hB2 : B * B = 1) : ∃ C : ↥(StatedSL 3 (ZMod 2)), C * A * C⁻¹ = B := by
  obtain ⟨c₁, hd₁, h₁⟩ := exists_conj_J (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))
    (fun h => hA (Subtype.ext h)) (by simpa using congrArg Subtype.val hA2)
  obtain ⟨c₂, hd₂, h₂⟩ := exists_conj_J (B : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))
    (fun h => hB (Subtype.ext h)) (by simpa using congrArg Subtype.val hB2)
  have hc₁ : c₁ ∈ StatedSL 3 (ZMod 2) := Subgroup.subset_closure hd₁
  have hc₂ : c₂ ∈ StatedSL 3 (ZMod 2) := Subgroup.subset_closure hd₂
  refine ⟨⟨c₂⁻¹ * c₁, (StatedSL 3 (ZMod 2)).mul_mem ((StatedSL 3 (ZMod 2)).inv_mem hc₂) hc₁⟩, ?_⟩
  apply Subtype.ext
  have h12 : c₁ * (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) * c₁⁻¹ =
      c₂ * (B : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) * c₂⁻¹ := Units.ext (h₁.trans h₂.symm)
  show c₂⁻¹ * c₁ * (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) * (c₂⁻¹ * c₁)⁻¹ = B
  calc c₂⁻¹ * c₁ * (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) * (c₂⁻¹ * c₁)⁻¹
      = c₂⁻¹ * (c₁ * (A : Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) * c₁⁻¹) * c₂ := by group
    _ = B := by rw [h12]; group

end Finite

end S153E61B

end CFSG.Quasithin
