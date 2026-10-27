module

public import CFSG.OddTranspositions.PartThree.Twelve.TenFiveModelChar

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalInvolution

set_option backward.isDefEq.respectTransparency false

theorem detSpinorNorm_mem_closure_pair {k : ℕ} (ε π : Bool)
    {g : GL (Fin (k + 1)) (ZMod 5)} (hg : g ∈ fiveReflectionGroup k ε π) :
    detSpinorNorm (fiveQ_nondegenerate k ε)
        ⟨fiveGLIso k g, fiveGLIso_mem_orthogonalGroup_of_mem hg⟩ ∈
      Subgroup.closure ({((-1 : (ZMod 5)ˣ), sqClass π)} : Set _) := by
  let a : (ZMod 5)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 5)) :=
    ((-1 : (ZMod 5)ˣ), sqClass π)
  refine Subgroup.closure_induction (k := fiveReflections k ε π)
    (p := fun g hg => detSpinorNorm (fiveQ_nondegenerate k ε)
      ⟨fiveGLIso k g, fiveGLIso_mem_orthogonalGroup_of_mem hg⟩ ∈
      Subgroup.closure ({((-1 : (ZMod 5)ˣ), sqClass π)} : Set _)) ?_ ?_ ?_ ?_ hg
  · intro r hr
    obtain ⟨v, hv, hsign, rfl⟩ := exists_eq_fiveReflOf hr
    have hQv : fiveQ k ε v ≠ 0 := by rwa [fiveQ_apply]
    letI : Invertible (fiveQ k ε v) := invertibleOfNonzero hQv
    have hsub : (⟨fiveGLIso k (fiveReflOf k ε v),
        fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.subset_closure hr)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) = reflO k ε v := by
      apply Subtype.ext
      change fiveGLIso k (fiveReflOf k ε v) = reflect (fiveQ k ε) v
      rw [fiveGLIso_fiveReflOf]
      rfl
    have hdet_eq : detSpinorNorm (fiveQ_nondegenerate k ε)
        ⟨fiveGLIso k (fiveReflOf k ε v),
          fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.subset_closure hr)⟩ =
        detSpinorNorm (fiveQ_nondegenerate k ε) (reflO k ε v) :=
      congrArg (detSpinorNorm (fiveQ_nondegenerate k ε)) hsub
    rw [hdet_eq, detSpinorNorm_reflO]
    have hsign' : IsSquare (fiveQ k ε v) ↔ π = true := by
      rw [fiveQ_apply]
      exact hsign
    rw [squareClassHom_unitOfInvertible_eq_sqClass hsign']
    exact Subgroup.subset_closure (by simp)
  · have h1 : (⟨fiveGLIso k 1,
        fiveGLIso_mem_orthogonalGroup_of_mem
          (Subgroup.one_mem (Subgroup.closure (fiveReflections k ε π)))⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) = 1 := by
      apply Subtype.ext
      change fiveGLIso k 1 = 1
      rw [map_one]
    have hdet1 : detSpinorNorm (fiveQ_nondegenerate k ε)
        ⟨fiveGLIso k 1, fiveGLIso_mem_orthogonalGroup_of_mem
          (Subgroup.one_mem (Subgroup.closure (fiveReflections k ε π)))⟩ = 1 := by
      rw [h1, map_one]
    rw [hdet1]
    exact Subgroup.one_mem _
  · intro x y hx hy ihx ihy
    have hxy : (⟨fiveGLIso k (x * y),
        fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.mul_mem _ hx hy)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) =
        ⟨fiveGLIso k x, fiveGLIso_mem_orthogonalGroup_of_mem hx⟩ *
          ⟨fiveGLIso k y, fiveGLIso_mem_orthogonalGroup_of_mem hy⟩ := by
      apply Subtype.ext
      change fiveGLIso k (x * y) = fiveGLIso k x * fiveGLIso k y
      rw [map_mul]
    have hdet := congrArg (detSpinorNorm (fiveQ_nondegenerate k ε)) hxy
    rw [hdet, map_mul]
    exact Subgroup.mul_mem _ ihx ihy
  · intro x hx ihx
    have hxy : (⟨fiveGLIso k x⁻¹,
        fiveGLIso_mem_orthogonalGroup_of_mem (Subgroup.inv_mem _ hx)⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) =
        (⟨fiveGLIso k x, fiveGLIso_mem_orthogonalGroup_of_mem hx⟩)⁻¹ := by
      apply Subtype.ext
      change fiveGLIso k x⁻¹ = (fiveGLIso k x)⁻¹
      rw [map_inv]
    have hdet := congrArg (detSpinorNorm (fiveQ_nondegenerate k ε)) hxy
    rw [hdet, map_inv]
    exact Subgroup.inv_mem _ ihx

theorem fiveReflOf_not_mem_fiveReflectionGroup {k : ℕ} (hk : 4 ≤ k) (ε π : Bool)
    {v : Fin (k + 1) → ZMod 5} (hv : fiveForm k ε v v ≠ 0)
    (hsign : IsSquare (fiveForm k ε v v) ↔ (!π) = true) :
    fiveReflOf k ε v ∉ fiveReflectionGroup k ε π := by
  intro hmem
  let a : (ZMod 5)ˣ × Multiplicative (TauCeti.SquareClassGroup (ZMod 5)) :=
    ((-1 : (ZMod 5)ˣ), sqClass π)
  have ha2 : a * a = 1 := by
    refine Prod.ext ?_ ?_
    · apply Units.ext; simp [a]
    · change sqClass π * sqClass π = 1
      cases π with
      | true => rw [sqClass_true, one_mul]
      | false =>
        rw [sqClass_false]
        exact squareClassHom_mul_self _
  have hmemH := detSpinorNorm_mem_closure_pair (k := k) ε π hmem
  have hQv : fiveQ k ε v ≠ 0 := by rwa [fiveQ_apply]
  letI : Invertible (fiveQ k ε v) := invertibleOfNonzero hQv
  have hsub : (⟨fiveGLIso k (fiveReflOf k ε v),
      fiveGLIso_mem_orthogonalGroup_of_mem hmem⟩ :
      TauCeti.QuadraticMap.orthogonalGroup (fiveQ k ε)) = reflO k ε v := by
    apply Subtype.ext
    change fiveGLIso k (fiveReflOf k ε v) = reflect (fiveQ k ε) v
    rw [fiveGLIso_fiveReflOf]
    rfl
  have hval : detSpinorNorm (fiveQ_nondegenerate k ε)
      ⟨fiveGLIso k (fiveReflOf k ε v), fiveGLIso_mem_orthogonalGroup_of_mem hmem⟩ =
      ((-1 : (ZMod 5)ˣ), sqClass (!π)) := by
    rw [congrArg (detSpinorNorm (fiveQ_nondegenerate k ε)) hsub, detSpinorNorm_reflO]
    congr 1
    have hsign' : IsSquare (fiveQ k ε v) ↔ (!π) = true := by rwa [fiveQ_apply]
    exact squareClassHom_unitOfInvertible_eq_sqClass hsign'
  have hmem' : ((-1 : (ZMod 5)ˣ), sqClass (!π)) ∈
      Subgroup.closure ({((-1 : (ZMod 5)ˣ), sqClass π)} : Set _) := by
    rw [← hval]
    exact hmemH
  have hcases := eq_one_or_eq_or_eq_mul_of_mem_closure_pair (a := a) (b := a) ha2 ha2
    (by rw [ha2])
    (Subgroup.closure_mono (by rintro x rfl; simp [a]) hmem')
  have hne1 : (-1 : (ZMod 5)ˣ) ≠ 1 := by decide
  have hne2 : (!π) ≠ π := by cases π <;> simp
  rcases hcases with h | h | h | h
  · exact hne1 (congrArg Prod.fst h)
  · exact hne2 (sqClass_injective (congrArg Prod.snd h))
  · exact hne2 (sqClass_injective (congrArg Prod.snd h))
  · exact hne1 (congrArg Prod.fst (h.trans ha2))

end CFSG.OddTranspositions.PartThree
