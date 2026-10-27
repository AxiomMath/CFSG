module

public import CFSG.GroupTheory.GL52.Simple

public section

namespace CFSG.Quasithin.F7Two

open CFSG.GroupTheory.GL52 Matrix

@[expose] def elemM (i j : Fin 5) : M5 := 1 + Matrix.single i j 1

theorem elemM_mul_self : ∀ i j : Fin 5, i ≠ j → elemM i j * elemM i j = 1 := by decide +kernel

@[expose] def elem (i j : Fin 5) (h : i ≠ j) : G52 :=
  mk5 (elemM i j) (elemM i j) (elemM_mul_self i j h)

@[expose] def swpM (a b : Fin 5) : M5 := Matrix.of fun i j => if Equiv.swap a b j = i then 1 else 0

theorem swpM_mul_self : ∀ a b : Fin 5, swpM a b * swpM a b = 1 := by decide +kernel

@[expose] def swp (a b : Fin 5) : G52 := mk5 (swpM a b) (swpM a b) (swpM_mul_self a b)

theorem eq_top_of_elem_mem {S : Subgroup G52}
    (h : ∀ (i j : Fin 5) (hij : i ≠ j), elem i j hij ∈ S) : S = ⊤ := by
  have hc : ∀ {i j : Fin 5} (hij : i ≠ j) (c : ZMod 2),
      SpecialLinearGroup.transvection hij c ∈
        S.comap (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 5) (ZMod 2) →* G52) := by
    intro i j hij c
    rw [Subgroup.mem_comap]
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · have h0 : SpecialLinearGroup.transvection hij (0 : ZMod 2) = 1 :=
        Subtype.ext (by simp)
      rw [h0, map_one]
      exact S.one_mem
    · have e : (Matrix.SpecialLinearGroup.toGL (SpecialLinearGroup.transvection hij (1 : ZMod 2)) :
          G52) = elem i j hij :=
        Units.ext (by
          simp only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
            CFSG.LinearGroups.coe_transvection, elem, elemM, coe_mk5])
      rw [e]
      exact h i j hij
  have h1 : S.comap (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 5) (ZMod 2) →* G52)
      = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := ZMod 2),
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    exact hc hij c
  rw [eq_top_iff]
  intro g _
  obtain ⟨s, rfl⟩ := bijective_toGL_G52.2 g
  have : s ∈ S.comap
      (Matrix.SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 5) (ZMod 2) →* G52) :=
    h1 ▸ Subgroup.mem_top s
  exact this

theorem elem_mem_of_conj {S : Subgroup G52} {w : G52} (hw : w ∈ S) {i j i' j' : Fin 5}
    {h : i ≠ j} {h' : i' ≠ j'}
    (he : (w : M5) * elemM i' j' * ((w⁻¹ : G52) : M5) = elemM i j)
    (hm : elem i' j' h' ∈ S) : elem i j h ∈ S := by
  have : w * elem i' j' h' * w⁻¹ = elem i j h :=
    Units.ext (by simpa only [Units.val_mul, elem, coe_mk5] using he)
  rw [← this]
  exact S.mul_mem (S.mul_mem hw hm) (S.inv_mem hw)

end CFSG.Quasithin.F7Two
