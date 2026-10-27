module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDInputs
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedTits
import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.PhanDn.QTwo

section Labels

theorem reindex_label {m : ℕ} {ι : Type} (e' : Fin m ≃ ι) (i j : Fin m) :
    ((ggCoxeterMatrixD m).reindex e').M (e' i) (e' j) = ggCoxeterMatrixD m i j := by
  have h := CoxeterMatrix.reindex_apply (M := ggCoxeterMatrixD m) (e := e') (e' i) (e' j)
  simpa using h

theorem qtwo_label_two_or_three {m : ℕ} {ι : Type} {M : CoxeterMatrix ι} (e' : Fin m ≃ ι)
    (hM : M = (ggCoxeterMatrixD m).reindex e') :
    ∀ a b : ι, a ≠ b → M.M a b = 2 ∨ M.M a b = 3 := by
  intro a b hab
  obtain ⟨i, rfl⟩ := e'.surjective a
  obtain ⟨j, rfl⟩ := e'.surjective b
  have hij : i ≠ j := fun h => hab (by rw [h])
  rw [hM, reindex_label]
  exact ggCoxeterMatrixD_two_or_three i j hij

theorem qtwo_label_le_three {m : ℕ} {ι : Type} {M : CoxeterMatrix ι} (e' : Fin m ≃ ι)
    (hM : M = (ggCoxeterMatrixD m).reindex e') : ∀ a b : ι, a ≠ b → M.M a b ≤ 3 := by
  intro a b hab
  rcases qtwo_label_two_or_three e' hM a b hab with h | h <;> omega

theorem qtwo_simple_injective {ι : Type} (M : CoxeterMatrix ι) : Function.Injective M.simple := by
  intro a b h
  by_contra hne
  have h1 := M.toCoxeterSystem.orderOf_simple_mul_simple a b
  have h2 : M.simple a * M.simple b = 1 := by
    rw [← h]
    exact M.toCoxeterSystem.simple_mul_simple_self a
  have h3 : M.toCoxeterSystem.simple a * M.toCoxeterSystem.simple b = 1 := h2
  rw [h3, orderOf_one] at h1
  have := M.off_diagonal a b hne
  omega

end Labels

section Refl

variable {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
  {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) {m : ℕ} (e' : Fin m ≃ ι)

theorem conjRefl_mem_ggCoxRefl (w : M.Group) (t : Fin m) :
    ((e (w * M.simple (e' t) * w⁻¹) : ↥A) : MulAut ↥Bs) ∈ ggCoxRefl M e :=
  ⟨w, e' t, rfl⟩

theorem conjRefl_comm (hM : M = (ggCoxeterMatrixD m).reindex e') (w : M.Group) {i j : Fin m}
    (h : ggCoxeterMatrixD m i j = 2) :
    ((e (w * M.simple (e' i) * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple (e' j) * w⁻¹) : ↥A) : MulAut ↥Bs) =
      ((e (w * M.simple (e' j) * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple (e' i) * w⁻¹) : ↥A) : MulAut ↥Bs) := by
  refine ggCoxConj_comm e w (ggSimplyLaced_simple_comm ?_)
  rw [hM, reindex_label]
  exact h

theorem conjRefl_noncomm [Finite ι] (hM : M = (ggCoxeterMatrixD m).reindex e')
    (w : M.Group) {i j : Fin m} (h : ggCoxeterMatrixD m i j = 3) :
    ((e (w * M.simple (e' i) * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple (e' j) * w⁻¹) : ↥A) : MulAut ↥Bs) ≠
      ((e (w * M.simple (e' j) * w⁻¹) : ↥A) : MulAut ↥Bs) *
        ((e (w * M.simple (e' i) * w⁻¹) : ↥A) : MulAut ↥Bs) := by
  have hsl : GGSimplyLaced M := qtwo_label_two_or_three e' hM
  refine ggCoxConj_ne_comm e w (ggSimplyLaced_simple_noncomm hsl ?_)
  rw [hM, reindex_label]
  exact h

theorem conjRefl_ne (w : M.Group) {i j : Fin m} (hij : i ≠ j) :
    ((e (w * M.simple (e' i) * w⁻¹) : ↥A) : MulAut ↥Bs) ≠
      ((e (w * M.simple (e' j) * w⁻¹) : ↥A) : MulAut ↥Bs) := by
  intro h
  have h1 : e (w * M.simple (e' i) * w⁻¹) = e (w * M.simple (e' j) * w⁻¹) := Subtype.ext h
  have h2 := e.injective h1
  have h3 : M.simple (e' i) = M.simple (e' j) := by
    have := mul_left_cancel (mul_right_cancel h2)
    exact this
  exact hij (e'.injective (qtwo_simple_injective M h3))

end Refl

end CFSG.StandardType.QTwo

end
