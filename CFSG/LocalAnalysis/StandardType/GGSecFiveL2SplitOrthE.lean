module

public import Mathlib.GroupTheory.Coxeter.Basic
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthEMoves

public section

namespace CFSG.StandardType

private theorem orthE_conj_of_table {ι : Type} {n : ℕ} {N : CoxeterMatrix (Fin n)}
    {e : Fin n ≃ ι} (hW : GGIsWeylMatrix (N.reindex e)) (f : Fin n → Fin n → ℕ)
    (hf : ∀ x y, N.M x y = f x y) (h3 : ∀ x y, x ≠ y → f x y ≤ 3)
    (a₀ b₀ : Fin n) (p q : Fin n → Fin n → Fin n) (rk : Fin n → Fin n → ℕ)
    (htab : ∀ a b, f a b = 2 → (a = a₀ ∧ b = b₀) ∨
      (f (p a b) (q a b) = 2 ∧ rk (p a b) (q a b) < rk a b ∧
        ((p a b = a ∧ f (q a b) b = 3) ∨ (q a b = b ∧ f (p a b) a = 3) ∨
          (p a b = b ∧ q a b = a ∧ ∃ x, f a x = 3 ∧ f b x = 3))))
    {t t' : (N.reindex e).Group}
    (ht : ∃ (w : (N.reindex e).Group) (i : ι), t = w * (N.reindex e).simple i * w⁻¹)
    (ht' : ∃ (w : (N.reindex e).Group) (i : ι), t' = w * (N.reindex e).simple i * w⁻¹)
    (hne : t ≠ t') (hcomm : t * t' = t' * t) {i j : ι} (h2 : (N.reindex e).M i j = 2) :
    ∃ w : (N.reindex e).Group, w * (N.reindex e).simple i * w⁻¹ = t ∧
      w * (N.reindex e).simple j * w⁻¹ = t' := by
  refine ggOrth_conj_of_simplePair hW
    (fun x y hxy => (hf _ _).trans_le (h3 (e.symm x) (e.symm y) (e.symm.injective.ne hxy)))
    (a₀ := e a₀) (b₀ := e b₀) (fun a b hab => ?_) ht ht' hne hcomm h2
  obtain ⟨w, hw₁, hw₂⟩ := ggSimplePair_conj_of_table (M := N.reindex e) e f
    (fun x y => by simp only [CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, hf]) a₀ b₀ p q
    rk htab (a := e.symm a) (b := e.symm b) ((hf _ _).symm.trans hab)
  simp only [Equiv.apply_symm_apply] at hw₁ hw₂
  exact ⟨w, hw₁, hw₂⟩

private def orthE6f : Fin 6 → Fin 6 → ℕ := fun x y => CoxeterMatrix.E₆.M x y

private def orthE6p : Fin 6 → Fin 6 → Fin 6 :=
  ![![0, 0, 0, 0, 0, 0], ![3, 0, 2, 0, 1, 3], ![0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 2],
    ![3, 1, 2, 0, 0, 0], ![4, 5, 4, 3, 0, 0]]

private def orthE6q : Fin 6 → Fin 6 → Fin 6 :=
  ![![0, 1, 0, 1, 3, 4], ![0, 0, 1, 0, 5, 5], ![0, 1, 0, 0, 4, 5], ![3, 0, 0, 0, 0, 5],
    ![0, 4, 4, 0, 0, 0], ![0, 3, 2, 5, 0, 0]]

private def orthE6rk : Fin 6 → Fin 6 → ℕ :=
  ![![0, 0, 0, 1, 2, 3], ![3, 0, 2, 0, 7, 6], ![0, 1, 0, 0, 3, 4], ![2, 0, 0, 0, 0, 5],
    ![3, 8, 4, 0, 0, 0], ![4, 7, 5, 6, 0, 0]]

theorem ggOrth_conj_E6 {ι : Type} {M : CoxeterMatrix ι} {e : Fin 6 ≃ ι}
    (hM : M = CoxeterMatrix.E₆.reindex e) {t t' : M.Group}
    (ht : ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (ht' : ∃ (w : M.Group) (i : ι), t' = w * M.simple i * w⁻¹) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) {i j : ι} (h2 : M.M i j = 2) :
    ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t' := by
  subst hM
  exact orthE_conj_of_table (Or.inr (Or.inl ⟨e, rfl⟩)) orthE6f
    (fun _ _ => rfl) (by decide +kernel) 0 1 orthE6p orthE6q orthE6rk (by decide +kernel) ht ht'
    hne hcomm h2

private def orthE7f : Fin 7 → Fin 7 → ℕ := fun x y => CoxeterMatrix.E₇.M x y

private def orthE7p : Fin 7 → Fin 7 → Fin 7 :=
  ![![0, 0, 0, 0, 0, 0, 0], ![3, 0, 2, 0, 1, 3, 3], ![0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 2, 2],
    ![3, 1, 2, 0, 0, 0, 3], ![4, 5, 4, 3, 0, 0, 0], ![5, 5, 5, 5, 4, 0, 0]]

private def orthE7q : Fin 7 → Fin 7 → Fin 7 :=
  ![![0, 1, 0, 1, 3, 4, 5], ![0, 0, 1, 0, 5, 5, 6], ![0, 1, 0, 0, 4, 5, 6], ![3, 0, 0, 0, 0, 5, 6],
    ![0, 4, 4, 0, 0, 0, 6], ![0, 3, 2, 5, 0, 0, 0], ![0, 1, 2, 3, 6, 0, 0]]

private def orthE7rk : Fin 7 → Fin 7 → ℕ :=
  ![![0, 0, 0, 1, 2, 3, 4], ![3, 0, 2, 0, 7, 6, 7], ![0, 1, 0, 0, 3, 4, 5], ![2, 0, 0, 0, 0, 5, 6],
    ![3, 8, 4, 0, 0, 0, 7], ![4, 7, 5, 6, 0, 0, 0], ![5, 8, 6, 7, 8, 0, 0]]

theorem ggOrth_conj_E7 {ι : Type} {M : CoxeterMatrix ι} {e : Fin 7 ≃ ι}
    (hM : M = CoxeterMatrix.E₇.reindex e) {t t' : M.Group}
    (ht : ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (ht' : ∃ (w : M.Group) (i : ι), t' = w * M.simple i * w⁻¹) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) {i j : ι} (h2 : M.M i j = 2) :
    ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t' := by
  subst hM
  exact orthE_conj_of_table (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩))) orthE7f
    (fun _ _ => rfl) (by decide +kernel) 0 1 orthE7p orthE7q orthE7rk (by decide +kernel) ht ht'
    hne hcomm h2

private def orthE8f : Fin 8 → Fin 8 → ℕ := fun x y => CoxeterMatrix.E₈.M x y

private def orthE8p : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![3, 0, 2, 0, 1, 3, 3, 3], ![0, 0, 0, 0, 0, 0, 0, 0],
    ![0, 0, 0, 0, 0, 2, 2, 2], ![3, 1, 2, 0, 0, 0, 3, 3], ![4, 5, 4, 3, 0, 0, 0, 4],
    ![5, 5, 5, 5, 4, 0, 0, 0], ![6, 6, 6, 6, 6, 5, 0, 0]]

private def orthE8q : Fin 8 → Fin 8 → Fin 8 :=
  ![![0, 1, 0, 1, 3, 4, 5, 6], ![0, 0, 1, 0, 5, 5, 6, 7], ![0, 1, 0, 0, 4, 5, 6, 7],
    ![3, 0, 0, 0, 0, 5, 6, 7], ![0, 4, 4, 0, 0, 0, 6, 7], ![0, 3, 2, 5, 0, 0, 0, 7],
    ![0, 1, 2, 3, 6, 0, 0, 0], ![0, 1, 2, 3, 4, 7, 0, 0]]

private def orthE8rk : Fin 8 → Fin 8 → ℕ :=
  ![![0, 0, 0, 1, 2, 3, 4, 5], ![3, 0, 2, 0, 7, 6, 7, 8], ![0, 1, 0, 0, 3, 4, 5, 6],
    ![2, 0, 0, 0, 0, 5, 6, 7], ![3, 8, 4, 0, 0, 0, 7, 8], ![4, 7, 5, 6, 0, 0, 0, 9],
    ![5, 8, 6, 7, 8, 0, 0, 0], ![6, 9, 7, 8, 9, 10, 0, 0]]

theorem ggOrth_conj_E8 {ι : Type} {M : CoxeterMatrix ι} {e : Fin 8 ≃ ι}
    (hM : M = CoxeterMatrix.E₈.reindex e) {t t' : M.Group}
    (ht : ∃ (w : M.Group) (i : ι), t = w * M.simple i * w⁻¹)
    (ht' : ∃ (w : M.Group) (i : ι), t' = w * M.simple i * w⁻¹) (hne : t ≠ t')
    (hcomm : t * t' = t' * t) {i j : ι} (h2 : M.M i j = 2) :
    ∃ w : M.Group, w * M.simple i * w⁻¹ = t ∧ w * M.simple j * w⁻¹ = t' := by
  subst hM
  exact orthE_conj_of_table (Or.inr (Or.inr (Or.inr (Or.inl ⟨e, rfl⟩)))) orthE8f
    (fun _ _ => rfl) (by decide +kernel) 0 1 orthE8p orthE8q orthE8rk (by decide +kernel) ht ht'
    hne hcomm h2

end CFSG.StandardType

end
