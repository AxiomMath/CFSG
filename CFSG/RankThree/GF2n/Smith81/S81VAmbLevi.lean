module

public import CFSG.RankThree.GF2n.Smith81.S81VBlockU

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [CharP F 2] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F}

private theorem gu1b_levi_smul_a (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b)
    (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (hdet : σ A.det = A.det) (j : Fin 3) :
    levi hσ hf A hA hdet • a j = ∑ i, A i j • a i := by
  have h := smul_fam hσ hf (levi hσ hf A hA hdet) (Sum.inl j)
  rw [gm_levi hσ hf A hA hdet, Fintype.sum_sum_type] at h
  simpa [fam] using h

private theorem gu1b_exists_det_one_cols (x : Fin 2 → Fin 3 → F) (hx : LinearIndependent F x) :
    ∃ A : Matrix (Fin 3) (Fin 3) F, A.det = 1 ∧ (fun i => A i 1) = x 0 ∧ (fun i => A i 2) = x 1 := by
  have hfin : Module.finrank F (Submodule.span F (Set.range x)) = 2 := by
    rw [finrank_span_eq_card hx, Fintype.card_fin]
  have hne : Submodule.span F (Set.range x) ≠ ⊤ := by
    intro h
    have h3 : Module.finrank F (Submodule.span F (Set.range x)) =
        Module.finrank F (⊤ : Submodule F (Fin 3 → F)) := by
      rw [h]
    rw [finrank_top, hfin] at h3
    simp at h3
  obtain ⟨u₀, -, hu₀⟩ := SetLike.exists_of_lt (lt_of_le_of_ne le_top hne)
  have hxv : (![x 0, x 1] : Fin 2 → Fin 3 → F) = x := by
    funext i
    fin_cases i <;> rfl
  have hvli : LinearIndependent F (![u₀, x 0, x 1] : Fin 3 → Fin 3 → F) := by
    rw [show (![u₀, x 0, x 1] : Fin 3 → Fin 3 → F) =
      (Fin.cons u₀ ![x 0, x 1] : Fin 3 → Fin 3 → F) from rfl,
      linearIndependent_finCons, hxv]
    exact ⟨hx, hu₀⟩
  obtain ⟨A₀, hA₀⟩ : ∃ A₀ : Matrix (Fin 3) (Fin 3) F,
      A₀ = Matrix.of fun i j => ![u₀, x 0, x 1] j i := ⟨_, rfl⟩
  have hunit : IsUnit A₀ := by
    rw [hA₀]
    exact Matrix.linearIndependent_cols_iff_isUnit.1 hvli
  have hd : A₀.det ≠ 0 := isUnit_iff_ne_zero.1 ((Matrix.isUnit_iff_isUnit_det _).1 hunit)
  have hc1 : ∀ i, A₀ i 1 = x 0 i := by
    intro i
    subst hA₀
    rfl
  have hc2 : ∀ i, A₀ i 2 = x 1 i := by
    intro i
    subst hA₀
    rfl
  refine ⟨A₀.updateCol 0 ((A₀.det)⁻¹ • fun i => A₀ i 0), ?_, ?_, ?_⟩
  · rw [Matrix.det_updateCol_smul, Matrix.updateCol_eq_self, inv_mul_cancel₀ hd]
  · funext i
    rw [Matrix.updateCol_ne (show (1 : Fin 3) ≠ 0 by decide), hc1 i]
  · funext i
    rw [Matrix.updateCol_ne (show (2 : Fin 3) ≠ 0 by decide), hc2 i]

theorem exists_levi_H₀ (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) {H' : Submodule F (Fin 6 → F)}
    (hH'le : H' ≤ Wa a) (hH'3 : finrank F H' = 2) :
    ∃ (A : Matrix (Fin 3) (Fin 3) F) (hA : A.det ≠ 0) (hdet : σ A.det = A.det),
      (Submodule.span F {a 1, a 2}).map (gLin (levi hσ hf A hA hdet)) = H' := by
  have hWa : Wa a = LinearMap.range (Fintype.linearCombination F a) := by
    unfold Wa
    rw [Fintype.range_linearCombination]
  have hrange : H' ≤ LinearMap.range (Fintype.linearCombination F a) := hH'le.trans hWa.le
  obtain ⟨b'⟩ : Nonempty (Basis (Fin 2) F H') := ⟨Module.finBasisOfFinrankEq F H' hH'3⟩
  choose x hx using fun i : Fin 2 => LinearMap.mem_range.1 (hrange (b' i).2)
  have hbli : LinearIndependent F (fun i => (b' i : Fin 6 → F)) :=
    b'.linearIndependent.map' H'.subtype (Submodule.ker_subtype H')
  have hxli : LinearIndependent F x := by
    refine LinearIndependent.of_comp (Fintype.linearCombination F a) ?_
    have e : ⇑(Fintype.linearCombination F a) ∘ x = fun i => (b' i : Fin 6 → F) := funext hx
    rw [e]
    exact hbli
  have hli' : LinearIndependent F (fun i => Fintype.linearCombination F a (x i)) := by
    have e : (fun i => Fintype.linearCombination F a (x i)) = fun i => (b' i : Fin 6 → F) :=
      funext hx
    rw [e]
    exact hbli
  have hspan : Submodule.span F (Set.range fun i => Fintype.linearCombination F a (x i)) = H' := by
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · refine Submodule.span_le.2 ?_
      rintro _ ⟨i, rfl⟩
      show Fintype.linearCombination F a (x i) ∈ H'
      rw [hx i]
      exact (b' i).2
    · rw [finrank_span_eq_card hli', Fintype.card_fin, hH'3]
  obtain ⟨A, hAdet, hA1, hA2⟩ := gu1b_exists_det_one_cols x hxli
  have hA : A.det ≠ 0 := by
    rw [hAdet]
    exact one_ne_zero
  have hdet : σ A.det = A.det := by
    rw [hAdet, map_one]
  refine ⟨A, hA, hdet, ?_⟩
  have e1 : gLin (levi hσ hf A hA hdet) (a 1) = Fintype.linearCombination F a (x 0) := by
    rw [gLin_apply, gu1b_levi_smul_a, ← hA1, Fintype.linearCombination_apply]
  have e2 : gLin (levi hσ hf A hA hdet) (a 2) = Fintype.linearCombination F a (x 1) := by
    rw [gLin_apply, gu1b_levi_smul_a, ← hA2, Fintype.linearCombination_apply]
  have hset : ({Fintype.linearCombination F a (x 0), Fintype.linearCombination F a (x 1)} :
      Set (Fin 6 → F)) = Set.range fun i : Fin 2 => Fintype.linearCombination F a (x i) := by
    ext y
    constructor
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  rw [Submodule.map_span, Set.image_pair, e1, e2, hset, hspan]

end CFSG.RankThree.GF2n.Smith81.S81V
