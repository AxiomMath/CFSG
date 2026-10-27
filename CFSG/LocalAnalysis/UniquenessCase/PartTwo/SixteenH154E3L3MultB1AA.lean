module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultB1AAA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

@[expose] def s16h_IsMinLeftInvMat (I : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2))) : Prop :=
  I ≠ ⊥ ∧
    (∀ (g : GL (Fin 3) (ZMod 2)), ∀ m ∈ I, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m ∈ I) ∧
    ∀ J : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)), J ≤ I →
      (∀ (g : GL (Fin 3) (ZMod 2)), ∀ m ∈ J, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * m ∈ J) →
        J = ⊥ ∨ J = I

private theorem s16h_l3RowSub_isMin {r : s16h_l3Vec} (hr : r ≠ 0) :
    s16h_IsMinLeftInvMat (s16h_l3RowSub (Submodule.span (ZMod 2) {r})) := by
  refine ⟨s16h_l3RowSub_ne_bot hr, ?_, ?_⟩
  · intro g m hm
    exact s16h_l3RowSub_invariant (Submodule.span (ZMod 2) {r}) g m hm
  · intro J hJ hJinv
    by_cases hbot : J = ⊥
    · exact Or.inl hbot
    · right
      obtain ⟨m, hmJ, hmne⟩ : ∃ m ∈ J, m ≠ 0 := by
        by_contra h
        apply hbot
        rw [AddSubgroup.eq_bot_iff_forall]
        intro x hx
        by_contra hxne
        exact h ⟨x, hx, hxne⟩
      have hrowspace_le : s16h_l3RowSpace m ≤ Submodule.span (ZMod 2) {r} := by
        change Submodule.span (ZMod 2) (Set.range m) ≤ Submodule.span (ZMod 2) {r}
        rw [Submodule.span_le]
        rintro v ⟨i, rfl⟩
        exact (s16h_l3RowSub_mem.mp (hJ hmJ)) i
      have hrowne : s16h_l3RowSpace m ≠ ⊥ := s16h_l3RowSpace_ne_bot hmne
      have hEq : s16h_l3RowSpace m = Submodule.span (ZMod 2) {r} :=
        s16h_l3SpanSingleton_eq_of_le hr hrowspace_le hrowne
      have hle : s16h_l3RowSub (s16h_l3RowSpace m) ≤ J := by
        rw [s16h_l3RowSub_eq_closure_orbit]
        apply (AddSubgroup.closure_le _).mpr
        rintro x ⟨g, rfl⟩
        exact hJinv g m hmJ
      have hJle : J ≤ s16h_l3RowSub (s16h_l3RowSpace m) := by
        rw [hEq]
        exact hJ
      have hfin : s16h_l3RowSub (s16h_l3RowSpace m) =
          s16h_l3RowSub (Submodule.span (ZMod 2) {r}) := by
        rw [hEq]
      rw [← hfin]
      exact le_antisymm hJle hle

private theorem s16h_l3_min_exists_rowSub (I : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hI : s16h_IsMinLeftInvMat I) :
    ∃ r : s16h_l3Vec, r ≠ 0 ∧ I = s16h_l3RowSub (Submodule.span (ZMod 2) {r}) := by
  obtain ⟨hne, hinv, hmin⟩ := hI
  obtain ⟨m, hmI, hmne⟩ : ∃ m ∈ I, m ≠ 0 := by
    by_contra h
    apply hne
    rw [AddSubgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hxne
    exact h ⟨x, hx, hxne⟩
  have hIeq : I = s16h_l3RowSub (s16h_l3RowSpace m) := by
    have hle : s16h_l3RowSub (s16h_l3RowSpace m) ≤ I := by
      rw [s16h_l3RowSub_eq_closure_orbit]
      apply (AddSubgroup.closure_le _).mpr
      rintro x ⟨g, rfl⟩
      exact hinv g m hmI
    have hInv2 : ∀ (g : GL (Fin 3) (ZMod 2)),
        ∀ x ∈ s16h_l3RowSub (s16h_l3RowSpace m),
          (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x ∈ s16h_l3RowSub (s16h_l3RowSpace m) :=
      s16h_l3RowSub_invariant (s16h_l3RowSpace m)
    have hne2 : s16h_l3RowSub (s16h_l3RowSpace m) ≠ ⊥ := by
      intro hbot
      have : m ∈ (⊥ : AddSubgroup s16h_l3Mat) := by
        rw [← hbot, s16h_l3RowSub_mem]
        intro i
        exact Submodule.subset_span (Set.mem_range_self i)
      exact hmne (by simpa using this)
    rcases hmin (s16h_l3RowSub (s16h_l3RowSpace m)) hle hInv2 with h | h
    · exact absurd h hne2
    · exact h.symm
  obtain ⟨j, hj⟩ : ∃ j : Fin 3, m j ≠ 0 := by
    by_contra h
    apply hmne
    funext i
    by_contra hmi
    exact h ⟨i, hmi⟩
  refine ⟨m j, hj, ?_⟩
  have hle : s16h_l3RowSub (Submodule.span (ZMod 2) {m j}) ≤ I := by
    rw [hIeq]
    exact s16h_l3RowSub_mono (by
      rw [Submodule.span_le]
      rintro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Submodule.subset_span (Set.mem_range_self j))
  have hInv : ∀ (g : GL (Fin 3) (ZMod 2)),
      ∀ x ∈ s16h_l3RowSub (Submodule.span (ZMod 2) {m j}),
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) * x ∈
          s16h_l3RowSub (Submodule.span (ZMod 2) {m j}) :=
    s16h_l3RowSub_invariant (Submodule.span (ZMod 2) {m j})
  rcases hmin (s16h_l3RowSub (Submodule.span (ZMod 2) {m j})) hle hInv with h | h
  · exact absurd h (s16h_l3RowSub_ne_bot hj)
  · exact h.symm

private noncomputable def s16h_l3MinEquivNonzero :
    {I : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) // s16h_IsMinLeftInvMat I} ≃
      {r : s16h_l3Vec // r ≠ 0} where
  toFun I :=
    ⟨Classical.choose (s16h_l3_min_exists_rowSub I.1 I.2),
      (Classical.choose_spec (s16h_l3_min_exists_rowSub I.1 I.2)).1⟩
  invFun r :=
    ⟨s16h_l3RowSub (Submodule.span (ZMod 2) {r.1}), s16h_l3RowSub_isMin r.2⟩
  left_inv I := by
    apply Subtype.ext
    exact (Classical.choose_spec (s16h_l3_min_exists_rowSub I.1 I.2)).2.symm
  right_inv r := by
    apply Subtype.ext
    have hspec := (Classical.choose_spec
      (s16h_l3_min_exists_rowSub (s16h_l3RowSub (Submodule.span (ZMod 2) {r.1}))
        (s16h_l3RowSub_isMin r.2))).2
    have hchoose := (Classical.choose_spec
      (s16h_l3_min_exists_rowSub (s16h_l3RowSub (Submodule.span (ZMod 2) {r.1}))
        (s16h_l3RowSub_isMin r.2))).1
    exact (s16h_l3RowSub_injective r.2 hchoose hspec).symm

theorem s16h_e3_gl3_minimal_left_invariant_card :
    Nat.card {I : AddSubgroup (Matrix (Fin 3) (Fin 3) (ZMod 2)) // s16h_IsMinLeftInvMat I} = 7 := by
  rw [Nat.card_congr s16h_l3MinEquivNonzero]
  exact s16h_l3Vec_nonzero_card

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
