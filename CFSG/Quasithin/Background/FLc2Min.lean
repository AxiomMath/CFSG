module

public import CFSG.Quasithin.Background.FLcR2Mat

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

@[expose] def NodesNe (n a : ℕ) : Set ℕ := {j | 1 ≤ j ∧ j < n ∧ j ≠ a}

theorem isNode_of_mem_NodesNe {n a j : ℕ} (h : j ∈ NodesNe n a) : IsNode n j := ⟨h.1, h.2.1⟩

theorem exists_node_of_minimal {n : ℕ} {J : Subgroup (SLt n)} (hUJ : Ut n ≤ J) (hne : J ≠ Ut n)
    (hmin : ∀ K : Subgroup (SLt n), Ut n ≤ K → K ≤ J → K = Ut n ∨ K = J) :
    ∃ a, IsNode n a ∧ J = QI n (NodesNe n a) := by
  set I := cuts J with hI
  have hJI : J = QI n I := eq_QI_cuts hUJ
  have hnode : ∀ i ∈ I, IsNode n i := fun i hi => isNode_of_mem_cuts hi
  have hmiss : ∃ a, IsNode n a ∧ a ∉ I := by
    by_contra hall
    push Not at hall
    apply hne
    have : cuts J = cuts (Ut n) := by
      rw [cuts_Ut]
      exact Set.Subset.antisymm hnode fun i hi => hall i hi
    exact eq_of_cuts_eq hUJ le_rfl this
  obtain ⟨a, ha, haI⟩ := hmiss
  refine ⟨a, ha, ?_⟩
  have hI' : I = NodesNe n a := by
    ext i
    constructor
    · intro hi
      have hin := hnode i hi
      refine ⟨hin.1, hin.2, fun h => haI (h ▸ hi)⟩
    · intro hi
      by_contra hiI
      have hin : IsNode n i := ⟨hi.1, hi.2.1⟩
      have hia : i ≠ a := hi.2.2
      have hIa : ∀ j ∈ insert a I, IsNode n j := by
        intro j hj
        rcases hj with rfl | hj
        · exact ha
        · exact hnode j hj
      set K := QI n (insert a I) with hK
      have hUK : Ut n ≤ K := Ut_le_QI n _
      have hKJ : K ≤ J := by
        rw [hJI]
        exact (QI_le_QI_iff hnode).2 (Set.subset_insert _ _)
      have hcK : cuts K = insert a I := cuts_QI hIa
      rcases hmin K hUK hKJ with h | h
      · have : cuts K = cuts (Ut n) := by rw [h]
        rw [hcK, cuts_Ut] at this
        have hi' : i ∈ insert a I := by rw [this]; exact hin
        rcases hi' with rfl | hi'
        · exact hia rfl
        · exact hiI hi'
      · have : cuts K = cuts J := by rw [h]
        rw [hcK] at this
        have : a ∈ cuts J := by rw [← this]; exact Set.mem_insert _ _
        exact haI this
  rw [hJI, hI']

theorem minimal_of_node {n a : ℕ} (ha : IsNode n a) :
    QI n (NodesNe n a) ≠ Ut n ∧ ∀ K : Subgroup (SLt n), Ut n ≤ K → K ≤ QI n (NodesNe n a) →
      K = Ut n ∨ K = QI n (NodesNe n a) := by
  have hNe : ∀ j ∈ NodesNe n a, IsNode n j := fun j hj => isNode_of_mem_NodesNe hj
  refine ⟨fun h => ?_, fun K hUK hKJ => ?_⟩
  · have h1 : reflection n (ZMod 2) a ha.1 ha.2 ∈ QI n (NodesNe n a) :=
      (reflection_mem_QI ha).2 fun h => h.2.2 rfl
    rw [h, Ut_eq_QI] at h1
    exact ((reflection_mem_QI ha).1 h1) ha
  · have hKc : K = QI n (cuts K) := eq_QI_cuts hUK
    have hsub : NodesNe n a ⊆ cuts K := by
      have := (le_iff_cuts hUK (Ut_le_QI n (NodesNe n a))).1 hKJ
      rwa [cuts_QI hNe] at this
    by_cases haK : a ∈ cuts K
    · left
      have : cuts K = cuts (Ut n) := by
        rw [cuts_Ut]
        ext i
        constructor
        · exact fun hi => isNode_of_mem_cuts hi
        · intro hi
          by_cases hia : i = a
          · rw [hia]; exact haK
          · exact hsub ⟨hi.1, hi.2, hia⟩
      exact eq_of_cuts_eq hUK le_rfl this
    · right
      have : cuts K = NodesNe n a := by
        refine Set.Subset.antisymm (fun i hi => ?_) hsub
        have hin := isNode_of_mem_cuts hi
        refine ⟨hin.1, hin.2, fun h => haK (h ▸ hi)⟩
      rw [hKc, this]

theorem pow_six_mem_Ut {n : ℕ} (hn : 4 ≤ n) {g : SLt n} (hg : g ∈ QI n (NodesNe n 2)) :
    g ^ 6 ∈ Ut n := by
  have hg' : g ∈ Qn n 2 := hg
  have hP : (⟨1, by omega⟩ : Fin n).val + 1 = 2 := rfl
  have hQ : (⟨2, by omega⟩ : Fin n).val = 2 := rfl
  have hne : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h1 := blk_mul_Qn (i := 2) (by norm_num) (by omega) hP hQ hg' ((Qn n 2).inv_mem hg')
  rw [mul_inv_cancel, blk_one hne] at h1
  refine mem_Ut_of_blk_one (i := 2) (by norm_num) (by omega) hP hQ ((Qn n 2).pow_mem hg' 6) ?_
  rw [blk_pow_Qn (i := 2) (by norm_num) (by omega) hP hQ hg' 6]
  exact gl2_pow_six _ _ h1.symm

end CFSG.Quasithin.FLc
