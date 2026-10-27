module

public import CFSG.LocalAnalysis.StandardType.GGQTwoChartDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.ClassicalInvolution.Phan
open CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary
open scoped Pointwise Matrix
variable {G : Type} [Group G] [Finite G]
variable {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {m n : ℕ}

private theorem qTwoChartExtend_window (hm : 5 ≤ m) (hN : n = m ∨ (n = m + 1 ∧ 3 ∣ n + 1)) :
    n + 1 + 4 ≤ 2 * m := by
  rcases hN with h | ⟨h, hd⟩
  · subst n; omega
  · subst n; omega

private theorem qTwoChartExtend_core {N : ℕ} (hN : N + 4 ≤ 2 * m)
    {P P' I : Finset (Fin N)} (hP : P.card = m) (hP' : P'.card = m) (hI : I ⊆ P ∩ P')
    (hI4 : I.card ≤ 4) : ∃ I4 : Finset (Fin N), I ⊆ I4 ∧ I4 ⊆ P ∩ P' ∧ I4.card = 4 := by
  have hcard : 4 ≤ (P ∩ P').card := by
    have hunion : (P ∪ P').card ≤ N := by
      simpa using Finset.card_le_univ (P ∪ P')
    have hsum := Finset.card_union_add_card_inter P P'
    omega
  exact Finset.exists_subsuperset_card_eq hI hI4 hcard

theorem qTwoChart_extendFrame (S : QTwoChartSetting B Bs x L D J 𝒦 m n)
    (ε0 : Fin m ↪ Fin (n + 1))
    {π π' : Equiv.Perm (Fin (n + 1))} {J J' : Finset (Fin m)}
    (hJ'card : J'.card = J.card) (hJ4 : J.card ≤ 4)
    (hframe : qTwoFrameSet ε0 π J = qTwoFrameSet ε0 π' J') :
    ∃ Q Q' : Finset (Fin m), Q.card = 4 ∧ Q'.card = 4 ∧ J ⊆ Q ∧ J' ⊆ Q' ∧
      qTwoFrameSet ε0 π Q = qTwoFrameSet ε0 π' Q' := by
  classical
  set P : Finset (Fin (n + 1)) := qTwoFrameSet ε0 π Finset.univ with hPdef
  set P' : Finset (Fin (n + 1)) := qTwoFrameSet ε0 π' Finset.univ with hP'def
  set I : Finset (Fin (n + 1)) := qTwoFrameSet ε0 π J with hIdef
  have hPcard : P.card = m := by
    rw [hPdef, qTwoFrameSet, Finset.card_map, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hP'card : P'.card = m := by
    rw [hP'def, qTwoFrameSet, Finset.card_map, Finset.card_map, Finset.card_univ,
      Fintype.card_fin]
  have hIcard : I.card ≤ 4 := by
    rw [hIdef, qTwoFrameSet, Finset.card_map, Finset.card_map]
    exact hJ4
  have hIP : I ⊆ P := by
    rw [hIdef, hPdef, qTwoFrameSet, qTwoFrameSet]
    exact Finset.map_subset_map.2 (Finset.map_subset_map.2 (Finset.subset_univ J))
  have hIP' : I ⊆ P' := by
    rw [hframe, hP'def, qTwoFrameSet, qTwoFrameSet]
    exact Finset.map_subset_map.2 (Finset.map_subset_map.2 (Finset.subset_univ J'))
  have hIinter : I ⊆ P ∩ P' := fun y hy => Finset.mem_inter.2 ⟨hIP hy, hIP' hy⟩
  obtain ⟨I4, hII4, hI4sub, hI4card⟩ :=
    qTwoChartExtend_core (N := n + 1) (P := P) (P' := P') (I := I)
      (qTwoChartExtend_window S.hm S.hN) hPcard hP'card hIinter hIcard
  set Q : Finset (Fin m) := Finset.univ.filter (fun i => π (ε0 i) ∈ I4) with hQdef
  set Q' : Finset (Fin m) := Finset.univ.filter (fun i => π' (ε0 i) ∈ I4) with hQ'def
  have hQmem : ∀ i, i ∈ Q ↔ π (ε0 i) ∈ I4 := by
    intro i; rw [hQdef]; simp
  have hQ'mem : ∀ i, i ∈ Q' ↔ π' (ε0 i) ∈ I4 := by
    intro i; rw [hQ'def]; simp
  have hQframe : qTwoFrameSet ε0 π Q = I4 := by
    ext y
    rw [qTwoFrameSet]
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_map.1 hy
      obtain ⟨i, hi, hiz⟩ := Finset.mem_map.1 hz
      rw [Equiv.coe_toEmbedding] at hzy
      have hπi : π (ε0 i) ∈ I4 := (hQmem i).1 hi
      rw [hiz, hzy] at hπi
      exact hπi
    · intro hy
      have hyP : y ∈ P := (Finset.mem_inter.1 (hI4sub hy)).1
      rw [hPdef, qTwoFrameSet] at hyP
      obtain ⟨z, hz, hzy⟩ := Finset.mem_map.1 hyP
      obtain ⟨i, -, hiz⟩ := Finset.mem_map.1 hz
      rw [Equiv.coe_toEmbedding] at hzy
      refine Finset.mem_map.2 ⟨ε0 i, ?_, ?_⟩
      · refine Finset.mem_map.2 ⟨i, ?_, rfl⟩
        rw [hQmem i, hiz, hzy]
        exact hy
      · rw [Equiv.coe_toEmbedding, hiz, hzy]
  have hQ'frame : qTwoFrameSet ε0 π' Q' = I4 := by
    ext y
    rw [qTwoFrameSet]
    constructor
    · intro hy
      obtain ⟨z, hz, hzy⟩ := Finset.mem_map.1 hy
      obtain ⟨i, hi, hiz⟩ := Finset.mem_map.1 hz
      rw [Equiv.coe_toEmbedding] at hzy
      have hπi : π' (ε0 i) ∈ I4 := (hQ'mem i).1 hi
      rw [hiz, hzy] at hπi
      exact hπi
    · intro hy
      have hyP' : y ∈ P' := (Finset.mem_inter.1 (hI4sub hy)).2
      rw [hP'def, qTwoFrameSet] at hyP'
      obtain ⟨z, hz, hzy⟩ := Finset.mem_map.1 hyP'
      obtain ⟨i, -, hiz⟩ := Finset.mem_map.1 hz
      rw [Equiv.coe_toEmbedding] at hzy
      refine Finset.mem_map.2 ⟨ε0 i, ?_, ?_⟩
      · refine Finset.mem_map.2 ⟨i, ?_, rfl⟩
        rw [hQ'mem i, hiz, hzy]
        exact hy
      · rw [Equiv.coe_toEmbedding, hiz, hzy]
  have hQcard : Q.card = 4 := by
    have h := congrArg Finset.card hQframe
    rw [qTwoFrameSet, Finset.card_map, Finset.card_map, hI4card] at h
    exact h
  have hQ'card : Q'.card = 4 := by
    have h := congrArg Finset.card hQ'frame
    rw [qTwoFrameSet, Finset.card_map, Finset.card_map, hI4card] at h
    exact h
  have hJQ : J ⊆ Q := by
    intro j hj
    rw [hQmem j]
    apply hII4
    rw [hIdef, qTwoFrameSet]
    exact Finset.mem_map.2 ⟨ε0 j, Finset.mem_map.2 ⟨j, hj, rfl⟩, rfl⟩
  have hJ'Q' : J' ⊆ Q' := by
    intro j hj
    rw [hQ'mem j]
    apply hII4
    rw [hframe, qTwoFrameSet]
    exact Finset.mem_map.2 ⟨ε0 j, Finset.mem_map.2 ⟨j, hj, rfl⟩, rfl⟩
  exact ⟨Q, Q', hQcard, hQ'card, hJQ, hJ'Q', hQframe.trans hQ'frame.symm⟩

end CFSG.StandardType.QTwo

end
