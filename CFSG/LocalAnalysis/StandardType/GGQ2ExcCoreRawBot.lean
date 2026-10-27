module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcRaw

public section

namespace CFSG.StandardType.GGQ2Frame

namespace ExcRaw

private def excParentTab (m : Fin 6) : List ℕ :=
  match m.val with
  | 0 => [0, 0, 1, 5, 1, 0, 0, 0, 0, 0, 0, 1, 7, 5, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0]
  | 1 => [0, 5, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 2, 0, 0, 0, 0, 0, 2, 5, 6, 0]
  | 2 => [0, 9, 0, 2, 12, 9, 9, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 9, 14, 2, 0, 0]
  | 3 => [0, 9, 0, 2, 12, 9, 9, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 9, 14, 2, 0, 0]
  | 4 => [0, 13, 0, 2, 16, 13, 13, 16, 19, 2, 13, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 13, 2, 2, 18, 16, 13, 13, 16, 2, 13, 18, 2, 0, 0, 0, 0, 0, 0, 2, 0]
  | _ => [0, 17, 0, 2, 20, 17, 17, 34, 17, 20, 23, 20, 23, 2, 17, 2, 2, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 17, 2, 2, 2, 22, 20, 17, 17, 20, 17, 17, 20, 2, 17, 22, 17, 2, 20, 17, 17, 20, 2, 0, 2, 2, 0, 2, 0, 22, 2, 0, 22, 17, 20, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 23, 20, 17, 34, 38, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 2, 0]

private def excDepthTab (m : Fin 6) : List ℕ :=
  match m.val with
  | 0 => [0, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1]
  | 1 => [0, 2, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1]
  | 2 => [0, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1]
  | 3 => [0, 2, 1, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 1, 1]
  | 4 => [0, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1]
  | _ => [0, 2, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1]

private def excParent (m : Fin 6) (i : ℕ) : ℕ := (excParentTab m).getD i 0

private def excDepth (m : Fin 6) (i : ℕ) : ℕ := (excDepthTab m).getD i 0

private def excPairingN (m : Fin 6) (i j : ℕ) : ℤ :=
  if m.val = 3 then
    ∑ k : Fin 6, ((tabF 2).getD i []).getD k 0 * ((tabH 2).getD j []).getD k 0
  else ∑ k : Fin (dim m), ((tabF m).getD i []).getD k 0 * ((tabH m).getD j []).getD k 0

private theorem excParentSpec (m : Fin 6) :
    ∀ i : Fin (nroots m), i.val = 0 ∨
      (excParent m i.val < nroots m ∧
        excDepth m (excParent m i.val) < excDepth m i.val ∧
        (excPairingN m i.val (excParent m i.val) ≠ 0 ∨
          excPairingN m (excParent m i.val) i.val ≠ 0)) := by
  fin_cases m <;> decide +kernel

private theorem excNroots_pos (m : Fin 6) : 0 < nroots m := by
  fin_cases m <;> decide

private theorem excAdjN_iff (m : Fin 6) (i j : ℕ) (hi : i < nroots m) (hj : j < nroots m) :
    (excPairingN m i j ≠ 0 ∨ excPairingN m j i ≠ 0) ↔ Adj m ⟨i, hi⟩ ⟨j, hj⟩ := by
  simp only [Adj, excPairingN, pairing, F, H]

private theorem excAdj_comm (m : Fin 6) (i j : Root m) : Adj m i j → Adj m j i := by
  intro h
  simpa only [Adj, or_comm] using h

private theorem excVanish_bot (m : Fin 6) (i : Root m) : Vanish m ⊥ i := by
  intro u hu
  rw [Submodule.mem_bot] at hu
  subst hu
  exact map_zero _

private theorem excConnected (m : Fin 6) (T : Finset (Root m)) (hne : T.Nonempty)
    (hcl : ∀ i ∈ T, ∀ j, Adj m i j → j ∈ T) : T = Finset.univ := by
  have h0 : (⟨0, excNroots_pos m⟩ : Fin (nroots m)) ∈ T := by
    obtain ⟨t, ht⟩ := hne
    have key : ∀ d, ∀ i : Fin (nroots m), i ∈ T → excDepth m i.val = d →
        (⟨0, excNroots_pos m⟩ : Fin (nroots m)) ∈ T := by
      intro d
      exact Nat.strong_induction_on d fun d ih i hi hdi => by
        by_cases hiz : i.val = 0
        · have hieq : i = ⟨0, excNroots_pos m⟩ := Fin.ext (by simpa using hiz)
          simpa [hieq] using hi
        · obtain ⟨hp, hlt, hadj⟩ := (excParentSpec m i).resolve_left hiz
          let p : Fin (nroots m) := ⟨excParent m i.val, hp⟩
          have hpmem : p ∈ T :=
            hcl i hi p ((excAdjN_iff m i.val p.val i.isLt p.isLt).1 hadj)
          have hlt' : excDepth m p.val < d := by
            simp only [p]
            omega
          exact ih (excDepth m p.val) hlt' p hpmem rfl
    exact key (excDepth m t.val) t ht rfl
  have hall : ∀ i : Fin (nroots m), i ∈ T := by
    intro i
    have key : ∀ d, ∀ i : Fin (nroots m), excDepth m i.val = d → i ∈ T := by
      intro d
      exact Nat.strong_induction_on d fun d ih i hdi => by
        by_cases hiz : i.val = 0
        · have hieq : i = ⟨0, excNroots_pos m⟩ := Fin.ext (by simpa using hiz)
          simpa [hieq] using h0
        · obtain ⟨hp, hlt, hadj⟩ := (excParentSpec m i).resolve_left hiz
          let p : Fin (nroots m) := ⟨excParent m i.val, hp⟩
          have hlt' : excDepth m p.val < d := by
            simp only [p]
            omega
          have hpmem : p ∈ T := ih (excDepth m p.val) hlt' p rfl
          have hadj' : Adj m i p := (excAdjN_iff m i.val p.val i.isLt p.isLt).1 hadj
          exact hcl p hpmem i (excAdj_comm m i p hadj')
    exact key (excDepth m i.val) i rfl
  exact Finset.eq_univ_of_forall hall

private theorem excLabel0 : label (0 : Fin 6) Finset.univ = ⟨CFSG.Assembly.LargeEvenLieTag.F4, 0, 1⟩ := by rfl

private theorem excLabel1 : label (1 : Fin 6) Finset.univ = ⟨CFSG.Assembly.LargeEvenLieTag.E6, 0, 1⟩ := by
  rw [label, show longCount (1 : Fin 6) Finset.univ = 12 from by decide +kernel]
  rfl

private theorem excLabel2 : label (2 : Fin 6) Finset.univ = ⟨CFSG.Assembly.LargeEvenLieTag.twE6, 0, 1⟩ := by
  rw [label, show orthCount (2 : Fin 6) Finset.univ = 540 from by decide +kernel]
  rfl

private theorem excLabel3 : label (3 : Fin 6) Finset.univ = ⟨CFSG.Assembly.LargeEvenLieTag.twE6, 0, 1⟩ := by
  rw [label, show orthCount (3 : Fin 6) Finset.univ = 540 from by decide +kernel]
  rfl

private theorem excLabel4 : label (4 : Fin 6) Finset.univ = ⟨CFSG.Assembly.LargeEvenLieTag.E7, 0, 1⟩ := by rfl

private theorem excLabel5 : label (5 : Fin 6) Finset.univ = ⟨CFSG.Assembly.LargeEvenLieTag.E8, 0, 1⟩ := by rfl

theorem occurs_bot_iff (m : Fin 6) (c : Finset (Root m)) :
    occurs m ⊥ c ↔ c = Finset.univ := by
  constructor
  · rintro ⟨hne, -, hcl, -⟩
    exact excConnected m c hne fun i hi j hadj => hcl i hi j (excVanish_bot m j) hadj
  · intro hc
    subst hc
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact ⟨⟨0, excNroots_pos m⟩, Finset.mem_univ _⟩
    · intro i _; exact excVanish_bot m i
    · intro i _ j _ _; exact Finset.mem_univ j
    · intro T _ hne hcl
      exact excConnected m T hne fun i hi j hadj => hcl i hi j (Finset.mem_univ j) hadj

private theorem excAdmissible0 : admissible (0 : Fin 6) Finset.univ := by
  refine ⟨⟨⊥, (occurs_bot_iff (0 : Fin 6) Finset.univ).2 rfl⟩, ?_⟩
  rw [excLabel0]; simp [CFSG.Assembly.LargeEvenInLambda2]

private theorem excAdmissible1 : admissible (1 : Fin 6) Finset.univ := by
  refine ⟨⟨⊥, (occurs_bot_iff (1 : Fin 6) Finset.univ).2 rfl⟩, ?_⟩
  rw [excLabel1]; simp [CFSG.Assembly.LargeEvenInLambda2]

private theorem excAdmissible2 : admissible (2 : Fin 6) Finset.univ := by
  refine ⟨⟨⊥, (occurs_bot_iff (2 : Fin 6) Finset.univ).2 rfl⟩, ?_⟩
  rw [excLabel2]; simp [CFSG.Assembly.LargeEvenInLambda2]

private theorem excAdmissible3 : admissible (3 : Fin 6) Finset.univ := by
  refine ⟨⟨⊥, (occurs_bot_iff (3 : Fin 6) Finset.univ).2 rfl⟩, ?_⟩
  rw [excLabel3]; simp [CFSG.Assembly.LargeEvenInLambda2]

private theorem excAdmissible4 : admissible (4 : Fin 6) Finset.univ := by
  refine ⟨⟨⊥, (occurs_bot_iff (4 : Fin 6) Finset.univ).2 rfl⟩, ?_⟩
  rw [excLabel4]; simp [CFSG.Assembly.LargeEvenInLambda2]

private theorem excAdmissible5 : admissible (5 : Fin 6) Finset.univ := by
  refine ⟨⟨⊥, (occurs_bot_iff (5 : Fin 6) Finset.univ).2 rfl⟩, ?_⟩
  rw [excLabel5]; simp [CFSG.Assembly.LargeEvenInLambda2]

theorem admissible_univ (m : Fin 6) : admissible m Finset.univ := by
  fin_cases m
  · exact excAdmissible0
  · exact excAdmissible1
  · exact excAdmissible2
  · exact excAdmissible3
  · exact excAdmissible4
  · exact excAdmissible5

end ExcRaw

end CFSG.StandardType.GGQ2Frame
