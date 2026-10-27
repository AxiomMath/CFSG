module

public import CFSG.Sporadic.HNOddCore.InvRow4
public import CFSG.Certificates.Kernel.SporSch.HNArr
public import CFSG.Quasithin.Background.Basic
public import CFSG.Open.LocalVocabulary

@[expose] public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.HNRank

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNOddCore CFSG.KS.HNArr

def t0Words : List (List Int) :=
  [[-10, 4, 10, 10, 8, -10], [-8, -10, 5], [-10, 5, 10, 10, 7, -10], [6]]

noncomputable def t0Gens :
    List JH :=
  t4J :: t0Words.map (wJ g4)

noncomputable def hnT0 :
    Subgroup JH :=
  Subgroup.closure {x | x ∈ t0Gens}

theorem hnT0_le_centralizer :
    hnT0 ≤ Subgroup.centralizer {t4J} := by
  have hg4 : Subgroup.closure (Set.range fun s : Fin 10 => g4 s) ≤
      Subgroup.centralizer {t4J} := by
    rw [Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    exact g4_mem s s.2
  have hw : ∀ w : List ℤ, (∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ 10) →
      wJ g4 w ∈ Subgroup.closure (Set.range fun s : Fin 10 => g4 s) := by
    intro w
    induction w with
    | nil => intro _; exact one_mem _
    | cons l w ih =>
      intro hl
      refine mul_mem ?_ (ih fun z hz => hl z (List.mem_cons_of_mem l hz))
      obtain ⟨hl0, hl10⟩ := hl l List.mem_cons_self
      unfold lJ
      split_ifs with hp
      · exact Subgroup.subset_closure ⟨⟨l.toNat - 1, by omega⟩, rfl⟩
      · exact inv_mem (Subgroup.subset_closure ⟨⟨(-l).toNat - 1, by omega⟩, rfl⟩)
  rw [hnT0, Subgroup.closure_le]
  intro x hx
  simp only [t0Gens, Set.mem_setOf_eq, List.mem_cons, List.mem_map] at hx
  rcases hx with rfl | ⟨w, hw', rfl⟩
  · exact Subgroup.mem_centralizer_singleton_iff.2 rfl
  · exact hg4 (hw w (by revert w; decide))

structure HNT0Facts :
    Prop where
  card : Nat.card hnT0 = 2 ^ 14
  card_le : ∀ E : Subgroup JH, E ≤ hnT0 → IsElemAbelian 2 E → Nat.card E ≤ 64
  t4_mem : t4J ∈ omegaOneCenterOf (thompsonJ hnT0)
  card_omega_le : Nat.card (omegaOneCenterOf (thompsonJ hnT0)) ≤ 4

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.HNRank

end
