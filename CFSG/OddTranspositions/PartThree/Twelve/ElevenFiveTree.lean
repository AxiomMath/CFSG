module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveTreeSteps

public section

namespace CFSG.OddTranspositions.PartThree

open Matrix

private theorem exists_fiveTreeBasis_aux (k : ℕ) (ε π : Bool) :
    ∀ m : ℕ, ∀ {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)},
      IsFiveNondeg k ε W → Module.finrank (ZMod 5) W = m → 4 ≤ m →
      ∃ (b : Fin m → Fin (k + 1) → ZMod 5) (p : Fin m → Fin m) (j : Fin m),
        IsFiveTree k ε π W b p ∧ IsFiveAnchor k ε W b j ∧
        Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)) =
          fiveReflectionGroupIn k ε π W := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro W hW hfin h4
    by_cases hm : m = 4
    · subst hm
      exact exists_fiveTree_four hW hfin
    · obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
      have hm'4 : 4 ≤ m' := by omega
      obtain ⟨H, hHW, hH, hHdim⟩ := exists_fiveNondeg_hyperplane hW (by omega)
      have hHfin : Module.finrank (ZMod 5) H = m' := by omega
      obtain ⟨b, p, j, htree, hanchor, hclos⟩ := ih m' (by omega) hH hHfin hm'4
      obtain ⟨x, hxW, hxH, hBxj, htree', hanchor'⟩ :=
        exists_fiveTree_leaf hW hH hHW hHdim htree hanchor
      obtain ⟨j', hanchor''⟩ := hanchor'
      have htree'' := htree'
      unfold IsFiveTree at htree'' htree
      have hxQ : fiveForm k ε x x ≠ 0 := by
        simpa only [Fin.snoc_last] using (htree''.1 (Fin.last m')).2.1
      have hxπ : IsSquare (fiveForm k ε x x) ↔ π = true := by
        simpa only [Fin.snoc_last] using (htree''.1 (Fin.last m')).2.2
      have hh : b j ∈ H := (htree.1 j).1
      have hsup := fiveReflectionGroupIn_eq_sup_of_hyperplane hW hH hHW hHdim (by omega)
        hxW hxH hxQ hxπ hh hBxj
      have hrange : Set.range (fun i : Fin (m' + 1) =>
            fiveReflOf k ε ((Fin.snoc b x : Fin (m' + 1) → Fin (k + 1) → ZMod 5) i)) =
          Set.insert (fiveReflOf k ε x) (Set.range fun i : Fin m' => fiveReflOf k ε (b i)) := by
        ext g
        constructor
        · rintro ⟨i, rfl⟩
          cases i using Fin.lastCases with
          | last => simp only [Fin.snoc_last]; exact Set.mem_insert _ _
          | cast i =>
            exact Set.mem_insert_of_mem _ ⟨i, by simp only [Fin.snoc_castSucc]⟩
        · intro hg
          rcases Set.mem_insert_iff.mp hg with rfl | ⟨i, rfl⟩
          · exact ⟨Fin.last m', by simp only [Fin.snoc_last]⟩
          · exact ⟨i.castSucc, by simp only [Fin.snoc_castSucc]⟩
      refine ⟨Fin.snoc b x, Fin.snoc (fun i => (p i).castSucc) j.castSucc, j', ?_, hanchor'', ?_⟩
      · exact htree'
      · rw [hrange]
        rw [show Set.insert (fiveReflOf k ε x) (Set.range fun i : Fin m' => fiveReflOf k ε (b i)) =
            {fiveReflOf k ε x} ∪ (Set.range fun i : Fin m' => fiveReflOf k ε (b i)) by rfl]
        rw [Subgroup.closure_union, hclos]
        rw [hsup]
        exact sup_comm _ _

theorem exists_fiveTreeBasis {k : ℕ} {ε π : Bool} {W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5)}
    (hW : IsFiveNondeg k ε W) (h4 : 4 ≤ Module.finrank (ZMod 5) W) :
    ∃ (b : Fin (Module.finrank (ZMod 5) W) → Fin (k + 1) → ZMod 5)
      (p : Fin (Module.finrank (ZMod 5) W) → Fin (Module.finrank (ZMod 5) W)),
      (∀ i, b i ∈ W ∧ fiveForm k ε (b i) (b i) ≠ 0 ∧
        (IsSquare (fiveForm k ε (b i) (b i)) ↔ π = true)) ∧
      LinearIndependent (ZMod 5) b ∧
      (∀ i : Fin (Module.finrank (ZMod 5) W), (i : ℕ) ≠ 0 →
        (p i : ℕ) < (i : ℕ) ∧ fiveForm k ε (b i) (b (p i)) ≠ 0) ∧
      (∀ i j : Fin (Module.finrank (ZMod 5) W), fiveForm k ε (b i) (b j) ≠ 0 →
        i = j ∨ ((i : ℕ) ≠ 0 ∧ j = p i) ∨ ((j : ℕ) ≠ 0 ∧ i = p j)) ∧
      Subgroup.closure (Set.range fun i => fiveReflOf k ε (b i)) =
        fiveReflectionGroupIn k ε π W := by
  obtain ⟨b, p, j, htree, -, hclos⟩ :=
    exists_fiveTreeBasis_aux k ε π (Module.finrank (ZMod 5) W) hW rfl h4
  have htree' := htree
  unfold IsFiveTree at htree'
  exact ⟨b, p, htree'.1, htree'.2.1, htree'.2.2.1, htree'.2.2.2, hclos⟩

end CFSG.OddTranspositions.PartThree

end
