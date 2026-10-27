module

public import Mathlib.Order.SupIndep
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.RankThree.GF2n

section Lattice

variable {α : Type*} [CompleteLattice α] [IsModularLattice α] [WellFoundedLT α]

theorem exists_supIndep_irred (I : α → Prop) (hI : ∀ x y, I x → I y → I (x ⊓ y))
    (hc : ∀ x, I x → ∃ y, I y ∧ IsCompl x y) {P : α} (hP : I P) :
    ∃ s : Finset α, s.SupIndep id ∧ s.sup id = P ∧
      ∀ W ∈ s, I W ∧ W ≠ ⊥ ∧ ∀ U ≤ W, I U → U = ⊥ ∨ U = W := by
  classical
  induction P using WellFoundedLT.induction with
  | _ P ih =>
  by_cases hP0 : P = ⊥
  · exact ⟨∅, Finset.supIndep_empty _, by simp [hP0], by simp⟩
  obtain ⟨W, ⟨hWI, hW0, hWP⟩, hWmin⟩ := wellFounded_lt.has_min {U | I U ∧ U ≠ ⊥ ∧ U ≤ P}
    ⟨P, hP, hP0, le_rfl⟩
  have hWirr : ∀ U ≤ W, I U → U = ⊥ ∨ U = W := fun U hUW hUI => by
    by_cases hU0 : U = ⊥
    · exact Or.inl hU0
    · refine Or.inr (by_contra fun hne => hWmin U ⟨hUI, hU0, hUW.trans hWP⟩ ?_)
      exact lt_of_le_of_ne hUW hne
  obtain ⟨Y, hYI, hWY⟩ := hc W hWI
  have hlt : P ⊓ Y < P := by
    refine lt_of_le_of_ne inf_le_left fun h => hW0 ?_
    have hWY' : W ≤ Y := (hWP.trans_eq h.symm).trans inf_le_right
    exact le_bot_iff.mp ((le_inf le_rfl hWY').trans hWY.disjoint.le_bot)
  obtain ⟨s, hs, hsP, hsirr⟩ := ih (P ⊓ Y) hlt (hI P Y hP hYI)
  refine ⟨insert W s, hs.insert ?_, ?_, ?_⟩
  · rw [hsP]
    exact hWY.disjoint.mono_right inf_le_right
  · rw [Finset.sup_insert, hsP, id, inf_comm, ← sup_inf_assoc_of_le Y hWP, hWY.sup_eq_top,
      top_inf_eq]
  · intro V hV
    rcases Finset.mem_insert.mp hV with rfl | hV
    · exact ⟨hWI, hW0, hWirr⟩
    · exact hsirr V hV

end Lattice

section Map

variable {G : Type*} [Group G] {M : Subgroup G}

theorem supIndep_image_map [DecidableEq (Subgroup G)] {s : Finset (Subgroup ↥M)}
    (hs : s.SupIndep id) : (s.image (Subgroup.map M.subtype)).SupIndep id := by
  have hinj : Function.Injective (Subgroup.map M.subtype) :=
    Subgroup.map_injective M.subtype_injective
  refine Finset.SupIndep.image ?_
  intro t ht i hi hit
  have h := hs ht hi hit
  have hsup : t.sup (id ∘ Subgroup.map M.subtype) = Subgroup.map M.subtype (t.sup id) := by
    rw [Finset.apply_sup_eq_sup_comp (Subgroup.map M.subtype) (fun x y => Subgroup.map_sup x y _)
      (Subgroup.map_bot _)]
    rfl
  rw [Function.comp_apply, id, hsup, disjoint_iff,
    ← Subgroup.map_inf_eq _ _ M.subtype M.subtype_injective,
    (disjoint_iff.mp h : i ⊓ t.sup id = ⊥), Subgroup.map_bot]

theorem sup_image_map [DecidableEq (Subgroup G)] (s : Finset (Subgroup ↥M)) :
    (s.image (Subgroup.map M.subtype)).sup id = (s.sup id).map M.subtype := by
  rw [Finset.sup_image, Finset.apply_sup_eq_sup_comp (Subgroup.map M.subtype)
    (fun x y => Subgroup.map_sup x y _) (Subgroup.map_bot _)]
  rfl

end Map

end CFSG.RankThree.GF2n
