module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G]

structure C23APair (M V W W' : Subgroup G) : Prop where
  elem : IsElemAbelian 2 V
  norm : M ≤ normalizer (V : Set G)
  le : W ≤ V
  le' : W' ≤ V
  sup : W ⊔ W' = V
  three : 3 ≤ mSub W
  three' : 3 ≤ mSub W'
  perm : ∀ m ∈ M, (conjSubgroup W m = W ∧ conjSubgroup W' m = W') ∨
    (conjSubgroup W m = W' ∧ conjSubgroup W' m = W)
  cent : ∀ w ∈ (W : Set G) ∪ (W' : Set G), w ≠ 1 → centralizer ({w} : Set G) ≤ M
  oneSided : ∀ t ∈ M, (∃ j : ℕ, orderOf t = 2 ^ j) → ¬ V ≤ centralizer ({t} : Set G) →
    mSub (commElt V t) ≤ 2 →
      (((∀ y ∈ W', t * y = y * t) ∧ commElt V t ≤ W) ∨
        ((∀ y ∈ W, t * y = y * t) ∧ commElt V t ≤ W')) ∧ 2 ≤ mSub (commElt V t)
  rankLe : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
    (∀ e ∈ E, e ∈ normalizer (W : Set G)) → (∀ e ∈ E, ∀ y ∈ W', e * y = y * e) →
      E3.mQuot E (centralizer (V : Set G)) ≤ 2
  rankLe' : ∀ E : Subgroup G, E ≤ M → IsElemAbelian 2 E →
    (∀ e ∈ E, e ∈ normalizer (W' : Set G)) → (∀ e ∈ E, ∀ y ∈ W, e * y = y * e) →
      E3.mQuot E (centralizer (V : Set G)) ≤ 2

theorem C23APair.symm {M V W W' : Subgroup G} (h : C23APair M V W W') : C23APair M V W' W where
  elem := h.elem
  norm := h.norm
  le := h.le'
  le' := h.le
  sup := by rw [sup_comm]; exact h.sup
  three := h.three'
  three' := h.three
  perm := fun m hm =>
    (h.perm m hm).elim (fun h1 => Or.inl ⟨h1.2, h1.1⟩) (fun h1 => Or.inr ⟨h1.2, h1.1⟩)
  cent := fun w hw => h.cent w (Set.union_comm _ _ ▸ hw)
  oneSided := fun t ht h2 hV hm => by
    obtain ⟨h1, h3⟩ := h.oneSided t ht h2 hV hm
    exact ⟨h1.symm, h3⟩
  rankLe := h.rankLe'
  rankLe' := h.rankLe

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
