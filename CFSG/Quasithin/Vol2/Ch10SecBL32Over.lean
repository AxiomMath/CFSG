module

public import CFSG.Quasithin.Vol2.Ch10SecBL32

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.L32

@[expose] def uList : List Γ :=
  [⟨!![1, 0, 0; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩,
   ⟨!![1, 0, 1; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩,
   ⟨!![1, 1, 1; 0, 1, 0; 0, 0, 1], by decide⟩, ⟨!![1, 1, 0; 0, 1, 1; 0, 0, 1], by decide⟩,
   ⟨!![1, 0, 1; 0, 1, 1; 0, 0, 1], by decide⟩, ⟨!![1, 1, 1; 0, 1, 1; 0, 0, 1], by decide⟩]

@[expose] def s1 : Γ := ⟨!![1, 0, 0; 0, 0, 1; 0, 1, 0], by decide⟩

@[expose] def s2 : Γ := ⟨!![0, 1, 0; 1, 0, 0; 0, 0, 1], by decide⟩

@[expose] def wList : List Γ := [1, s1, s2, s1 * s2, s2 * s1, s1 * s2 * s1]

theorem mem_uList_iff : ∀ g : Γ, g ∈ uList ↔ IsU g := by
  unfold uList IsU ent
  decide +kernel

theorem bruhat : ∀ h : Γ, ∃ u₁ ∈ uList, ∃ w ∈ wList, ∃ u₂ ∈ uList, h = u₁ * w * u₂ := by
  unfold uList wList s1 s2
  decide +kernel

theorem pa_cells : ∀ p : Γ, IsPa p → IsU p ∨ ∃ u₁ ∈ uList, ∃ u₂ ∈ uList, p = u₁ * s1 * u₂ := by
  unfold uList s1 IsPa IsU ent
  decide +kernel

theorem pb_cells : ∀ p : Γ, IsPb p → IsU p ∨ ∃ u₁ ∈ uList, ∃ u₂ ∈ uList, p = u₁ * s2 * u₂ := by
  unfold uList s2 IsPb IsU ent
  decide +kernel

theorem cells_pa : ∀ u₁ ∈ uList, ∀ u₂ ∈ uList, IsPa (u₁ * u₂) ∧ IsPa (u₁ * s1 * u₂) ∧
    IsPb (u₁ * u₂) ∧ IsPb (u₁ * s2 * u₂) ∧ IsU (u₁ * u₂) := by
  unfold uList s1 s2 IsPa IsPb IsU ent
  decide +kernel

theorem exchange : ∀ w ∈ [s1 * s2, s2 * s1, s1 * s2 * s1],
    (∃ u ∈ uList, (IsPa (w * u * w⁻¹) ∧ ¬ IsU (w * u * w⁻¹)) ∨
        (IsPa (w⁻¹ * u * w) ∧ ¬ IsU (w⁻¹ * u * w))) ∧
      ∃ u ∈ uList, (IsPb (w * u * w⁻¹) ∧ ¬ IsU (w * u * w⁻¹)) ∨
        (IsPb (w⁻¹ * u * w) ∧ ¬ IsU (w⁻¹ * u * w)) := by
  unfold uList s1 s2 IsPa IsPb IsU ent
  decide +kernel

theorem s_mem : IsPa s1 ∧ ¬ IsU s1 ∧ IsPb s2 ∧ ¬ IsU s2 ∧ ¬ IsPb s1 ∧ ¬ IsPa s2 := by
  unfold s1 s2 IsPa IsPb IsU ent
  decide

theorem normalizer_U3_aux : ∀ g : Γ, (∀ u ∈ uList, IsU (g * u * g⁻¹)) → IsU g := by
  unfold uList IsU ent
  decide +kernel

theorem mem_of_mem_uList {Y : Subgroup Γ} (hY : U3 ≤ Y) {u : Γ} (hu : u ∈ uList) : u ∈ Y :=
  hY ((mem_uList_iff u).mp hu)

theorem mem_of_cell {Y : Subgroup Γ} (hY : U3 ≤ Y) {u₁ w u₂ : Γ} (h₁ : u₁ ∈ uList)
    (h₂ : u₂ ∈ uList) (h : u₁ * w * u₂ ∈ Y) : w ∈ Y := by
  have := Y.mul_mem (Y.mul_mem (Y.inv_mem (mem_of_mem_uList hY h₁)) h)
    (Y.inv_mem (mem_of_mem_uList hY h₂))
  simpa [mul_assoc] using this

theorem s1_mem_of {Y : Subgroup Γ} (hY : U3 ≤ Y) {p : Γ} (hp : IsPa p) (hpU : ¬ IsU p)
    (hpY : p ∈ Y) : s1 ∈ Y := by
  rcases pa_cells p hp with h | ⟨u₁, h₁, u₂, h₂, rfl⟩
  · exact absurd h hpU
  · exact mem_of_cell hY h₁ h₂ hpY

theorem s2_mem_of {Y : Subgroup Γ} (hY : U3 ≤ Y) {p : Γ} (hp : IsPb p) (hpU : ¬ IsU p)
    (hpY : p ∈ Y) : s2 ∈ Y := by
  rcases pb_cells p hp with h | ⟨u₁, h₁, u₂, h₂, rfl⟩
  · exact absurd h hpU
  · exact mem_of_cell hY h₁ h₂ hpY

theorem pa_le_of {Y : Subgroup Γ} (hY : U3 ≤ Y) (hs : s1 ∈ Y) : Pa ≤ Y := by
  intro p hp
  rcases pa_cells p hp with h | ⟨u₁, h₁, u₂, h₂, rfl⟩
  · exact hY h
  · exact Y.mul_mem (Y.mul_mem (mem_of_mem_uList hY h₁) hs) (mem_of_mem_uList hY h₂)

theorem pb_le_of {Y : Subgroup Γ} (hY : U3 ≤ Y) (hs : s2 ∈ Y) : Pb ≤ Y := by
  intro p hp
  rcases pb_cells p hp with h | ⟨u₁, h₁, u₂, h₂, rfl⟩
  · exact hY h
  · exact Y.mul_mem (Y.mul_mem (mem_of_mem_uList hY h₁) hs) (mem_of_mem_uList hY h₂)

theorem s_mem_of_long {Y : Subgroup Γ} (hY : U3 ≤ Y) {w : Γ}
    (hw : w ∈ [s1 * s2, s2 * s1, s1 * s2 * s1]) (hwY : w ∈ Y) : s1 ∈ Y ∧ s2 ∈ Y := by
  obtain ⟨⟨u, hu, ha⟩, ⟨u', hu', hb⟩⟩ := exchange w hw
  have huY := mem_of_mem_uList hY hu
  have hu'Y := mem_of_mem_uList hY hu'
  constructor
  · rcases ha with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · exact s1_mem_of hY hp hn (Y.mul_mem (Y.mul_mem hwY huY) (Y.inv_mem hwY))
    · exact s1_mem_of hY hp hn (Y.mul_mem (Y.mul_mem (Y.inv_mem hwY) huY) hwY)
  · rcases hb with ⟨hp, hn⟩ | ⟨hp, hn⟩
    · exact s2_mem_of hY hp hn (Y.mul_mem (Y.mul_mem hwY hu'Y) (Y.inv_mem hwY))
    · exact s2_mem_of hY hp hn (Y.mul_mem (Y.mul_mem (Y.inv_mem hwY) hu'Y) hwY)

theorem exists_cell {Y : Subgroup Γ} (hY : U3 ≤ Y) {h : Γ} (hh : h ∈ Y) :
    ∃ u₁ ∈ uList, ∃ w ∈ wList, ∃ u₂ ∈ uList, h = u₁ * w * u₂ ∧ w ∈ Y := by
  obtain ⟨u₁, h₁, w, hw, u₂, h₂, rfl⟩ := bruhat h
  exact ⟨u₁, h₁, w, hw, u₂, h₂, rfl, mem_of_cell hY h₁ h₂ hh⟩

theorem overgroups (Y : Subgroup Γ) (hY : U3 ≤ Y) : Y = U3 ∨ Y = Pa ∨ Y = Pb ∨ Y = ⊤ := by
  have hlong : ∀ {w : Γ}, w ∈ wList → w ≠ 1 → w ≠ s1 → w ≠ s2 →
      w ∈ [s1 * s2, s2 * s1, s1 * s2 * s1] := by
    intro w hw h1 h2 h3
    simp only [wList, List.mem_cons, List.mem_nil_iff, or_false] at hw ⊢
    tauto
  by_cases h1 : s1 ∈ Y <;> by_cases h2 : s2 ∈ Y
  · refine Or.inr (Or.inr (Or.inr (eq_top_iff.mpr fun h _ => ?_)))
    obtain ⟨u₁, h₁, w, hw, u₂, h₂, rfl⟩ := bruhat h
    refine Y.mul_mem (Y.mul_mem (mem_of_mem_uList hY h₁) ?_) (mem_of_mem_uList hY h₂)
    simp only [wList, List.mem_cons, List.mem_nil_iff, or_false] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Y.one_mem
    · exact h1
    · exact h2
    · exact Y.mul_mem h1 h2
    · exact Y.mul_mem h2 h1
    · exact Y.mul_mem (Y.mul_mem h1 h2) h1
  · refine Or.inr (Or.inl (le_antisymm (fun h hh => ?_) (pa_le_of hY h1)))
    obtain ⟨u₁, h₁, w, hw, u₂, h₂, rfl, hwY⟩ := exists_cell hY hh
    by_cases hw1 : w = 1
    · subst hw1; show IsPa (u₁ * 1 * u₂); rw [mul_one]; exact (cells_pa u₁ h₁ u₂ h₂).1
    by_cases hws1 : w = s1
    · subst hws1; exact (cells_pa u₁ h₁ u₂ h₂).2.1
    by_cases hws2 : w = s2
    · subst hws2; exact absurd hwY h2
    exact absurd (s_mem_of_long hY (hlong hw hw1 hws1 hws2) hwY).2 h2
  · refine Or.inr (Or.inr (Or.inl (le_antisymm (fun h hh => ?_) (pb_le_of hY h2))))
    obtain ⟨u₁, h₁, w, hw, u₂, h₂, rfl, hwY⟩ := exists_cell hY hh
    by_cases hw1 : w = 1
    · subst hw1; show IsPb (u₁ * 1 * u₂); rw [mul_one]; exact (cells_pa u₁ h₁ u₂ h₂).2.2.1
    by_cases hws1 : w = s1
    · subst hws1; exact absurd hwY h1
    by_cases hws2 : w = s2
    · subst hws2; exact (cells_pa u₁ h₁ u₂ h₂).2.2.2.1
    exact absurd (s_mem_of_long hY (hlong hw hw1 hws1 hws2) hwY).1 h1
  · refine Or.inl (le_antisymm (fun h hh => ?_) hY)
    obtain ⟨u₁, h₁, w, hw, u₂, h₂, rfl, hwY⟩ := exists_cell hY hh
    by_cases hw1 : w = 1
    · subst hw1; show IsU (u₁ * 1 * u₂); rw [mul_one]; exact (cells_pa u₁ h₁ u₂ h₂).2.2.2.2
    by_cases hws1 : w = s1
    · subst hws1; exact absurd hwY h1
    by_cases hws2 : w = s2
    · subst hws2; exact absurd hwY h2
    exact absurd (s_mem_of_long hY (hlong hw hw1 hws1 hws2) hwY).1 h1

theorem normalizer_U3 : Subgroup.normalizer (U3 : Set Γ) = U3 := by
  refine le_antisymm (fun g hg => normalizer_U3_aux g fun u hu => ?_) Subgroup.le_normalizer
  exact (Subgroup.mem_normalizer_iff.mp hg u).mp ((mem_uList_iff u).mp hu)

end CFSG.Quasithin.Vol2.Ch10.SecB.L32
