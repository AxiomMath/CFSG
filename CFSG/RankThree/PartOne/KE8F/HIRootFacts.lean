module

public import CFSG.RankThree.PartOne.KE8F.E8Gauss

public section

namespace CFSG.RankThree.PartOne.KE8F

open CFSG.Blueprint.Chevalley Matrix CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE

@[expose] def za (l : List ℤ) : ℤ := (e8P4Coord l).getD 0 0

@[expose] def zb (l : List ℤ) : ℤ := (e8P4Coord l).getD 1 0

theorem gA_toVec_zero (l : List ℤ) : gA (toVec Tag.E8.rank l) 0 = za l := by
  have h := congrFun (toVec_lmulVec Tag.E8.rank e8P4BinvRows l) ⟨0, by decide⟩
  simp only [za, e8P4Coord, gA]
  exact h.symm

theorem gB_toVec_zero (l : List ℤ) : gB (toVec Tag.E8.rank l) 0 = zb l := by
  have h := congrFun (toVec_lmulVec Tag.E8.rank e8P4BinvRows l) ⟨1, by decide⟩
  simp only [zb, e8P4Coord, gB]
  exact h.symm

theorem rf_two_list : Tag.E8.artifactRoots.all (fun l =>
    (za l == 2 && zb l == 0) ||
      decide (0 < (za l - 2) ^ 2 + (zb l) ^ 2 ∧ (za l - 2) ^ 2 + (zb l) ^ 2 ≤ 16)) = true := by
  decide +kernel

theorem rf_unique_list : Tag.E8.artifactRoots.all (fun l => Tag.E8.artifactRoots.all (fun l' =>
    !(za l == 2 && zb l == 0 && za l' == 2 && zb l' == 0) || l == l')) = true := by
  decide +kernel

theorem rf_exists_list : Tag.E8.artifactRoots.any (fun l => za l == 2 && zb l == 0) = true := by
  decide +kernel

theorem rf_fiber_list : Tag.E8.artifactRoots.all (fun l =>
    ((za l) ^ 2 + (zb l) ^ 2 == 4 && (za l == 0 || zb l == 0)) ||
      Tag.E8.artifactRoots.any (fun l' => l' != l && za l' == za l && zb l' == zb l)) = true := by
  decide +kernel

section Vector


theorem toVec_injective_of_mem {l l' : List ℤ} (hl : l ∈ Tag.E8.artifactRoots)
    (hl' : l' ∈ Tag.E8.artifactRoots) (h : toVec Tag.E8.rank l = toVec Tag.E8.rank l') :
    l = l' := by
  have := congrArg List.ofFn h
  rwa [ofFn_toVec (length_of_mem_artifactRoots hl), ofFn_toVec (length_of_mem_artifactRoots hl')]
    at this

theorem rootFact_two {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    (gA α 0 = 2 ∧ gB α 0 = 0) ∨
      (0 < (gA α 0 - 2) ^ 2 + (gB α 0) ^ 2 ∧ (gA α 0 - 2) ^ 2 + (gB α 0) ^ 2 ≤ 16) := by
  refine (forall_isRoot_iff (τ := .E8) (fun v => (gA v 0 = 2 ∧ gB v 0 = 0) ∨
      (0 < (gA v 0 - 2) ^ 2 + (gB v 0) ^ 2 ∧ (gA v 0 - 2) ^ 2 + (gB v 0) ^ 2 ≤ 16))).2
    (fun l hl => ?_) α hα
  have h := List.all_eq_true.1 rf_two_list l hl
  rw [gA_toVec_zero, gB_toVec_zero]
  simpa only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] using h

theorem rootFact_exists : ∃ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ ∧ gA γ 0 = 2 ∧ gB γ 0 = 0 := by
  obtain ⟨l, hl, h⟩ := List.any_eq_true.1 rf_exists_list
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨toVec Tag.E8.rank l, isRoot_toVec hl, by rw [gA_toVec_zero]; exact h.1,
    by rw [gB_toVec_zero]; exact h.2⟩

theorem rootFact_unique {α β : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) (hβ : IsRoot .E8 β)
    (hα1 : gA α 0 = 2) (hα2 : gB α 0 = 0) (hβ1 : gA β 0 = 2) (hβ2 : gB β 0 = 0) : α = β := by
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
  obtain ⟨l', hl', rfl⟩ := isRoot_iff_exists_mem.1 hβ
  rw [gA_toVec_zero] at hα1 hβ1
  rw [gB_toVec_zero] at hα2 hβ2
  have h := List.all_eq_true.1 (List.all_eq_true.1 rf_unique_list l hl) l' hl'
  have hcond : (za l == 2 && zb l == 0 && za l' == 2 && zb l' == 0) = true := by
    simp [hα1, hα2, hβ1, hβ2]
  rw [hcond] at h
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h
  rw [h]

theorem rootFact_fiber {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    ((gA α 0) ^ 2 + (gB α 0) ^ 2 = 4 ∧ (gA α 0 = 0 ∨ gB α 0 = 0)) ∨
      ∃ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ ∧ γ ≠ α ∧ gA γ 0 = gA α 0 ∧ gB γ 0 = gB α 0 := by
  obtain ⟨l, hl, rfl⟩ := isRoot_iff_exists_mem.1 hα
  have h := List.all_eq_true.1 rf_fiber_list l hl
  rw [gA_toVec_zero, gB_toVec_zero]
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl ⟨h.1, by rcases h.2 with h2 | h2 <;> simp [h2]⟩
  · obtain ⟨l', hl', h'⟩ := List.any_eq_true.1 h
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h'
    refine Or.inr ⟨toVec Tag.E8.rank l', isRoot_toVec hl', fun he => h'.1.1
      (toVec_injective_of_mem hl' hl he), ?_, ?_⟩
    · rw [gA_toVec_zero]; exact h'.1.2
    · rw [gB_toVec_zero]; exact h'.2

end Vector

end CFSG.RankThree.PartOne.KE8F
