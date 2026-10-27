module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Model
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Cover
public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityQ2Gen

public section

open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartTwo.Sec4.Item434D42
open CFSG.AGLEmbedding.ChevOuter HuppertD4Q2

namespace CFSG.RankThree.PartTwo.Sec19.TrialityTwo

section Assembly

theorem conj_ne_one {α r : MulAut lineGroup} (hr : r ≠ 1) : α * r * α⁻¹ ≠ 1 := by
  intro h0
  apply hr
  have := congrArg (fun z => α⁻¹ * z * α) h0
  simpa [mul_assoc] using this

theorem closure_fixUnion_of_conj_lines (hZ : Subgroup.center lineGroup = ⊥) {i : ℕ}
    (h : classCheck i = true) {E : Subgroup (MulAut lineGroup)} (α : MulAut lineGroup)
    (h1 : α * repLine1 i * α⁻¹ ∈ E) (h2 : α * repLine2 i * α⁻¹ ∈ E) :
    Subgroup.closure (fixUnion E) = ⊤ := by
  obtain ⟨hn1, hn2⟩ := repLine_ne_one hZ h
  have hgen := classGen_of_check hZ h
  rw [closure_fixUnion_eq_planeClosure, eq_top_iff]
  have key : ∀ t ∈ fixSet (repLine1 i) ∪ fixSet (repLine2 i), α t ∈ planeClosure E := by
    rintro t (ht | ht)
    · exact mem_planeClosure_of_fixed h1 (conj_ne_one hn1) (by
        have ht' : repLine1 i t = t := ht
        simp [MulAut.mul_apply, ht'])
    · exact mem_planeClosure_of_fixed h2 (conj_ne_one hn2) (by
        have ht' : repLine2 i t = t := ht
        simp [MulAut.mul_apply, ht'])
  have hmap : ∀ x ∈ Subgroup.closure (fixSet (repLine1 i) ∪ fixSet (repLine2 i)),
      α x ∈ planeClosure E := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy => exact key y hy
    | one => rw [map_one]; exact one_mem _
    | mul y z _ _ hy hz => rw [map_mul]; exact mul_mem hy hz
    | inv y _ hy => rw [map_inv]; exact inv_mem hy
  intro g _
  have hg : α⁻¹ g ∈ Subgroup.closure (fixSet (repLine1 i) ∪ fixSet (repLine2 i)) := by
    rw [hgen]; trivial
  simpa using hmap _ hg

theorem trialityTwoPlanes_of_checks (hZ : Subgroup.center lineGroup = ⊥)
    (hAut : Nat.card (MulAut lineGroup) = 3 * 211341312) (h0 : planeCoverCheck () = true)
    (hc : ∀ i < 6, classCheck i = true) : TrialityTwoPlanes := by
  intro E hE hcard
  obtain ⟨i, hi, α, h1, h2⟩ := planeCover_of_check hZ hAut h0 hE hcard
  exact closure_fixUnion_of_conj_lines hZ (hc i hi) α h1 h2

end Assembly

end CFSG.RankThree.PartTwo.Sec19.TrialityTwo
