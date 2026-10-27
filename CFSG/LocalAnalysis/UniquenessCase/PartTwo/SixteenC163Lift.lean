module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3OddNc
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165Lift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace C163

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem exists_noncyclic_le_centralizer {M V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {p : ℕ} (hp : p.Prime) (hV₀ : Nat.card V₀ < p) {w : G} (hw : w ∈ V)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hEM : E ≤ Mbar M V₀ V hV) (hEp : IsPGroup p ↥E)
    (hEc : ¬ IsCyclic ↥E)
    (hEw : ∀ x ∈ E, x (mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) =
      mkTil V₀ V hV (IntMod.mk hV ⟨w, hw⟩)) :
    ∃ P : Subgroup G, P ≤ M ⊓ centralizer ({w} : Set G) ∧ IsPGroup p ↥P ∧ ¬ IsCyclic ↥P := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨X, hX, hXp, hXc⟩ := s16c167_exists_pSub_lift hV hEM hEp hEc
  refine ⟨X, le_inf (fun x hx => ((mem_preBarSub M V₀ V hV E).1 (hX hx)).1) ?_, hXp, hXc⟩
  refine Om8Lift.le_centralizer_of_conj_mem hp hXp hV₀ ?_
  intro x hx
  obtain ⟨-, hxs, hxE⟩ := (mem_preBarSub M V₀ V hV E).1 (hX hx)
  have h1 := hEw _ hxE
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val] at h1
  exact h1

end C163

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
