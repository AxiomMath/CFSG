module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4Model

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open Equiv Equiv.Perm Subgroup
open CFSG.RankThree.PartTwo.Sec21.FF84.S3 (P8)

theorem mem_CenS_Pm_iff (g : P8) : g ∈ CenS Pm ↔ g * cc = cc * g ∧ g * dd = dd * g := by
  constructor
  · intro h
    have hc : cc ∈ (Pm : Set P8) := Subgroup.subset_closure (Set.mem_insert _ _)
    have hd : dd ∈ (Pm : Set P8) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    exact ⟨(mem_centralizer_iff.1 h cc hc).symm, (mem_centralizer_iff.1 h dd hd).symm⟩
  · rintro ⟨h1, h2⟩
    have hle : Subgroup.closure ({cc, dd} : Set P8) ≤ centralizer {g} := by
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      rcases hx with rfl | hx
      · exact mem_centralizer_singleton_iff.2 h1.symm
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact mem_centralizer_singleton_iff.2 h2.symm
    refine mem_centralizer_iff.2 fun x hx => ?_
    exact mem_centralizer_singleton_iff.1 (hle hx)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
theorem involution_cent_P_key : ∀ g : P8, g * cc = cc * g → g * dd = dd * g → g * g = 1 →
    g ≠ 1 → g = swap 6 7 := by
  decide +kernel

theorem involution_cent_P_eq (g : P8) (h1 : g * cc = cc * g) (h2 : g * dd = dd * g)
    (h3 : g * g = 1) (h4 : g ≠ 1) : g = swap 6 7 :=
  involution_cent_P_key g h1 h2 h3 h4

theorem A_cent_P_inv_involution : ∀ g ∈ CenS Pm, orderOf g = 2 → g = Equiv.swap 6 7 := by
  intro g hg ho
  rw [mem_CenS_Pm_iff] at hg
  have hsq : g * g = 1 := by
    have := pow_orderOf_eq_one g
    rw [ho] at this
    simpa [pow_two] using this
  have hne : g ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ho
    exact absurd ho (by norm_num)
  exact involution_cent_P_eq g hg.1 hg.2 hsq hne

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
