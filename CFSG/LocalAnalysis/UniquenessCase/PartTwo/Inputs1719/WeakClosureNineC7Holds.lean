module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineC7Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

theorem tcCoord7_holds : TCCoord7 := by
  intro B _ _ L D hD hLn hL1 hLp hB
  obtain ⟨φ, hφ⟩ := NFF7.exists_model hB hD
  obtain ⟨ψ⟩ := NFF7.nonempty_equiv_pgl2_zmod hB
  obtain ⟨hcard, -, hcent⟩ := NFF7.lb_facts ψ hLn hL1 hLp
  have hidx : L.index = 2 := by
    have h1 := L.index_mul_card
    rw [hcard, CFSG.GroupTheory.card_of_isPGL2_seven hB] at h1
    omega
  exact ⟨⊥, NFF7.C914.coordFacts hφ hD (fun x => sq_mem_of_index_two hidx x)
    (by rw [hcard]; norm_num) hcent⟩

end CFSG.LocalAnalysis.WeakClosure81
