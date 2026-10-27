module

public import CFSG.Quasithin.H13.StatementsL6

public section

namespace CFSG.Quasithin.H13.TI325

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

theorem of_eq_conjClosure {V M : Subgroup G} (h : V = conjClosure V M) : IsTISetUnder V M := by
  intro g hg hgn
  refine (hgn ?_).elim
  rw [h]
  exact le_normalizer_conjClosure V M hg

variable [Finite G]

theorem of_stmt3_2_5 (h325 : Stmt3_2_5) {T L V₀ : Subgroup G} (hfsu : FSU G T L V₀)
    (hL : L = conjClosure L T) :
    IsTISetUnder (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) := by
  obtain ⟨-, -, hcases⟩ := h325 G T L V₀ hfsu hL
  rw [← hL]
  rcases hcases with ⟨-, hVM⟩ | ⟨hV, -, -, -, hTI⟩ | ⟨-, -, ⟨t, ht, htN⟩, hall⟩
  · exact of_eq_conjClosure hVM
  · rw [← hV]
    exact hTI
  · exact of_eq_conjClosure (hall t ht htN).1.symm

theorem of_stmt3_2_5_of_le_normalizer (h325 : Stmt3_2_5) {T L V₀ : Subgroup G}
    (hfsu : FSU G T L V₀) (hTL : T ≤ Subgroup.normalizer (L : Set G)) :
    IsTISetUnder (conjClosure V₀ T) (Subgroup.normalizer (conjClosure L T : Set G)) :=
  of_stmt3_2_5 h325 hfsu (le_antisymm (le_conjClosure L T)
    (conjClosure_le fun _ ht l hl => (Subgroup.mem_normalizer_iff.mp (hTL ht) l).mp hl))

end CFSG.Quasithin.H13.TI325
