module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem false_of_k_eq_one_of_inP11 {D : Data G} {V₀ V : Subgroup G} {hV : Hyp125 D V₀ V}
    (h1 : R17_1At D V₀ V hV) (hk : D.k = 1) {Q : Subgroup G} (hQ : F11.InP11 D Q) : False := by
  have hk2 : D.k = 2 := (h1.2 ⟨Q, hQ⟩).2.1
  omega

theorem Ctx17_42.one_le_exponent {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (hC : Ctx17_42 D V₀ V L X p n l C Dc Gamma) :
    1 ≤ n := by
  obtain ⟨t, m, hadm, -⟩ := hC.chev
  exact hadm.2.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
