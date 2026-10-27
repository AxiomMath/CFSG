module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147SzJ1Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22K147Sz
import CFSG.LocalAnalysis.UniquenessCase.UC22K147J1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

theorem k147SzJ1_holds : K147SzJ1 := by
  intro G _ _ V _ _ _ ρ hρ hirr L hL n hcase
  obtain ⟨ℓ, hℓ, hℓ2, hn, hF⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ≠ 2 ∧ 2 * n + 4 ≤ orderOf (2 : ZMod ℓ) ∧
      Excl147.Facts L ℓ := by
    rcases hcase.1 with ⟨hn, hSz⟩ | ⟨hJ, rfl⟩
    · obtain ⟨ℓ, hℓ, hℓ2, hord, hF⟩ := Excl147.facts_of_isSz hSz
      exact ⟨ℓ, hℓ, hℓ2, by omega, hF⟩
    · exact ⟨19, by norm_num, by norm_num, by rw [Excl147.orderOf_two_zmod_nineteen]; norm_num,
        Excl147.facts_of_isJ1 hJ⟩
  exact Excl147.lt_mGV_of_facts ρ hρ hirr hL hℓ hℓ2 hF hn

end CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
