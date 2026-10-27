module

public import CFSG.LocalAnalysis.WeakClosure81.W183B2Fin
import CFSG.Adapters.LieModelL4U4Sp4Torus
import CFSG.LocalAnalysis.UniquenessCase.UC22P22n

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Open Subgroup
open CFSG.Blueprint

theorem finSp44Noncyclic5_holds : FinSp44Noncyclic5 := by
  intro M _ hM
  obtain ⟨-, K, hfield, hfinite, hK, ⟨e⟩⟩ := hM.statedClassicalModel_of_ne_zero (by norm_num)
  letI : Field K := hfield
  letI : Finite K := hfinite
  haveI : Finite M := Finite.of_equiv _ e.symm.toEquiv
  have h2 : 2 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup M) :=
    hM.two_le_pRank_psp4_of_dvd (by norm_num) (by norm_num) (Or.inr (by norm_num))
  obtain ⟨E, -, hEab, hcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 5 (by norm_num) (⊤ : Subgroup M)
  refine ⟨E, IsPGroup.of_card hcard, uc22p22n_not_isCyclic_of_card (by norm_num) hEab ?_⟩
  rw [hcard]
  exact Nat.pow_le_pow_right (by norm_num) h2

end CFSG.LocalAnalysis.WeakClosure81

end
