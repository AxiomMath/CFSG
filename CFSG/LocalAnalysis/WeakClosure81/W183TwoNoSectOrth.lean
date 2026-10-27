module

public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectOrthAux1
public import CFSG.LocalAnalysis.WeakClosure81.W183TwoNoSectOrthAux2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)

theorem noPsp45Factor_of_isOrthGp (hO : LieOrderFormulasInput)
    {Y : Type} [Group Y] {m n : ℕ} (h : IsOrthGp Y m n) :
    NoPsp45Factor Y := by
  rcases h with ⟨k, hk, rfl, hY⟩ | ⟨k, hk, rfl, hY⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hY
    refine NoPsp45Factor.of_mulEquiv e.symm ?_
    rcases (by omega : k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | h4
    · exact w183b5_noPsp45Factor_orthogonalPlus_two hO hF
    · exact w183b5_noPsp45Factor_orthogonalPlus_three hO hF
    · exact w183b5_noPsp45Factor_orthogonalPlus hO hF h4
  · obtain ⟨F, _, _, hF, b, c, hbc, ⟨e⟩⟩ := hY
    refine NoPsp45Factor.of_mulEquiv e.symm ?_
    rcases (by omega : k = 1 ∨ k = 2 ∨ 3 ≤ k) with rfl | rfl | h3
    · exact w183b5_noPsp45Factor_orthogonalMinus_one hO hF hbc
    · exact w183b5_noPsp45Factor_orthogonalMinus_two hO hF hbc
    · exact w183b5_noPsp45Factor_orthogonalMinus hO hF h3 hbc


end CFSG.LocalAnalysis.WeakClosure81

end
