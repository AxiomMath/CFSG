module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Defs
import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1Weyl

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal

@[expose] def GGIsWeylMatrixAD5 {ι : Type} (M : CoxeterMatrix ι) : Prop :=
  (∃ (n : ℕ) (e : Fin n ≃ ι), 5 ≤ n ∧ M = (CoxeterMatrix.A n).reindex e) ∨
    (∃ (n : ℕ) (e : Fin n ≃ ι), 4 ≤ n ∧ M = (ggCoxeterMatrixD n).reindex e)

theorem GGIsWeylMatrixAD5.toAD {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrixAD5 M) :
    GGIsWeylMatrixAD M := by
  rcases h with ⟨n, e, hn, hM⟩ | ⟨n, e, hn, hM⟩
  · exact Or.inl ⟨n, e, by omega, hM⟩
  · exact Or.inr ⟨n, e, hn, hM⟩

theorem GGIsWeylMatrixAD5.le_three {ι : Type} {M : CoxeterMatrix ι} (h : GGIsWeylMatrixAD5 M)
    (i j : ι) (hij : i ≠ j) : M.M i j ≤ 3 :=
  GGIsWeylMatrixAD.le_three h.toAD i j hij

end CFSG.StandardType

end
