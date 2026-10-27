module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnit63Desc
public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
import all CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescentC
import all CFSG.LocalAnalysis.StandardType.GGTwA5ThreeDescentD

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTorusTorData_descent_two {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    {N : ℕ} {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAle : A ≤ U63TB.presZ (U63TB.twoSub ψ.ker hker))
    (H : GGTorusTorData 3 N C M
      (L' ⧸ U63TB.twoSub ψ.ker hker) (U63TB.redSub hker hAle).range) :
    GGTorusTorData 3 N C M L' A := by
  obtain ⟨w₁, hw₁⟩ := H
  exact ⟨twd_w hker hperf hAle w₁ hw₁, twd_holds hker hperf hAle w₁ hw₁⟩

end CFSG.StandardType

end
