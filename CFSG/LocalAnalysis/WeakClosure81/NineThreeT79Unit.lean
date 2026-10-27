module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeT79UnitA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification.RankTwoClassical

theorem nine3_prop710_unitary {m n : ℕ} (hn : 1 ≤ n) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = (2 ^ n) ^ 2)
    {c a e a' v : StatedProj (StatedSU m (2 ^ n) F)} (hc : IsUnitaryTransvectionIn m n c)
    (h : Nine3Config c a e a' v) :
    ∃ d, IsConj c d ∧ d ≠ v ∧ d * a = a * d ∧ d * e = e * d := by
  have hU : UnitaryFieldData 2 n F := unitaryFieldData_of_card hF hn
  exact nine3_prop710_unitary_geom hU hc h

end CFSG.LocalAnalysis.WeakClosure81
