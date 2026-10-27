module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGTPRowDatum (Y : Type) [Group Y] : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (K : Type) (_ : Field K) (_ : Finite K)
    (H : Subgroup (GL ι K)), Nonempty (Y ≃* LargeEvenProj H) ∧ Fintype.card ι ≤ 19 ∧
      CharP K 2 ∧ ¬ 3 ∣ Nat.card ((LargeEvenScalars ι K).subgroupOf H)

end CFSG.StandardType

end
