module

public import CFSG.LocalAnalysis.StandardType.GGTPNRegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmRABase
public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGCentJRank (p : ℕ) (X : Type) [Group X] (J : Subgroup X) : Prop :=
  (Nat.card (Subgroup.center X)).Coprime p → ∀ E : Subgroup X, IsElemAbelian p E →
    (∀ z ∈ E, ∀ j ∈ J, z * j = j * z) → Nat.card E ≤ p

@[expose] def GGA2EightExcPair : Prop :=
  GGTablePKnownR fun p n labJ labX => GGRegimeA2Eight p n labJ labX ∧ GGKacExcPair labX p

@[expose] def GGA2EightNonExc : Prop :=
  GGTablePKnownR fun p n labJ labX =>
    GGRegimeA2Eight p n labJ labX ∧ ¬ GGTPNClTag labX.tag ∧ ¬ GGTPNExcTag labX.tag

end CFSG.StandardType

end
