module

public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.GroupTheory.HallHigmanPiCore

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGPCompCentQuasisimple (P : LargeEvenLabel → Prop) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ (L : Type) [Group L] [Finite L] (E : Subgroup (MulAut L))
    (y : MulAut L) (lab : LargeEvenLabel), LargeEvenInLambda2 lab → P lab →
    GGHasLabel lab (L ⧸ Subgroup.center L) → y ∈ E → orderOf y = p →
    LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I) →
    ∀ S : Subgroup L, LargeEvenPComponent p (ggAutFixedSubgroup y) S → CFSG.IsQuasisimple ↥S

end CFSG.StandardType

end
