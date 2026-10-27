module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327

open CFSG.Blueprint (LieModel)
open UC326 (jOf)

structure Hyp327 (G : Type) [Group G] [Finite G] (P A : Subgroup G) : Prop where
  kgroup : CFSG.Open.IsKGroup G
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P ⊤
  jA : A = jOf P
  elem : CFSG.Open.IsElemAbelian 3 A
  card : Nat.card A = 27
  shape : A = P ∨ Nonempty (↥P ≃* (Multiplicative (ZMod 3) ≀ᵣ Multiplicative (ZMod 3)))

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC327
