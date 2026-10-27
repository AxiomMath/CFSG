module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.LocalAnalysis.WeakClosure81.SevenThree

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G]

@[expose] def FiveTenConc (H M : Subgroup G) (Ω : Set (Subgroup G)) : Prop :=
  ∃ A ∈ Ω, A ≤ M ∧ ∃ H' : Subgroup G, H' ≤ H ∧ A ≤ H' ∧ kerMOf M H ≤ kerMOf M H' ∧
    ¬ A ≤ kerMOf M H' ∧ maxOver H' (A ⊔ kerMOf M H') = {M ⊓ H'}

structure FiveTenHyp (H M T : Subgroup G) (Ω : Set (Subgroup G)) : Prop where
  invColl : E1.IsInvColl H Ω
  sylow : IsSylowIn 2 T H
  normalizer_le : H ⊓ normalizer (E1.weakClosure T Ω : Set G) ≤ M
  not_le : ¬ H ≤ M

@[expose] def FiveTenAt (H M : Subgroup G) : Prop :=
  ∀ (T : Subgroup G) (Ω : Set (Subgroup G)), FiveTenHyp H M T Ω → FiveTenConc H M Ω

end CFSG.LocalAnalysis.WeakClosure81
