module

public import CFSG.LocalAnalysis.WeakClosure81.EightTailReduction
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G]

@[expose] def KBarOddQuotShape (V H T : Subgroup G) (P : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∃ (X : Type) (_ : Group X) (φ : ↥(kGenIn V H) →* X),
    IsBarMap (kGenIn V H) (Subgroup.centralizer (eSub V H T : Set G)) φ ∧
      P (X ⧸ fusionOddCore X)

@[expose] def Hyp85Three' (V H T : Subgroup G) : Prop :=
  (∃ m n : ℕ, 3 < m ∧ KBarCenterShape V H T (fun X _ => IsSpGp X m n) ∧ rankBarV V H T = n) ∨
    (∃ m n : ℕ, 3 < m ∧ KBarCenterShape V H T (fun X _ => IsPSUGp X m n) ∧
      rankBarV V H T = n) ∨
    (∃ m : ℕ, 3 < m ∧ KBarOddQuotShape V H T (fun X _ => IsSymGp X m))

@[expose] def W3Lem85ThreeFirst' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
      Hyp85Three' V H T →
        H = (H ⊓ Subgroup.normalizer (V : Set G)) ⊔
          (H ⊓ Subgroup.normalizer (E3.wClos V 0 T : Set G))

@[expose] def W3Shape86C' (G : Type) [Group G] [Finite G] : Prop :=
  ∀ V H T : Subgroup G, Hyp7 V → IsCalH V H → ¬ IsCalH0 V H →
    IsSylowIn 2 T (H ⊓ Subgroup.normalizer (V : Set G)) → H = kGenIn V H ⊔ T →
      Hyp85Three' V H T ∨ Shape86Delta' V H T ∨ Shape86WeakC V H T

end CFSG.LocalAnalysis.WeakClosure81

end
