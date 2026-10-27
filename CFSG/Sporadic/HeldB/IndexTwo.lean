module

public import CFSG.Sporadic.HeldB.AllFixed
public import CFSG.Sporadic.HeldB.IndexTwoCore

public noncomputable section

namespace CFSG.Sporadic.HeldB

open CFSG.ComponentClassification

theorem Held_index_two_B_under_proper_subgroup_B
    {G : Type} [Group G] [Finite G]
    [IsSimpleGroup (GeneralizedFitting.subgroup G)]
    (hnonab : ∃ a b : GeneralizedFitting.subgroup G, a * b ≠ b * a)
    (hindex : (GeneralizedFitting.subgroup G).index ≤ 2)
    (hiso : Nonempty (GeneralizedFitting.subgroup G ≃* Blueprint.NativeSporadic.He))
    (hproper : ∀ X : Subgroup G, X ≠ ⊤ → CentralTwoBInclusion.Property X) :
    (∀ S : Subgroup G, S ≠ ⊥ → IsPGroup 2 S →
      TwoComponents.badSubgroup (Subgroup.normalizer (S : Set G)) = ⊥) ∧
    CentralTwoBInclusion.Property G :=
  index_two_B_of_fixed_model hnonab hindex (hiso.some.trans heEquivP)
    (fun α hα L hL => ctbh_all_involution_automorphism_fixed_p_components ⟨heEquivP.symm⟩ α hα L
      hL) hproper

end CFSG.Sporadic.HeldB
