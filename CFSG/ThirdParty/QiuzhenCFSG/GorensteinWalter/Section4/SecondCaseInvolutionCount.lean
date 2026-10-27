module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseFactorization
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.InvolutionCountInSubgroup

namespace CFSG
end CFSG
open CFSG

/-!
# The involution count inside the selected second-case component
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- In the selected component, the component-fusion theorem makes all
involutions conjugate to `t` inside `E`.  Consequently the ambient count of
involutions lying in `E` is the index of `C_E(t)`. -/
public theorem secondCase_component_involutions_card_eq_centralizer_index
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w) :
    Nat.card {x : G // IsInvolution x ∧ x ∈ d.E} =
      (Subgroup.centralizer
        ({⟨c.t, d.t_mem_E⟩} : Set d.E)).index := by
  have hfuse : ∀ x : d.E, IsInvolution x →
      ∃ g : d.E, g * x * g⁻¹ = ⟨c.t, d.t_mem_E⟩ := by
    intro x hx
    have hxG : IsInvolution (x : G) := by
      constructor
      · intro h1
        apply hx.1
        apply Subtype.ext
        exact h1
      · simpa [pow_two] using congrArg Subtype.val hx.2
    obtain ⟨g, hgE, hg⟩ :=
      secondCase_involutions_fused w d (x : G)
        x.property hxG
    refine ⟨⟨g, hgE⟩, ?_⟩
    apply Subtype.ext
    exact hg
  exact involutions_in_subgroup_card_eq_centralizer_index
    d.E c.t d.t_mem_E c.t_involution hfuse

end CFSG.GorensteinWalter
