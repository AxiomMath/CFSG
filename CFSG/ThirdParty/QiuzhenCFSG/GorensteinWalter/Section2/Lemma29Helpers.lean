module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

namespace CFSG
end CFSG
open CFSG

/-!
# Elementary intersection endpoints for Lemma 2.9

The source proof of Lemma 2.9 first forces the distinguished involution into
one of two normal layers.  This module records the small lattice step that is
independent of the harder D-group and component arguments: a nonidentity
element common to two subgroups makes their intersection nontrivial.
-/

namespace CFSG.GorensteinWalter

universe u

/-- If a nonidentity element lies in both subgroups, their intersection is
nontrivial.  Keeping this generic avoids repeating the bottom-membership
argument in the Lemma 2.9 route. -/
public theorem subgroup_inf_ne_bot_of_mem_of_ne_one
    {G : Type u} [Group G]
    {A B : Subgroup G} {x : G}
    (hxA : x ∈ A) (hxB : x ∈ B) (hxne : x ≠ 1) :
    A ⊓ B ≠ ⊥ := by
  intro hbot
  have hxinf : x ∈ A ⊓ B := ⟨hxA, hxB⟩
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    rw [hbot] at hxinf
    exact hxinf
  exact hxne (by simpa using hxbot)

/-- The setup-specific disjunction used at the endpoint of Lemma 2.9. -/
public theorem lemma_2_9_t_mem_target
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    {V N : Subgroup G}
    (htV : c.t ∈ V)
    (ht : c.t ∈ twoCoreOf N ∨ c.t ∈ componentLayerOf N) :
    V ⊓ twoCoreOf N ≠ ⊥ ∨
      V ⊓ componentLayerOf N ≠ ⊥ := by
  rcases ht with ht2 | htE
  · exact Or.inl (subgroup_inf_ne_bot_of_mem_of_ne_one htV ht2 c.t_involution.1)
  · exact Or.inr (subgroup_inf_ne_bot_of_mem_of_ne_one htV htE c.t_involution.1)

end CFSG.GorensteinWalter
