module

public import CFSG.YGroups.Y443.Native.Hom
public import CFSG.Monster.Generated.FiniteSimple

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.Generated CFSG.Monster.Griess CFSG.Open

theorem range_finite
    (f : MonsterY443Derived →* Gmat) : Finite f.range := by
  have : Finite Gmat := generated_rational_group_finite_simple.2.2
  infer_instance

theorem y443_derived_nontrivial_finite_image :
    (∃! f : MonsterY443Derived →* Gmat, IsFM f) ∧
      ∀ f : MonsterY443Derived →* Gmat, IsFM f →
        f (axElt y443U11) = ⟨tauB, tauB_mem_Gmat⟩ ∧ orderOf (f (axElt y443U11)) = 3 ∧
          f ≠ 1 ∧ Nontrivial f.range ∧ Finite f.range ∧ Group.IsPerfect f.range ∧
          f.ker ≠ ⊤ ∧ f.ker.Normal := by
  obtain ⟨hex, h⟩ := y443_derived_nontrivial_image
  refine ⟨hex, fun f hf => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h f hf
  exact ⟨h1, h2, h3, h4, range_finite f, h5, h6, h7⟩

end CFSG.YGroups.Y443
