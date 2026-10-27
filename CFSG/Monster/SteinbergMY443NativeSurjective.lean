module

public import CFSG.YGroups.Y443.Native.Surjective
public import CFSG.YGroups.Y443.Native.TerminalInputs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster.Generated CFSG.Open

theorem y443_native_surjective_homomorphism :
    (∀ f : MonsterY443Derived →* Gmat, IsFM f →
      Function.Surjective f ∧ f.range = ⊤ ∧ Nonempty (MonsterY443Derived ⧸ f.ker ≃* Gmat)) ∧
    ∀ f : E443 →* Gmat, (∀ g : E443Gen, f (PresentedGroup.of g) = gGen g) →
      Function.Surjective f := by
  have hs : Function.Surjective fM := fM_surjective_of_order fM_terminal_order
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · obtain rfl := fM_unique_ax hf
    exact ⟨hs, MonoidHom.range_eq_top.2 hs, ⟨QuotientGroup.quotientKerEquivOfSurjective fM hs⟩⟩
  · obtain rfl := f443_unique hf
    intro y
    obtain ⟨m, rfl⟩ := hs y
    exact ⟨e443Phi.symm m, rfl⟩

end CFSG.YGroups.Y443
