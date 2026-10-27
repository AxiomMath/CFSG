module

public import CFSG.Permutation.FiveTransitive.NineAlternatingImageSectionAlgebra
public import CFSG.Permutation.FiveTransitive.NineAlternatingImageSectionLift
public import CFSG.Permutation.FiveTransitive.NineAlternatingDoubleImage

public section

namespace CFSG

namespace FiveTransitive.NineAlternatingImageSection

private theorem exists_equiv_and_lifts
    {G F E : Type*} [Group G] [Finite G]
    [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 9)
    (rho : G →* alternatingGroup F) (hrho : Function.Surjective rho)
    (sigma : G →* Equiv.Perm E) (hker : IsPGroup 5 sigma.ker) :
    ∃ e : alternatingGroup F ≃* alternatingGroup E,
      (∀ g : G, (e (rho g)).val = sigma g) ∧ rho.ker = sigma.ker ∧
      sigma.range = alternatingGroup E ∧
      ∀ u : alternatingGroup F, orderOf u = 2 →
        ∃ g : G, rho g = u ∧ orderOf g = 2 := by
  obtain ⟨e,hcompat,hkernels,himage⟩ :=
    NineAlternatingImageSectionAlgebra.exists_equiv hF hE rho hrho sigma hker
  have hkrho : IsPGroup 5 rho.ker := by rw [hkernels]; exact hker
  exact ⟨e,hcompat,hkernels,himage,fun u hu =>
    NineAlternatingImageSectionLift.exists_involution_lift rho hrho hkrho u hu⟩

theorem exists_double_lift
    {G F E : Type*} [Group G] [Finite G]
    [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
    (hF : Nat.card F = 9) (hE : Nat.card E = 9)
    (rho : G →* alternatingGroup F) (hrho : Function.Surjective rho)
    (sigma : G →* Equiv.Perm E) (hker : IsPGroup 5 sigma.ker) :
    ∃ g : G, orderOf g = 2 ∧
      Nat.card (Function.fixedPoints (rho g).val) = 5 ∧
      Nat.card (Function.fixedPoints (sigma g)) = 5 := by
  obtain ⟨e,hcompat,_,_,hlifts⟩ := exists_equiv_and_lifts hF hE rho hrho sigma hker
  let alpha : alternatingGroup F →* Equiv.Perm E :=
    (alternatingGroup E).subtype.comp e.toMonoidHom
  have hi : Function.Injective alpha := (alternatingGroup E).subtype_injective.comp e.injective
  obtain ⟨u,hu,huf,hue⟩ := NineAlternatingDoubleImage.exists_double hF hE alpha hi
  obtain ⟨g,hgu,hg⟩ := hlifts u hu
  refine ⟨g,hg,?_,?_⟩
  · rw [hgu]
    exact huf
  · have he : alpha u = sigma g := by
      rw [← hgu]
      exact hcompat g
    rwa [← he]

end FiveTransitive.NineAlternatingImageSection

end CFSG
