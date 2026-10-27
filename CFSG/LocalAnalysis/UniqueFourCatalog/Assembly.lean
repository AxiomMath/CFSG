module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Alternating
public import CFSG.LocalAnalysis.UniqueFourCatalog.Sporadic
public import CFSG.LocalAnalysis.UniqueFourCatalog.Classical
public import CFSG.LocalAnalysis.UniqueFourCatalog.Exceptional

open CFSG.Open
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Blueprint

theorem false_of_cyclic {G : Type} [Group G] [Finite G] (hS : Standing4 G) {p : ℕ}
    (e : G ≃* Multiplicative (ZMod p)) : False := by
  obtain ⟨a, b, hab⟩ := hS.nonab
  exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))

section Final

set_option linter.unusedSectionVars false


theorem catalogNoUniqueFour_of_oddExceptional
    (h₁ : TwistedE6OddExclusion)
    (h₂ : TrialityD4OddExclusion) (h₃ : UntwistedExceptionalOddExclusion) :
    CFSG.Yardstones.Mf4cdcdf2e013.CatalogNoUniqueFour := by
  intro G _ _ hS hC
  rcases hC with ⟨p, hp, ⟨e⟩⟩ | ⟨n, hn, ⟨e⟩⟩ | ⟨t, n, p, f, hcl⟩ | hexc | ⟨s, ⟨e⟩⟩
  · exact fun _ => false_of_cyclic hS e
  · exact fun _ => (CFSG.Yardstones.Mf4cdcdf2e013.Standing4.false_of_alternating hS e).elim
  · exact not_uniqueFour_of_statedClassicalModel hS hcl
  · exact not_uniqueFour_of_exceptionalRep h₁ h₂ h₃ hS hexc
  · exact not_uniqueFour_of_sporadic hS s e

end Final

end CFSG.LocalAnalysis.UniqueFourCatalog
