module

public import Certificates.Data.GrSLitL34FactsSpMultONCheck
import Certificates.Kernel.PresLetters.F22225A
import CFSG.Certificates.Kernel.Misc.Coset.TableFact
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.ONan
import all TauCeti.GroupTheory.Presentation.GroupPresentation
import all TauCeti.GroupTheory.Presentation.Relator

public section

open CFSG.ComponentClassification.GSThmB.SpMult CFSG.CosetTable

namespace Certificates

private theorem certificate22225_rels_eq :
    onCoverRels.map CFSG.KC.MiscCoset.encW = CFSG.KBRoute.F22225.rels := by
  decide

open CFSG.ComponentClassification.GSThmB.SpMult CFSG.CosetTable in
theorem certificate22225 : (genSub {r : FreeGroup (Fin onGens) | r ∈ onCoverRels.map FreeGroup.mk}
      (subsetOf onGens [0, 1, 2, 3, 4, 5])).FiniteIndex ∧
    (genSub {r : FreeGroup (Fin onGens) | r ∈ onCoverRels.map FreeGroup.mk}
      (subsetOf onGens [0, 1, 2, 3, 4, 5])).index ≤ 122760 := by
  have h := CFSG.KBFact.F22225
  rw [← certificate22225_rels_eq] at h
  exact CFSG.KC.MiscCoset.TableFact.genSub_index onCoverRels (by decide)
    (subsetOf onGens [0, 1, 2, 3, 4, 5]) h

end Certificates
