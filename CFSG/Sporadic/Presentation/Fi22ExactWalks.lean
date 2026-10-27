module

public import CFSG.Sporadic.Presentation.Fi22ExactData
public import CFSG.Certificates.CentralizerWalks
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import CFSG.Sporadic.Presentation.Fi22ExactWalksInputs
public import Certificates.Certificate9110
public meta import CFSG.Sporadic.Presentation.Fi22ExactData
public meta import CFSG.Certificates.CentralizerWalks
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import TauCeti.GroupTheory.SpecificGroups.CFSG.Index
import all TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public meta import Mathlib
public import Mathlib

public section

namespace CFSG.Sporadic.Presentation.Fi22Exact

open CFSG.CosetTable CFSG.Certificates CFSG.Certificates.CosetEnumeration

private theorem presentation_eq :
    TauCeti.SporadicName.Fi22.presentation = TauCeti.Sporadic.fi22Presentation := rfl

theorem gc_eq : gc = 2 := by
  have : TauCeti.SporadicName.Fi22.presentation.generatorCount = 2 := by
    rw [presentation_eq]; simp [TauCeti.GroupPresentation.generatorCount]
  exact this

abbrev ga : Fin gc := ⟨0, by rw [gc_eq]; decide⟩

abbrev gb : Fin gc := ⟨1, by rw [gc_eq]; decide⟩

theorem pairs_agree {pp : Conj × Conj} (hpp : pp ∈ allPairs) :
    (evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk})
        (gW pp.1.1 pp.1.2))⁻¹ *
      presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk} 0 *
      evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}) (gW pp.1.1 pp.1.2) =
    (evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk})
        (gW pp.2.1 pp.2.2))⁻¹ *
      presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk} 0 *
      evalWord (presLetter {r : FreeGroup (Fin gc) | r ∈ W0.map FreeGroup.mk}) (gW pp.2.1 pp.2.2) :=
  Certificates.certificate9110 pp hpp

end CFSG.Sporadic.Presentation.Fi22Exact
