
module

public import CFSG.Milestones.ASVolI.C31.J4NP.Is2AAffNative
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Milestones.ASVolI.C31.J4NP.HClDefs

@[expose] public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.J4Tree.Native CFSG.ASVolI
open CFSG.Quasithin.J4Loc (z0)

theorem burnsideJ4NP_affine2A_eq_with (a : Code) :
    burnsideJ4NP_affine2A a = burnsideJ4NP_affine2AWith (burnsideJ4NP_sextArr ()) a :=
  rfl

theorem burnsideJ4NP_Is2A_iff_isConj (x : J) : burnsideJ4NP_Is2A x ↔ IsConj x z0 := by
  constructor
  · rintro ⟨g, rfl⟩
    exact isConj_iff.2 ⟨g⁻¹, by group⟩
  · intro h
    obtain ⟨g, hg⟩ := isConj_iff.1 h
    exact ⟨g⁻¹, by rw [← hg]; group⟩

end CFSG.ASVolI
