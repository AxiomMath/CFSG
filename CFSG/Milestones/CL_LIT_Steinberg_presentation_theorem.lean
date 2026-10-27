module

public import CFSG.LieType.Steinberg.Milestone

public section

namespace CFSG.Milestones

universe w

open CFSG.LieType.Universal CFSG.LieType.Steinberg in
theorem cl_lit_steinberg_presentation_theorem (t : CFSG.Assembly.LowTwoRank.StatedLieTag)
    (n p f : ℕ) [Fact p.Prime] (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible t n p f)
    (hrank : 3 ≤ bnRank t n) :
    PresentationA.{0, 0, w} (bnRootSystem (lieUniversal t n p f hadm.1))
        (lieUniversal t n p f hadm.1).D.rootGroup ∧
      (IsUntwistedTag t →
        IsParametrization (Φ := bnRootSystem (lieUniversal t n p f hadm.1))
            (lieUniversal t n p f hadm.1).D.rootGroup (untwistedParam t n p f hadm.1) ∧
          Nonempty (CommOrder (bnRootSystem (lieUniversal t n p f hadm.1))) ∧
          PresentationB (Φ := bnRootSystem (lieUniversal t n p f hadm.1))
            (untwistedParam t n p f hadm.1) ∧
          RedundantR2 (bnRootSystem (lieUniversal t n p f hadm.1))
            (lieUniversal t n p f hadm.1).D.rootGroup) :=
  steinberg_presentation t n p f hadm hrank

end CFSG.Milestones
