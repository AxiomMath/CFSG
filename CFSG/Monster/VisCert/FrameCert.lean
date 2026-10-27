module

public import Certificates.Certificate3019

public section

namespace CFSG.Monster.VisCert

open CFSG.KC.AxisPlane CFSG.KC.VisFrame

theorem frameOrbits :
    ∀ r < 6, natOrbit gens (reps.getD r 0) ⊆ Set.Iio (2 ^ 24) ∧
      (natOrbit gens (reps.getD r 0)).ncard = sizes.getD r 0 ∧
      ∀ r' < 6, r ≠ r' →
        Disjoint (natOrbit gens (reps.getD r 0)) (natOrbit gens (reps.getD r' 0)) :=
  Certificates.certificate3019

end CFSG.Monster.VisCert
