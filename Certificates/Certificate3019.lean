module

public import CFSG.Certificates.Kernel.AxisPlane.Orbit
public import Certificates.Data.Kernel.VisFrame.Gens
import Certificates.Kernel.VisFrame.Planes
import CFSG.Certificates.Kernel.AxisPlane.Two
public import Mathlib.Data.Set.Card

public section

namespace Certificates

open CertificateChecks

open CFSG.KC.AxisPlane CFSG.KC.VisFrame

open CFSG.KC.AxisPlane CFSG.KC.VisFrame in
theorem certificate3019 : ∀ r < 6, natOrbit gens (reps.getD r 0) ⊆ Set.Iio (2 ^ 24) ∧
    (natOrbit gens (reps.getD r 0)).ncard = sizes.getD r 0 ∧
    ∀ r' < 6, r ≠ r' → Disjoint (natOrbit gens (reps.getD r 0)) (natOrbit gens (reps.getD r' 0)) :=
  orbits_two (A := gen0.toArray) (B := gen1.toArray) (n := 6) (lam := fun r => reps.getD r 0)
    (size := fun r => sizes.getD r 0) KernelAP.VisFrame.R.chk rfl rfl rfl rfl rfl

end Certificates
