module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLatCheck

public section

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice

namespace CertificateChecks.Batch450102

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice

private theorem lattice_orbits : latticeOrbitsProp := by
  decide +kernel

private theorem lattice_r0 : r0Prop := by
  decide +kernel

end CertificateChecks.Batch450102

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.CocodeModelLattice in
theorem certificate450102 : latticeProp :=
  ⟨CertificateChecks.Batch450102.lattice_orbits, CertificateChecks.Batch450102.lattice_r0⟩

end Certificates
