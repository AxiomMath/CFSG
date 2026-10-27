module

public import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
public import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
public import TauCeti.RingTheory.Smooth.Regular

public section

namespace CFSG

universe u v
variable {k : Type u} [Field k]

theorem isDomain_of_isRegularRing_of_connectedSpace (R : Type v) [CommRing R]
    [IsRegularRing R] [ConnectedSpace (PrimeSpectrum R)] : IsDomain R := by
  let : ConnectedSpace (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
    inferInstanceAs (ConnectedSpace (PrimeSpectrum R))
  let : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
    TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk _
  exact (AlgebraicGeometry.affine_isIntegral_iff (CommRingCat.of R)).1 inferInstance

theorem isDomain_of_smooth_of_connected (R : Type v) [CommRing R] [Algebra k R]
    [Algebra.Smooth k R] [ConnectedSpace (PrimeSpectrum R)] : IsDomain R := by
  let : IsRegularRing R := TauCeti.IsRegularRing.of_smooth (R := k)
  exact isDomain_of_isRegularRing_of_connectedSpace R

end CFSG
