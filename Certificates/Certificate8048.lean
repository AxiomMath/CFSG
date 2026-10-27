module

public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityVocab
import CFSG.Sporadic.Mathieu.M11
meta import CFSG.Sporadic.Mathieu.M11
meta import CFSG.Blueprint.NativeSporadic
meta import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityVocab

public section

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint

namespace CertificateChecks.Batch8048

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint

private theorem m11Rotation_commute_m11a : Commute m11Rotation m11a := by
  apply Subtype.ext
  decide +kernel

private theorem m11Reflection_commute_m11a : Commute m11Reflection m11a := by
  apply Subtype.ext
  decide +kernel

private theorem m11LocalThree_commute_m11a : Commute m11LocalThree m11a := by
  apply Subtype.ext
  decide +kernel

private theorem m11_centralizer_coordinates_commute_0 :
    ∀ x, m11CentralizerCoordinates x * m11a = m11a * m11CentralizerCoordinates x := fun x =>
  (((m11Rotation_commute_m11a.pow_left x.1.1.val).mul_left
    (m11Reflection_commute_m11a.pow_left x.1.2.val)).mul_left
      (m11LocalThree_commute_m11a.pow_left x.2.val)).eq

end CertificateChecks.Batch8048

namespace Certificates

open CertificateChecks

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate8048 : ∀ x, m11CentralizerCoordinates x * m11a = m11a * m11CentralizerCoordinates x := by
  exact CertificateChecks.Batch8048.m11_centralizer_coordinates_commute_0

end Certificates
