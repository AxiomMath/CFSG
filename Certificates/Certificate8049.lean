module

public import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityCoordVocab
import CFSG.Sporadic.Mathieu.M11
meta import CFSG.Sporadic.Mathieu.M11
meta import CFSG.Blueprint.NativeSporadic
import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityVocab
meta import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityVocab
meta import CFSG.CharacterTheory.Semidihedral.ProperSubgroupRegularityCoordVocab
import Certificates.Certificate8048

public section

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint

namespace CertificateChecks.Batch8049

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint

private theorem m11LocalThreeC_perm :
    ((m11LocalThreeC : NativeSporadic.M11) : Equiv.Perm (Fin 11)) =
      List.formPerm [0, 2, 5] * List.formPerm [1, 6, 10] * List.formPerm [3, 9, 4] := by
  decide +kernel

private theorem m11ReflectionC_perm :
    ((m11ReflectionC : NativeSporadic.M11) : Equiv.Perm (Fin 11)) =
      List.formPerm [2, 5] * List.formPerm [3, 10] * List.formPerm [4, 8] *
        List.formPerm [6, 7] := by
  decide +kernel

private theorem m11Centralizer_eq_iff {g h : Subgroup.centralizer ({m11a} : Set NativeSporadic.M11)} :
    g = h ↔ ((g : NativeSporadic.M11) : Equiv.Perm (Fin 11)) = h :=
  Subtype.ext_iff.trans Subtype.ext_iff

private theorem m11_local_three_obstruction_facts_0 :
    m11LocalThreeC ≠ 1 ∧ m11LocalThreeC ^ 3 = 1 ∧
      (m11LocalThreeC * (m11ReflectionC * m11LocalThreeC * m11ReflectionC⁻¹)) ^ 2 ≠ 1 ∧
      (m11LocalThreeC * (m11ReflectionC * m11LocalThreeC * m11ReflectionC⁻¹)) ^ 4 = 1 := by
  simp only [ne_eq, m11Centralizer_eq_iff, Subgroup.coe_pow, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.coe_one, m11LocalThreeC_perm, m11ReflectionC_perm]
  decide +kernel

end CertificateChecks.Batch8049

namespace Certificates

open CertificateChecks

open CFSG CFSG.Semidihedral CFSG.Semidihedral.ProperSubgroupRegularity CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate8049 : 
    m11LocalThreeC ≠ 1 ∧ m11LocalThreeC ^ 3 = 1 ∧
      (m11LocalThreeC * (m11ReflectionC * m11LocalThreeC * m11ReflectionC⁻¹)) ^ 2 ≠ 1 ∧
      (m11LocalThreeC * (m11ReflectionC * m11LocalThreeC * m11ReflectionC⁻¹)) ^ 4 = 1 := by
  exact CertificateChecks.Batch8049.m11_local_three_obstruction_facts_0

end Certificates
