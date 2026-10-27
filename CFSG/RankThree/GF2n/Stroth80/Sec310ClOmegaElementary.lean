module

public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaElementary

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry

theorem commutator_orthogonalGroup_eq_elementaryGroup_of_plusTwo
    (hP2 : ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
      ⁅TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K),
        TauCeti.QuadraticMap.orthogonalGroup (quadPlus 2 K)⁆ = elementaryGroup (quadPlus 2 K))
    {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (Qf : QuadraticForm K V) (h4K : 4 ≤ Nat.card K)
    (hQ : Qf.polarBilin.Nondegenerate) (h4 : 4 ≤ Module.finrank K V) :
    ⁅TauCeti.QuadraticMap.orthogonalGroup Qf, TauCeti.QuadraticMap.orthogonalGroup Qf⁆ =
      elementaryGroup Qf := by
  obtain ⟨m, hm⟩ :=
    (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
      Qf hQ).1
  have hm2 : 2 ≤ m := by omega
  rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus Qf hQ
      (by omega : 1 ≤ m) hm with ⟨⟨e⟩⟩ | ⟨b, c, hirr, ⟨e⟩⟩
  · rcases (by omega : m = 2 ∨ 3 ≤ m) with rfl | h3
    · exact derived_eq_elementary_isometry e.symm (hP2 K h4K)
    · exact derived_eq_elementary_isometry e.symm (commutator_orthogonalGroup_quadPlus h3)
  · exact derived_eq_elementary_isometry e.symm
      (commutator_orthogonalGroup_quadMinus_of_two_le hm2 hirr)

end CFSG.RankThree.GF2n.Stroth80.Classify
