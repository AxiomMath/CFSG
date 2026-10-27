module

public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.LocalAnalysis.ComponentClassification.Components

public section

namespace CFSG.RankThree

open CFSG CFSG.RankThree.LocalRank

variable {G : Type*} [Group G] [Finite G]

theorem solvable_radical_subnormal_intersection {H : Subgroup G} (hH : H.IsSubnormal) :
    inSubgroup solvableRadical H = H ⊓ solvableRadical G ∧
      (Group.IsSolvable H → H ≤ solvableRadical G) :=
  ⟨CFSG.SignalizerFunctorTheorem.Nonsolvable.map_subtype_solvableRadical_eq_inf hH,
    CFSG.SignalizerFunctorTheorem.Nonsolvable.le_solvableRadical_of_isSubnormal hH⟩

omit [Finite G] in
theorem aschbacherSolvableCore_map_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A]
    {p : ℕ} (hp : p.Prime) (φ : A ≃* B) :
    (aschbacherSolvableCore p A).map φ.toMonoidHom = aschbacherSolvableCore p B := by
  have : Finite B := Finite.of_equiv A φ.toEquiv
  rw [aschbacherSolvableCore_eq_solvablePrimeComplementCore hp,
    aschbacherSolvableCore_eq_solvablePrimeComplementCore hp]
  exact CFSG.RankThreeEvenClassification.Helpers.solvablePrimeComplementCore_map_equiv p hp φ

theorem inSubgroup_aschbacherSolvableCore_top {p : ℕ} (hp : p.Prime) :
    inSubgroup (aschbacherSolvableCore p) (⊤ : Subgroup G) = aschbacherSolvableCore p G :=
  aschbacherSolvableCore_map_mulEquiv hp Subgroup.topEquiv

theorem solvable_prime_complement_core_subnormal_intersection {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : H.IsSubnormal) :
    inSubgroup (aschbacherSolvableCore p) H = H ⊓ aschbacherSolvableCore p G := by
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
    CFSG.RankThreeEvenClassification.Helpers.thetaCoreOf_subnormal_intersection p hp
      (CFSG.ComponentClassification.Components.chain_of_mathlib_subnormal hH),
    ← inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp, inSubgroup_aschbacherSolvableCore_top hp]

end CFSG.RankThree
