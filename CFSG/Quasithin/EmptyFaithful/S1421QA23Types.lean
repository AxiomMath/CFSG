module

public import CFSG.Quasithin.EmptyFaithful.S1421QA23Rk
public import CFSG.Quasithin.EmptyFaithful.S1421QA23U33
public import CFSG.Quasithin.EmptyFaithful.S1421QA23Setup

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace QA23

theorem not_isSolvable_of_isQuasisimple {X : Type} [Group X] [Finite X]
    (hXq : CFSG.IsQuasisimple X) : ¬ Group.IsSolvable X := by
  have hperf : Group.IsPerfect X := hXq.1
  have : Nontrivial X := by
    obtain ⟨a, b, hab⟩ := hXq.2.2
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hab
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y => exact congrArg QuotientGroup.mk (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable X

theorem borel_of_listAD
    {X : Type} [Group X] [Finite X] (hXq : CFSG.IsQuasisimple X) (hO2 : CFSG.pCore 2 X = ⊥)
    (hl : ListAD X) (hnC : ¬ (IsPSL 4 2 1 X ∨ IsPSL 5 2 1 X))
    (hA7 : ¬ IsAlt 7 (X ⧸ Subgroup.center X))
    {U A K : Subgroup X} (hU : IsSylowTwoOf U ⊤) (hUA : U ≤ A) (hA : Group.IsSolvable ↥A)
    (hKp : ⁅K, K⁆ = K) (hKne : K ≠ ⊥) (hKU : K ⊔ U ≠ ⊤)
    (hKB : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K)) :
    A ≤ Subgroup.normalizer (U : Set X) := by
  rcases hl with ⟨n, hn, h⟩ | hB | hCt | hD
  · refine normalizer_of_isPSL_two h hU hUA ?_
    rintro rfl
    exact not_isSolvable_of_isQuasisimple hXq
      (Group.isSolvable_of_surjective (f := (⊤ : Subgroup X).subtype) (by
        intro x
        exact ⟨⟨x, trivial⟩, rfl⟩))
  · exact solvableOvergroupsNormalize_of_typeB hO2 hB hU A hUA hA
  · exact (hnC hCt).elim
  · rcases hD with h7 | h32 | h6 | h33
    · exact absurd h7 hA7
    · exact (false_of_isPSL_three_two hXq h32 hKp hKne hKU).elim
    · exact (false_of_isAlt_six hXq h6 hU hKp hKne hKU).elim
    · exact (false_of_isPSU_three_three hXq h33 hU hKp hKne hKU hKB).elim

end QA23

end CFSG.Quasithin
