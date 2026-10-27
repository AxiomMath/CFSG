module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.SchurFamilies.Even
public import CFSG.SignalizerFunctorTheorem.McBride.Models.SchurFamilies.Odd
public import CFSG.SignalizerFunctorTheorem.McBride.Models.SchurReduction
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem schur_family
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    {J : Type*} [Group J] [Finite J] (hJ : signalizerNearSimpleModel p J)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hrk : IsPGroup r π.ker) (hne : π.ker ≠ ⊥) :
    (r = 2 ∧ (Nonempty (J ≃* PSL(2, GaloisField 3 p)) ∨ (p = 3 ∧ Nonempty (J ≃* Sz 1)))) ∨
      (r = 3 ∧ Nonempty (J ≃* PSU3 2 p)) := by
  by_cases hr2 : r = 2
  · subst hr2
    left
    refine ⟨rfl, ?_⟩
    rcases hJ with h1 | h2 | ⟨n, hn, h3⟩ | h4
    · exact Or.inr (schur_two_kernel hp hp2 (Or.inl h1) π hπ hcen hrk hne)
    · exact Or.inl h2
    · exact Or.inr (schur_two_kernel hp hp2 (Or.inr (Or.inl ⟨n, hn, h3⟩)) π hπ hcen hrk hne)
    · exact Or.inr (schur_two_kernel hp hp2 (Or.inr (Or.inr h4)) π hπ hcen hrk hne)
  · have hodd : Odd (Nat.card π.ker) := by
      have : Fact r.Prime := ⟨hr⟩
      obtain ⟨k, hk⟩ := hrk.exists_card_eq
      rw [hk]
      exact (hr.eq_two_or_odd'.resolve_left hr2).pow
    rcases hJ with h1 | h2 | ⟨n, hn, h3⟩ | h4
    · exact absurd (schur_odd_psl2Even hp hp2 h1 π hπ hcen hodd) hne
    · exact absurd (schur_odd_psl2Three hp hp2 h2 π hπ hcen hodd) hne
    · have hpos : 0 < n := by
        have := hp.two_le
        omega
      exact absurd (schur_odd_sz hpos h3 π hπ hcen hodd) hne
    · right
      refine ⟨?_, h4⟩
      have hdvd := schur_odd_psu3 hp hp2 h4 π hπ hcen hodd
      have : Fact r.Prime := ⟨hr⟩
      obtain ⟨k, hk⟩ := hrk.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hne (Subgroup.card_eq_one.mp (by simpa using hk))
      rw [hk] at hdvd
      exact (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp ((dvd_pow_self r hk0).trans hdvd)

theorem schur_multiplier_input'
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime)
    {Y : Type*} [Group Y] [Finite Y] (L : Subgroup Y) [L.Normal]
    (hLc : L ≤ Subgroup.center Y) (hLr : IsPGroup r L) (hL1 : L ≠ ⊥)
    (hY : Group.IsPerfect Y) (hss : IsSemisimple (⊤ : Subgroup (Y ⧸ L)))
    (hnear : signalizerNearPSolvable p (Y ⧸ L)) :
    ∃ J ∈ lcalOf (Y ⧸ L),
      (r = 2 ∧ (Nonempty (↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) ∨
        (p = 3 ∧ Nonempty (↥J ≃* Sz 1)))) ∨
      (r = 3 ∧ Nonempty (↥J ≃* PSU3 2 p)) := by
  obtain ⟨J, hJ, K, ρ, hKperf, hρ, hρc, hρne, hρr⟩ :=
    exists_factor_central_cover L hLc hLr hL1 hY hss
  refine ⟨J, hJ, ?_⟩
  obtain ⟨-, hJs', hJnc⟩ := hJ
  have : IsSimpleGroup ↥J := hJs'
  have hnab : ∃ a b : ↥J, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    exact hJnc ⟨⟨fun a b => hcon a b⟩⟩
  have hmodel : signalizerNearSimpleModel p ↥J :=
    nearSimpleModel_of_isSectionOf hnear hnab (IsSectionOf.of_subgroup J)
  have := hKperf
  exact schur_family hp hp2 hr hmodel ρ hρ hρc hρr hρne

end CFSG.SignalizerFunctorTheorem.McBride
