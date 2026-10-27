module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsYam

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup
open CFSG.Quasithin (perfectCore)
open scoped commutatorElement

private theorem eq_bot_of_perfect_of_isSolvable_aux {X : Type*} [Group X] {K : Subgroup X}
    (hK : ⁅K, K⁆ = K) (hs : Group.IsSolvable K) : K = ⊥ := by
  have hc : commutator K = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_subtype_commutator, hK, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hd : ∀ k, derivedSeries K k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih, ← commutator_def, hc]
  obtain ⟨k, hk⟩ := (Group.isSolvable_def _).mp hs
  have htb : (⊤ : Subgroup K) = ⊥ := (hd k).symm.trans hk
  rw [eq_bot_iff]
  intro x hx
  have : (⟨x, hx⟩ : K) ∈ (⊥ : Subgroup K) := htb ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at this
  rw [Subgroup.mem_bot]
  exact congrArg Subtype.val this

theorem sup_perfectCore_eq_top_of_yamStd {C : Type} [Group C] [Finite C] [IsSimpleGroup C]
    {U P₀ P₁ : Subgroup C} (hY : CFSG.Quasithin.H13.Sec53F.Yam.YamStd C U P₀ P₁)
    (hsol : Group.IsSolvable ↥(P₀ ⊓ P₁))
    (hU₀ : U ≤ perfectCore P₀) (hU₁ : U ≤ perfectCore P₁) :
    perfectCore P₀ ⊔ perfectCore P₁ = ⊤ := by
  have hU : U ≠ ⊥ := by
    rintro rfl
    apply hY.coatom₀.1
    rw [eq_top_iff, ← Subgroup.normalizer_eq_top_iff.mpr (inferInstance : (⊥ : Subgroup C).Normal)]
    exact hY.le₀
  set X := perfectCore P₀ ⊔ perfectCore P₁ with hX
  have hP₀N : P₀ ≤ normalizer (perfectCore P₀ : Set C) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P₀)
  have hP₁N : P₁ ≤ normalizer (perfectCore P₁ : Set C) :=
    Subgroup.le_normalizer.trans (CFSG.Quasithin.normalizer_le_normalizer_perfectCore P₁)
  have hBN : normalizer (U : Set C) ≤ normalizer (X : Set C) := by
    intro g hg
    have h0 := hP₀N (hY.le₀ hg)
    have h1 := hP₁N (hY.le₁ hg)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h0 h1 ⊢
    rw [hX, Subgroup.map_sup, h0, h1]
  have hbot : ∀ {A : Subgroup C}, A ≤ P₀ ⊓ P₁ → ⁅A, A⁆ = A → A = ⊥ := by
    intro A hA hperf
    haveI := hsol
    exact eq_bot_of_perfect_of_isSolvable_aux hperf
      (solvable_of_solvable_injective (Subgroup.inclusion_injective hA))
  by_cases htop : normalizer (X : Set C) = ⊤
  · haveI : X.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal X with hb | ht
    · exact absurd (eq_bot_iff.mpr ((hU₀.trans le_sup_left).trans hb.le)) hU
    · exact ht
  · exfalso
    rcases hY.above _ hBN htop with h0 | h1
    · have hle : perfectCore P₁ ≤ P₀ ⊓ P₁ :=
        le_inf ((le_sup_right.trans Subgroup.le_normalizer).trans h0)
          (CFSG.Quasithin.perfectCore_le P₁)
      exact hU (eq_bot_iff.mpr (hU₁.trans
        (hbot hle (CFSG.Quasithin.perfectCore_perfect P₁)).le))
    · have hle : perfectCore P₀ ≤ P₀ ⊓ P₁ :=
        le_inf (CFSG.Quasithin.perfectCore_le P₀)
          ((le_sup_left.trans Subgroup.le_normalizer).trans h1)
      exact hU (eq_bot_iff.mpr (hU₀.trans
        (hbot hle (CFSG.Quasithin.perfectCore_perfect P₀)).le))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
