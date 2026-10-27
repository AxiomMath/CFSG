module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsWeakClosure
public import CFSG.LocalAnalysis.WeakClosure81.SevenOne

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22
open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem forall_conjSubgroup_eq_of_isTI {V₀ : Subgroup G} (h : CFSG.CGT.Timmesfeld75.IsTI V₀) :
    ∀ y : G, V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ → conjSubgroup V₀ y = V₀ := by
  intro y hy
  have h := h y⁻¹
  have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup y⁻¹ V₀ = conjSubgroup V₀ y := by
    rw [t75_conjSubgroup_eq, inv_inv]
  rw [hconj] at h
  rcases h with hbot | heq
  · exact absurd hbot hy
  · have hle : V₀ ≤ conjSubgroup V₀ y := by
      have h2 : V₀ ⊓ conjSubgroup V₀ y ≤ conjSubgroup V₀ y := inf_le_right
      rwa [heq] at h2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [E3.card_conjSubgroup])).symm

theorem isTI_form_conj {V₀ : Subgroup G}
    (hTI : ∀ y : G, V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ → conjSubgroup V₀ y = V₀) (g : G) :
    ∀ y : G, conjSubgroup V₀ g ⊓ conjSubgroup (conjSubgroup V₀ g) y ≠ ⊥ →
      conjSubgroup (conjSubgroup V₀ g) y = conjSubgroup V₀ g := by
  intro y hy
  set z := g * y * g⁻¹ with hz
  have hzy : z * g = g * y := by
    rw [hz]
    group
  have h2 : conjSubgroup (conjSubgroup V₀ g) y = conjSubgroup (conjSubgroup V₀ z) g := by
    rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup, hzy]
  have hzmem : V₀ ⊓ conjSubgroup V₀ z ≠ ⊥ := by
    intro hbot
    apply hy
    rw [h2, ← E3.conjSubgroup_inf, hbot, E3.conjSubgroup_bot]
  rw [h2, hTI z hzmem]

private theorem conjSubgroup_conj_mul {A : Subgroup G} (y g : G) :
    conjSubgroup (conjSubgroup A y) (y⁻¹ * g * y) =
      conjSubgroup (conjSubgroup A g) y := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  congr 1
  group

theorem inCalO_conj {n : ℕ} {M V₀ V : Subgroup G} (y g : G) :
    InCalO n (conjSubgroup M y) (conjSubgroup V₀ y) (conjSubgroup V y) (y⁻¹ * g * y) ↔
      InCalO n M V₀ V g := by
  simp only [InCalO, OFirst, ODual, conjSubgroup_conj_mul,
    E3.conjSubgroup_le_conjSubgroup_iff, E3.mQuot_conjSubgroup,
    ← E3.conjSubgroup_inf, ne_eq, CFSG.LocalAnalysis.UniquenessCase.PartTwo.conjSubgroup_eq_bot_iff]

end CFSG.LocalAnalysis.WeakClosure81
