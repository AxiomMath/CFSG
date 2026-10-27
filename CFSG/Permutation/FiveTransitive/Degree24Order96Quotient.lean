module

public import CFSG.Permutation.FiveTransitive.SimpleGoursat
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG

namespace FiveTransitive.Degree24

open Subgroup

theorem perm_six_factor_small_or_bijective
    (N F B : Type) [Group N] [Fintype N]
    [Fintype F] [DecidableEq F]
    [Fintype B] [DecidableEq B]
    (hFcard : Nat.card F = 6)
    (hBcard : Nat.card B = 6)
    (ρ : N →* Equiv.Perm F)
    (hρ : Function.Surjective ρ)
    (ψ : N →* Equiv.Perm B)
    (hker : ρ.ker ≤ ψ.ker) :
    Nat.card ψ.range < 360 ∨
      ∃ α : Equiv.Perm F →* Equiv.Perm B,
        Function.Bijective α ∧ α.comp ρ = ψ := by
  classical
  letI : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [← Nat.card_eq_fintype_card, hFcard]
      norm_num)
  let α : Equiv.Perm F →* Equiv.Perm B :=
    ρ.liftOfSurjective hρ ⟨ψ, hker⟩
  have hcomp : α.comp ρ = ψ := by
    simp [α]
  have hrangeEq : α.range = ψ.range := by
    ext q
    constructor
    · rintro ⟨x, hx⟩
      obtain ⟨n, hn⟩ := hρ x
      refine ⟨n, ?_⟩
      calc
        ψ n = α (ρ n) := by
          rw [← hcomp]
          rfl
        _ = α x := by rw [hn]
        _ = q := hx
    · rintro ⟨n, hn⟩
      refine ⟨ρ n, ?_⟩
      calc
        α (ρ n) = (α.comp ρ) n := rfl
        _ = ψ n := by rw [hcomp]
        _ = q := hn
  by_cases hα : Function.Injective α
  · right
    refine ⟨α, ?_, hcomp⟩
    apply
      (Nat.bijective_iff_injective_and_card α).mpr
    refine ⟨hα, ?_⟩
    rw [Nat.card_perm, Nat.card_perm,
      hFcard, hBcard]
  · left
    have hkerNe : α.ker ≠ ⊥ := by
      intro hbot
      exact hα (α.ker_eq_bot_iff.mp hbot)
    letI : Nontrivial α.ker :=
      α.ker.nontrivial_iff_ne_bot.mpr hkerNe
    have hAltLe :
        alternatingGroup F ≤ α.ker :=
      Equiv.Perm.alternatingGroup_le_of_normal
        (by rw [hFcard]; norm_num)
        (by infer_instance)
    have hAltCard :
        Nat.card (alternatingGroup F) = 360 := by
      rw [Nat.card_eq_fintype_card,
        card_alternatingGroup,
        ← Nat.card_eq_fintype_card, hFcard]
      norm_num
    have hdiv :
        Nat.card (alternatingGroup F) ∣
          Nat.card α.ker :=
      Subgroup.card_dvd_of_le hAltLe
    have hkerLower : 360 ≤ Nat.card α.ker := by
      rw [← hAltCard]
      exact Nat.le_of_dvd Nat.card_pos hdiv
    have hproduct :
        Nat.card α.ker * Nat.card α.range =
          Nat.card (Equiv.Perm F) := by
      rw [← Subgroup.index_ker]
      exact α.ker.card_mul_index
    have hPermCard :
        Nat.card (Equiv.Perm F) = 720 := by
      rw [Nat.card_perm, hFcard]
      norm_num
    rw [hPermCard] at hproduct
    rw [← hrangeEq]
    have hrangePos : 0 < Nat.card α.range :=
      Nat.card_pos
    have hscaled :
        360 * Nat.card α.range ≤ 720 := by
      calc
        360 * Nat.card α.range ≤
            Nat.card α.ker * Nat.card α.range :=
          Nat.mul_le_mul_right
            (Nat.card α.range) hkerLower
        _ = 720 := hproduct
    omega

end FiveTransitive.Degree24

end CFSG
