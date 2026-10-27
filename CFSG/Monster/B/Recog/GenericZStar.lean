module

public import CFSG.LocalAnalysis.ZStar
public import Mathlib.Data.Fintype.Shrink
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational

public section

namespace CFSG.Monster.B.Recog

universe u

theorem exists_conj_ne_commute_of_normal_odd₀ {G : Type} [Group G] [Finite G]
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) {t : G} (ht : orderOf t = 2)
    (hnc : t ∉ Subgroup.center G) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹) := by
  have := Fintype.ofFinite G
  by_contra h
  push Not at h
  have hiso : ∀ g : G, g * t * g⁻¹ * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := fun g hg => by
    by_contra hne
    exact h g hne hg
  have ht1 : t ≠ 1 := by
    rintro rfl
    simp at ht
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  obtain ⟨N, hN, hNodd, hNt⟩ := CFSG.ZStar.glauberman_zStar G t ht1 ht2 hiso
  have hbot := hO N hN hNodd
  apply hnc
  rw [Subgroup.mem_center_iff]
  intro g
  have := hNt g
  rw [hbot, Subgroup.mem_bot, mul_inv_eq_one] at this
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [this]

theorem exists_conj_ne_commute_of_normal_odd {G : Type u} [Group G] [Finite G]
    (hO : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥) {t : G} (ht : orderOf t = 2)
    (hnc : t ∉ Subgroup.center G) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹) := by
  let φ : Shrink.{0} G ≃* G := Shrink.mulEquiv
  have hO' : ∀ N : Subgroup (Shrink.{0} G), N.Normal → Odd (Nat.card N) → N = ⊥ := by
    intro N hN hodd
    have h₁ : (N.map φ.toMonoidHom).Normal := hN.map φ.toMonoidHom φ.surjective
    have h₂ : Nat.card (N.map φ.toMonoidHom) = Nat.card N :=
      Subgroup.card_map_of_injective φ.injective
    exact (Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 (hO _ h₁ (h₂ ▸ hodd))
  have ht' : orderOf (φ.symm t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hnc' : φ.symm t ∉ Subgroup.center (Shrink.{0} G) := fun h => hnc (by
    rw [Subgroup.mem_center_iff] at h ⊢
    intro g
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg φ (h (φ.symm g)))
  obtain ⟨g, hg₁, hg₂⟩ := exists_conj_ne_commute_of_normal_odd₀ hO' ht' hnc'
  refine ⟨φ g, fun h => hg₁ (φ.injective ?_), ?_⟩
  · rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    exact h
  · simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply] using congrArg φ hg₂

theorem exists_conj_ne_commute {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2) :
    ∃ g : G, g * t * g⁻¹ ≠ t ∧ g * t * g⁻¹ * t = t * (g * t * g⁻¹) := by
  refine exists_conj_ne_commute_of_normal_odd (fun N hN hodd => ?_) ht ?_
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
    · exact h
    · exfalso
      rw [h, Subgroup.card_top] at hodd
      have : 2 ∣ Nat.card G := ht ▸ orderOf_dvd_natCard t
      exact Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 this)
  · intro hc
    obtain ⟨a, b, hab⟩ := hnonab
    have ht1 : t ≠ 1 := by
      rintro rfl
      simp at ht
    have hcen : Subgroup.center G = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
      · exact absurd (h ▸ hc) (by simpa using ht1)
      · exact h
    exact hab (Subgroup.mem_center_iff.1 (hcen ▸ Subgroup.mem_top b) a)

end CFSG.Monster.B.Recog
