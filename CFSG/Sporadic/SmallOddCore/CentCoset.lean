module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Sporadic.SmallOddCore

open Subgroup

variable {G : Type*} [Group G]

theorem eq_one_of_mem_centralizer_simple {D : Subgroup G} (hs : IsSimpleGroup D)
    (hnab : ∃ a b : D, a * b ≠ b * a) {x : G} (hx : x ∈ D)
    (hc : x ∈ centralizer (D : Set G)) : x = 1 := by
  have hZ : center D = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (center D) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have hb : b ∈ center D := h ▸ mem_top b
      exact hab (mem_center_iff.1 hb a)
  have hcen : (⟨x, hx⟩ : D) ∈ center D := by
    rw [mem_center_iff]
    intro g
    exact Subtype.ext ((mem_centralizer_iff.1 hc) g g.2)
  rw [hZ, mem_bot] at hcen
  exact congrArg Subtype.val hcen

theorem card_inf_centralizer_le_of_cosets [Finite G] {C D : Subgroup G} (hDC : D ≤ C)
    (hs : IsSimpleGroup D) (hnab : ∃ a b : D, a * b ≠ b * a) {k : ℕ} (g : Fin k → G)
    (hg : ∀ i, g i ∈ C) (hdist : ∀ i j, i ≠ j → (g i)⁻¹ * g j ∉ D)
    (hC : Nat.card C = k * Nat.card D) (S : Finset (Fin k))
    (hS : ∀ i ∉ S, ∃ x ∈ D, ∀ d ∈ D, d * x * d⁻¹ ≠ (g i)⁻¹ * x * g i) :
    Nat.card ↥(C ⊓ centralizer (D : Set G)) ≤ S.card := by
  classical
  let F : Fin k × D → C := fun p => ⟨g p.1 * p.2, C.mul_mem (hg p.1) (hDC p.2.2)⟩
  have hF : Function.Injective F := by
    rintro ⟨i, d⟩ ⟨j, d'⟩ h
    have h' : g i * d = g j * d' := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hne
      apply hdist i j hne
      have e : (g i)⁻¹ * g j = d * (d' : G)⁻¹ := by
        calc (g i)⁻¹ * g j = (g i)⁻¹ * (g j * d') * (d' : G)⁻¹ := by group
          _ = (g i)⁻¹ * (g i * d) * (d' : G)⁻¹ := by rw [h']
          _ = d * (d' : G)⁻¹ := by group
      rw [e]
      exact D.mul_mem d.2 (D.inv_mem d'.2)
    subst hij
    have e : (d : G) = d' := mul_left_cancel h'
    exact Prod.ext rfl (Subtype.ext e)
  have hFb : Function.Bijective F := by
    apply hF.bijective_of_nat_card_le
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin, hC]
  have hdec : ∀ c : ↥(C ⊓ centralizer (D : Set G)), ∃ i ∈ S, ∃ d ∈ D, (c : G) = g i * d := by
    intro c
    obtain ⟨⟨i, d⟩, hp⟩ := hFb.2 ⟨c, (mem_inf.1 c.2).1⟩
    have he : (c : G) = g i * d := (congrArg Subtype.val hp).symm
    refine ⟨i, ?_, d, d.2, he⟩
    by_contra hi
    obtain ⟨x, hx, hne⟩ := hS i hi
    apply hne d d.2
    have hcx : x * (c : G) = c * x := mem_centralizer_iff.1 (mem_inf.1 c.2).2 x hx
    rw [he] at hcx
    calc (d : G) * x * (d : G)⁻¹ = (g i)⁻¹ * (g i * d * x) * (d : G)⁻¹ := by group
      _ = (g i)⁻¹ * (x * (g i * d)) * (d : G)⁻¹ := by rw [← hcx]
      _ = (g i)⁻¹ * x * g i := by group
  choose φ hφS hφ using hdec
  have hinj : Function.Injective (fun c => (⟨φ c, hφS c⟩ : S)) := by
    intro c c' h
    have hii : φ c = φ c' := congrArg Subtype.val h
    obtain ⟨d, hd, e⟩ := hφ c
    obtain ⟨d', hd', e'⟩ := hφ c'
    rw [hii] at e
    have hm : (c : G)⁻¹ * c' ∈ D := by
      have e2 : (c : G)⁻¹ * c' = (d : G)⁻¹ * d' := by rw [e, e']; group
      rw [e2]
      exact D.mul_mem (D.inv_mem hd) hd'
    have hz : (c : G)⁻¹ * c' ∈ centralizer (D : Set G) :=
      (mem_inf.1 ((C ⊓ centralizer (D : Set G)).mul_mem
        ((C ⊓ centralizer (D : Set G)).inv_mem c.2) c'.2)).2
    exact Subtype.ext (inv_mul_eq_one.1 (eq_one_of_mem_centralizer_simple hs hnab hm hz))
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := S), Fintype.card_coe] at h

end CFSG.Sporadic.SmallOddCore

end
