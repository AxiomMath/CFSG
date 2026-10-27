module

public import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
public import Mathlib.Data.Finset.Attr
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

variable {G : Type*} [Group G] {P Q H L : Subgroup G}

theorem commutator_quotient_le_map_of_factor [(Q.subgroupOf P).Normal] (hQP : Q ≤ P)
    (hHP : H ≤ P) (hLP : L ≤ P) (hfac : ∀ g ∈ P, ∃ q ∈ Q, ∃ h ∈ H, ∃ l ∈ L, g = q * (h * l))
    (hHN : H ≤ Subgroup.normalizer (L : Set G)) (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a) :
    commutator (↥P ⧸ Q.subgroupOf P) ≤
      (L.subgroupOf P).map (QuotientGroup.mk' (Q.subgroupOf P)) := by
  set π := QuotientGroup.mk' (Q.subgroupOf P) with hπdef
  have hπ : ∀ p : ↥P, ∃ h, ∃ hh : h ∈ H, ∃ l, ∃ hl : l ∈ L,
      π p = π ⟨h, hHP hh⟩ * π ⟨l, hLP hl⟩ := by
    intro p
    obtain ⟨q, hq, h, hh, l, hl, hp⟩ := hfac p p.2
    refine ⟨h, hh, l, hl, ?_⟩
    have hp' : p = ⟨q, hQP hq⟩ * (⟨h, hHP hh⟩ * ⟨l, hLP hl⟩) := Subtype.ext hp
    have hq1 : π ⟨q, hQP hq⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).2 (show (⟨q, hQP hq⟩ : ↥P) ∈ Q.subgroupOf P from hq)
    rw [hp', map_mul, map_mul, hq1, one_mul]
  set L₀ := (L.subgroupOf P).map π with hL₀def
  set C₀ := (H.subgroupOf P).map π with hC₀def
  haveI hL₀n : L₀.Normal := ⟨fun x hx y => by
    obtain ⟨⟨l', hl'P⟩, hl', rfl⟩ := hx
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf P) y
    obtain ⟨h, hh, l, hl, hp⟩ := hπ p
    replace hl' : l' ∈ L := hl'
    refine ⟨(⟨h, hHP hh⟩ * ⟨l, hLP hl⟩) * ⟨l', hl'P⟩ * (⟨h, hHP hh⟩ * ⟨l, hLP hl⟩)⁻¹, ?_, ?_⟩
    · show h * l * l' * (h * l)⁻¹ ∈ L
      have h1 : l * l' * l⁻¹ ∈ L := mul_mem (mul_mem hl hl') (inv_mem hl)
      have h2 := (Subgroup.mem_normalizer_iff.1 (hHN hh) _).1 h1
      have h3 : h * (l * l' * l⁻¹) * h⁻¹ = h * l * l' * (h * l)⁻¹ := by group
      rw [h3] at h2
      exact h2
    · show π _ = π p * π ⟨l', hl'P⟩ * (π p)⁻¹
      rw [hp, map_mul, map_mul, map_inv, map_mul]⟩
  have hsup : L₀ ⊔ C₀ = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf P) y
    obtain ⟨h, hh, l, hl, hp⟩ := hπ p
    show π p ∈ L₀ ⊔ C₀
    rw [hp]
    exact mul_mem (Subgroup.mem_sup_right ⟨⟨h, hHP hh⟩, hh, rfl⟩)
      (Subgroup.mem_sup_left ⟨⟨l, hLP hl⟩, hl, rfl⟩)
  have hC₀ : IsMulCommutative ↥C₀ := IsMulCommutative.of_comm fun a b => by
    obtain ⟨_, ⟨a', ha', rfl⟩⟩ := a
    obtain ⟨_, ⟨b', hb', rfl⟩⟩ := b
    apply Subtype.ext
    show π a' * π b' = π b' * π a'
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext (hHc _ ha' _ hb'))
  exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hC₀

theorem nonempty_mulEquiv_map_subgroupOf_of_inf_eq_bot [(Q.subgroupOf P).Normal] (hLP : L ≤ P)
    (hLQ : L ⊓ Q = ⊥) :
    Nonempty (↥((L.subgroupOf P).map (QuotientGroup.mk' (Q.subgroupOf P))) ≃* ↥L) := by
  let φ : ↥L →* ↥P ⧸ Q.subgroupOf P := (QuotientGroup.mk' _).comp (Subgroup.inclusion hLP)
  have hφ : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hl
    have hlLQ : (l : G) ∈ L ⊓ Q := ⟨l.2, hl⟩
    rw [hLQ, Subgroup.mem_bot] at hlLQ
    exact (Subgroup.mem_bot).2 (Subtype.ext hlLQ)
  have hrange : φ.range = (L.subgroupOf P).map (QuotientGroup.mk' (Q.subgroupOf P)) := by
    ext y
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLP l, l.2, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨⟨p, hp⟩, rfl⟩
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hφ).symm⟩

end CFSG.RankThree.GF2n.Stroth80

end
