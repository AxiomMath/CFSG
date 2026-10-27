module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.YGroups

variable {G : Type*} [Group G]

structure DoubleCosetData (H C : Subgroup G) (t : G) (r : ℕ) where
  x : Fin r → G
  S : Fin r → Subgroup G
  rep : Fin r → Finset G
  tgt : (i : Fin r) → G → Fin r
  tgtElt : (i : Fin r) → G → G
  base : Fin r
  base_mem : x base ∈ H
  S_le : ∀ i, S i ≤ H
  S_conj : ∀ i, ∀ s ∈ S i, x i * s * (x i)⁻¹ ∈ H
  rep_le : ∀ i, ∀ k ∈ rep i, k ∈ H
  rep_cover : ∀ i, ∀ h ∈ H, ∃ k ∈ rep i, ∃ s ∈ S i, ∃ c ∈ C, h = s * k * c
  tgtElt_mem : ∀ i, ∀ k ∈ rep i, tgtElt i k ∈ H
  tgt_spec : ∀ i, ∀ k ∈ rep i, x i * k * t * (x (tgt i k) * tgtElt i k)⁻¹ ∈ H

namespace DoubleCosetData

variable {H C : Subgroup G} {t : G} {r : ℕ} (D : DoubleCosetData H C t r)

theorem mul_t_mem (hCH : C ≤ H) (htC : ∀ c ∈ C, t * c = c * t) (i : Fin r) {h : G}
    (hh : h ∈ H) : ∃ j : Fin r, ∃ a ∈ H, ∃ b ∈ H, D.x i * h * t = a * D.x j * b := by
  obtain ⟨k, hk, s, hs, c, hc, rfl⟩ := D.rep_cover i h hh
  refine ⟨D.tgt i k, D.x i * s * (D.x i)⁻¹ * (D.x i * k * t * (D.x (D.tgt i k) * D.tgtElt i k)⁻¹),
    H.mul_mem (D.S_conj i s hs) (D.tgt_spec i k hk), D.tgtElt i k * c,
    H.mul_mem (D.tgtElt_mem i k hk) (hCH hc), ?_⟩
  have := htC c hc
  calc D.x i * (s * k * c) * t = D.x i * s * k * (c * t) := by group
    _ = D.x i * s * k * (t * c) := by rw [this]
    _ = _ := by group

theorem exists_eq_of_doubleCoset_data (hCH : C ≤ H) (ht : t * t = 1)
    (htC : ∀ c ∈ C, t * c = c * t) (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤) (g : G) :
    ∃ i : Fin r, ∃ a ∈ H, ∃ b ∈ H, g = a * D.x i * b := by
  have hg : g ∈ Subgroup.closure ((H : Set G) ∪ {t}) := hgen ▸ Subgroup.mem_top g
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  induction hg using Subgroup.closure_induction_right with
  | one =>
    exact ⟨D.base, (D.x D.base)⁻¹, H.inv_mem D.base_mem, 1, H.one_mem, by group⟩
  | mul_right g _ y hy ih =>
    obtain ⟨i, a, ha, b, hb, rfl⟩ := ih
    rcases hy with hy | hy
    · exact ⟨i, a, ha, b * y, H.mul_mem hb hy, by group⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy]
      obtain ⟨j, a', ha', b', hb', he⟩ := D.mul_t_mem hCH htC i hb
      refine ⟨j, a * a', H.mul_mem ha ha', b', hb', ?_⟩
      calc a * D.x i * b * t = a * (D.x i * b * t) := by group
        _ = a * (a' * D.x j * b') := by rw [he]
        _ = _ := by group
  | mul_inv_cancel g _ y hy ih =>
    obtain ⟨i, a, ha, b, hb, rfl⟩ := ih
    rcases hy with hy | hy
    · exact ⟨i, a, ha, b * y⁻¹, H.mul_mem hb (H.inv_mem hy), by group⟩
    · rw [Set.mem_singleton_iff] at hy
      rw [hy, htinv]
      obtain ⟨j, a', ha', b', hb', he⟩ := D.mul_t_mem hCH htC i hb
      refine ⟨j, a * a', H.mul_mem ha ha', b', hb', ?_⟩
      calc a * D.x i * b * t = a * (D.x i * b * t) := by group
        _ = a * (a' * D.x j * b') := by rw [he]
        _ = _ := by group

theorem mk_mul_inv_eq {i : Fin r} {k k' : G} (h : k⁻¹ * k' ∈ D.S i) :
    ((k * (D.x i)⁻¹ : G) : G ⧸ H) = ((k' * (D.x i)⁻¹ : G) : G ⧸ H) := by
  rw [QuotientGroup.eq]
  have := D.S_conj i _ h
  rw [show (k * (D.x i)⁻¹)⁻¹ * (k' * (D.x i)⁻¹) = D.x i * (k⁻¹ * k') * (D.x i)⁻¹ by group]
  exact this

theorem index_le_sum (hCH : C ≤ H) (ht : t * t = 1) (htC : ∀ c ∈ C, t * c = c * t)
    (hgen : Subgroup.closure ((H : Set G) ∪ {t}) = ⊤) [Finite H] :
    H.FiniteIndex ∧ H.index ≤ ∑ i, (D.S i).relIndex H := by
  classical
  let φ : (Σ i : Fin r, H ⧸ (D.S i).subgroupOf H) → G ⧸ H := fun p =>
    Quotient.liftOn' p.2 (fun k : H => ((k * (D.x p.1)⁻¹ : G) : G ⧸ H)) (by
      intro k k' hkk'
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hkk'
      exact D.mk_mul_inv_eq (by simpa using hkk'))
  have hsurj : Function.Surjective φ := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨i, a, ha, b, hb, hab⟩ := D.exists_eq_of_doubleCoset_data hCH ht htC hgen g⁻¹
      refine ⟨⟨i, ((⟨b⁻¹, H.inv_mem hb⟩ : H) : H ⧸ (D.S i).subgroupOf H)⟩, ?_⟩
      show ((b⁻¹ * (D.x i)⁻¹ : G) : G ⧸ H) = (g : G ⧸ H)
      rw [QuotientGroup.eq]
      have hg : g = b⁻¹ * (D.x i)⁻¹ * a⁻¹ := by
        rw [← inv_inv g, hab]; group
      rw [hg]
      have : (b⁻¹ * (D.x i)⁻¹)⁻¹ * (b⁻¹ * (D.x i)⁻¹ * a⁻¹) = a⁻¹ := by group
      rw [this]
      exact H.inv_mem ha
  have hfin : ∀ i, Finite (H ⧸ (D.S i).subgroupOf H) := fun i => inferInstance
  have : Finite (G ⧸ H) := Finite.of_surjective φ hsurj
  refine ⟨Subgroup.finiteIndex_of_finite_quotient, ?_⟩
  calc H.index = Nat.card (G ⧸ H) := Subgroup.index_eq_card H
    _ ≤ Nat.card (Σ i : Fin r, H ⧸ (D.S i).subgroupOf H) := Nat.card_le_card_of_surjective φ hsurj
    _ = ∑ i, Nat.card (H ⧸ (D.S i).subgroupOf H) := Nat.card_sigma
    _ = ∑ i, (D.S i).relIndex H := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Subgroup.relIndex, Subgroup.index_eq_card]

end DoubleCosetData

end CFSG.YGroups
