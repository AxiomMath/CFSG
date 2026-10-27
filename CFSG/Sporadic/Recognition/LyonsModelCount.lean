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

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Subgroup

theorem image_inv_mem_of_image_mem {Ω : Type*} [Finite Ω] (𝓕 : Set (Set Ω)) (a : Perm Ω)
    (h : ∀ S ∈ 𝓕, a '' S ∈ 𝓕) : ∀ S ∈ 𝓕, (a⁻¹ : Perm Ω) '' S ∈ 𝓕 := by
  have hfin : 𝓕.Finite := Set.toFinite 𝓕
  have hinj : Set.InjOn (fun S : Set Ω => a '' S) 𝓕 :=
    ((Equiv.injective a).image_injective).injOn
  have hbij := (hfin.injOn_iff_bijOn_of_mapsTo (f := fun S : Set Ω => a '' S)
    (fun S hS => h S hS)).1 hinj
  intro S hS
  obtain ⟨T, hT, rfl⟩ := hbij.surjOn hS
  simpa [Set.image_image] using hT

open scoped Pointwise in
theorem exists_subgroup_ncard_mul_card_eq {Ω : Type*} (B : Subgroup (Perm Ω))
    (F : Set Ω) (𝓕 : Set (Set Ω)) (hcov : ∀ S ∈ 𝓕, ∃ g ∈ B, S = g '' F)
    (hmem : ∀ g ∈ B, g '' F ∈ 𝓕) :
    ∃ K : Subgroup (Perm Ω), (∀ g, g ∈ K ↔ g ∈ B ∧ g '' F = F) ∧
      𝓕.ncard * Nat.card K = Nat.card B := by
  classical
  have horb : MulAction.orbit B F = 𝓕 := by
    ext S
    constructor
    · rintro ⟨b, rfl⟩
      exact hmem b b.2
    · intro hS
      obtain ⟨g, hg, rfl⟩ := hcov S hS
      exact ⟨⟨g, hg⟩, rfl⟩
  refine ⟨(MulAction.stabilizer B F).map B.subtype, ?_, ?_⟩
  · intro g
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨b.2, hb⟩
    · rintro ⟨hg, hF⟩
      exact ⟨⟨g, hg⟩, hF, rfl⟩
  · rw [Subgroup.card_map_of_injective B.subtype_injective, ← horb,
      ← MulAction.index_stabilizer B F, mul_comm]
    exact Subgroup.card_mul_index _

theorem inv_mul_mem_normalizer_of_image_eq {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (B : Subgroup (Perm Ω)) (y : Perm Ω) (𝓕 : Set (Set Ω))
    (hcov : ∀ S ∈ 𝓕, ∃ g ∈ B, S = g '' {i | y i = i})
    (hmem : ∀ g ∈ B, g '' {i | y i = i} ∈ 𝓕)
    (hcard : 𝓕.ncard * Nat.card ↥(B ⊓ normalizer (zpowers y : Set (Perm Ω))) = Nat.card B)
    {g g' : Perm Ω} (hg : g ∈ B) (hg' : g' ∈ B)
    (he : g '' {i | y i = i} = g' '' {i | y i = i}) :
    g⁻¹ * g' ∈ normalizer (zpowers y : Set (Perm Ω)) := by
  classical
  have hA : ∀ n ∈ normalizer (zpowers y : Set (Perm Ω)), ∀ i, y i = i → y (n i) = n i := by
    intro n hn i hi
    have h1 : n⁻¹ * y * n ∈ zpowers y := by
      refine (mem_normalizer_iff.mp hn (n⁻¹ * y * n)).mpr ?_
      rw [show n * (n⁻¹ * y * n) * n⁻¹ = y by group]
      exact mem_zpowers y
    obtain ⟨k, hk⟩ := h1
    have h2 : (y ^ k) i = i := Perm.zpow_apply_eq_self_of_apply_eq_self hi k
    rw [show y ^ k = n⁻¹ * y * n from hk] at h2
    have h3 : n⁻¹ (y (n i)) = i := by simpa [Perm.mul_apply] using h2
    calc y (n i) = n (n⁻¹ (y (n i))) := by simp
      _ = n i := by rw [h3]
  have hB : ∀ n ∈ normalizer (zpowers y : Set (Perm Ω)), n '' {i | y i = i} = {i | y i = i} := by
    intro n hn
    ext j
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact hA n hn i hi
    · intro hj
      exact ⟨n⁻¹ j, hA n⁻¹ (inv_mem hn) j hj, by simp⟩
  obtain ⟨K, hK, hKcard⟩ := exists_subgroup_ncard_mul_card_eq B {i | y i = i} 𝓕 hcov hmem
  have hne : 𝓕.ncard ≠ 0 := by
    have h1 : ({i | y i = i} : Set Ω) ∈ 𝓕 := by simpa using hmem 1 B.one_mem
    exact ((Set.ncard_pos (Set.toFinite 𝓕)).2 ⟨_, h1⟩).ne'
  have hle : B ⊓ normalizer (zpowers y : Set (Perm Ω)) ≤ K := by
    intro n hn
    exact (hK n).2 ⟨hn.1, hB n hn.2⟩
  have hcardeq : Nat.card K = Nat.card ↥(B ⊓ normalizer (zpowers y : Set (Perm Ω))) :=
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (hKcard.trans hcard.symm)
  have hKeq : B ⊓ normalizer (zpowers y : Set (Perm Ω)) = K :=
    Subgroup.eq_of_le_of_card_ge hle hcardeq.le
  have hmemK : g⁻¹ * g' ∈ K := by
    refine (hK _).2 ⟨B.mul_mem (B.inv_mem hg) hg', ?_⟩
    rw [Perm.coe_mul, Set.image_comp, ← he, ← Set.image_comp, ← Perm.coe_mul, inv_mul_cancel,
      Perm.coe_one, Set.image_id]
  rw [← hKeq] at hmemK
  exact hmemK.2

end CFSG.Sporadic.Recognition.LyonsSims
