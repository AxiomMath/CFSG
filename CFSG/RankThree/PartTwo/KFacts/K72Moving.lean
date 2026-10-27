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
public import Mathlib.GroupTheory.Nilpotent
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

namespace CFSG.RankThree.PartTwo.KFacts

variable {G : Type*} [Group G] [Finite G]

open scoped Pointwise

theorem exists_sylow_le_normalizer {p : ℕ} [Fact p.Prime] {A L : Subgroup G}
    (hA : IsPGroup p A) (hAN : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ Q : Sylow p L,
      A ≤ Subgroup.normalizer (((Q : Subgroup L).map L.subtype : Subgroup G) : Set G) := by
  let φ : A →* MulAut L := L.normalizerMonoidHom.comp (Subgroup.inclusion hAN)
  let _ : MulDistribMulAction A L := MulDistribMulAction.compHom L φ
  have hcard : ¬ p ∣ Nat.card (Sylow p L) := by
    intro h
    have h1 := card_sylow_modEq_one p L
    have h2 : Nat.card (Sylow p L) ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.mpr h
    have h3 : 1 ≡ 0 [MOD p] := h1.symm.trans h2
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.eq_one_of_dvd_one ((Nat.modEq_zero_iff_dvd.mp h3)))
  obtain ⟨Q, hQ⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p L) hcard
  have key : ∀ g ∈ A, ∀ z ∈ (Q : Subgroup L).map L.subtype, g * z * g⁻¹ ∈
      (Q : Subgroup L).map L.subtype := by
    intro g hg z hz
    obtain ⟨z', hz', rfl⟩ := hz
    have h1 : (⟨g, hg⟩ : A) • Q = Q := hQ ⟨g, hg⟩
    have h2 : (⟨g, hg⟩ : A) • (Q : Subgroup L) = Q := by
      rw [← Sylow.pointwise_smul_def, h1]
    have h3 : (⟨g, hg⟩ : A) • z' ∈ (Q : Subgroup L) := by
      rw [← h2]
      exact Subgroup.smul_mem_pointwise_smul z' _ _ hz'
    exact ⟨_, h3, rfl⟩
  refine ⟨Q, fun g hg => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key g hg y
  · intro hy
    have h1 := key g⁻¹ (A.inv_mem hg) _ hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at h1

theorem exists_moving_of_not_centralizes_sylow {p : ℕ} [Fact p.Prime] {A L : Subgroup G}
    {a : G} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1)
    (hΩ : ∀ x : G, x ^ p = 1 → (∀ y ∈ A, y * x = x * y) → x ∈ A)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (haA : a ∈ A)
    (hab : ∀ Q : Sylow p L, ∀ x ∈ (Q : Subgroup L), ∀ y ∈ (Q : Subgroup L), x * y = y * x)
    (hQ : ∀ Q : Sylow p L, ¬ ∀ y ∈ (Q : Subgroup L), a * (y : G) = y * a) :
    ∃ l ∈ L ⊓ Subgroup.normalizer (A : Set G), (∃ k : ℕ, l ^ p ^ k = 1) ∧
      ∃ x ∈ A, l * x * l⁻¹ ≠ x := by
  have hA : IsPGroup p A := fun x => ⟨1, Subtype.ext (by simpa using hAp x x.2)⟩
  obtain ⟨Q, hQN⟩ := exists_sylow_le_normalizer hA hAN
  set Q' := (Q : Subgroup L).map L.subtype with hQ'
  have hQ'L : Q' ≤ L := Subgroup.map_subtype_le _
  have hQ'p : IsPGroup p Q' := Q.isPGroup'.map L.subtype
  by_contra hno
  push Not at hno
  have hcen : ∀ q ∈ Q', q ∈ Subgroup.normalizer (A : Set G) → ∀ x ∈ A, q * x = x * q := by
    intro q hq hqN x hx
    obtain ⟨k, hk⟩ := hQ'p ⟨q, hq⟩
    have hk' : q ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 := hno q ⟨hQ'L hq, hqN⟩ ⟨k, hk'⟩ x hx
    calc q * x = q * x * q⁻¹ * q := by group
      _ = x * q := by rw [h1]
  set X := Q' ⊔ A with hX
  have hXp : IsPGroup p X := hQ'p.to_sup_of_normal_left' hA hQN
  have hXmul : (X : Set G) = (Q' : Set G) * (A : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left Q' A hQN
  set B := X ⊓ Subgroup.centralizer (A : Set G) with hB
  have hAB : A ≤ B := fun x hx => ⟨Subgroup.mem_sup_right hx,
    Subgroup.mem_centralizer_iff.mpr fun y hy => hAc y hy x hx⟩
  have hNA : ∀ x ∈ X, x ∈ Subgroup.normalizer (A : Set G) → x ∈ B := by
    intro x hxX hxN
    have hx' : x ∈ (Q' : Set G) * (A : Set G) := by rw [← hXmul]; exact hxX
    obtain ⟨q, hq, a', ha', rfl⟩ := hx'
    have hqN : q ∈ Subgroup.normalizer (A : Set G) := by
      have e : q = q * a' * a'⁻¹ := by group
      rw [e]
      exact Subgroup.mul_mem _ hxN (Subgroup.le_normalizer (A.inv_mem ha'))
    refine ⟨hxX, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have h1 := hcen q hq hqN y hy
    calc y * (q * a') = (y * q) * a' := by group
      _ = (q * y) * a' := by rw [h1]
      _ = q * (y * a') := by group
      _ = q * (a' * y) := by rw [hAc y hy a' ha']
      _ = q * a' * y := by group
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ (Q' : Set G) * (A : Set G) := by rw [← hXmul]; exact hx.1
    have hy' : y ∈ (Q' : Set G) * (A : Set G) := by rw [← hXmul]; exact hy.1
    obtain ⟨q₁, hq₁, a₁, ha₁, rfl⟩ := hx'
    obtain ⟨q₂, hq₂, a₂, ha₂, rfl⟩ := hy'
    have hq₁c : ∀ z ∈ A, q₁ * z = z * q₁ := fun z hz => by
      have h1 := Subgroup.mem_centralizer_iff.mp hx.2 z hz
      have h2 := hAc z hz a₁ ha₁
      have h3 : z * q₁ * a₁ = q₁ * z * a₁ := by
        calc z * q₁ * a₁ = z * (q₁ * a₁) := by group
          _ = q₁ * a₁ * z := h1
          _ = q₁ * (a₁ * z) := by group
          _ = q₁ * (z * a₁) := by rw [h2]
          _ = q₁ * z * a₁ := by group
      exact (mul_right_cancel h3).symm
    have hq₂c : ∀ z ∈ A, q₂ * z = z * q₂ := fun z hz => by
      have h1 := Subgroup.mem_centralizer_iff.mp hy.2 z hz
      have h2 := hAc z hz a₂ ha₂
      have h3 : z * q₂ * a₂ = q₂ * z * a₂ := by
        calc z * q₂ * a₂ = z * (q₂ * a₂) := by group
          _ = q₂ * a₂ * z := h1
          _ = q₂ * (a₂ * z) := by group
          _ = q₂ * (z * a₂) := by rw [h2]
          _ = q₂ * z * a₂ := by group
      exact (mul_right_cancel h3).symm
    obtain ⟨q₁', hq₁', rfl⟩ := hq₁
    obtain ⟨q₂', hq₂', rfl⟩ := hq₂
    have hq : (q₁' : G) * q₂' = q₂' * q₁' := congrArg Subtype.val (hab Q q₁' hq₁' q₂' hq₂')
    have hq₁c' : ∀ z ∈ A, (q₁' : G) * z = z * q₁' := hq₁c
    have hq₂c' : ∀ z ∈ A, (q₂' : G) * z = z * q₂' := hq₂c
    calc (q₁' : G) * a₁ * (q₂' * a₂) = q₁' * (a₁ * q₂') * a₂ := by group
      _ = q₁' * (q₂' * a₁) * a₂ := by rw [← hq₂c' a₁ ha₁]
      _ = (q₁' * q₂') * (a₁ * a₂) := by group
      _ = (q₂' * q₁') * (a₂ * a₁) := by rw [hq, hAc a₁ ha₁ a₂ ha₂]
      _ = q₂' * (q₁' * a₂) * a₁ := by group
      _ = q₂' * (a₂ * q₁') * a₁ := by rw [hq₁c' a₂ ha₂]
      _ = q₂' * a₂ * (q₁' * a₁) := by group
  have hBX : B = X := by
    by_contra hne
    have hBlt : B.subgroupOf X < ⊤ := by
      refine lt_of_le_of_ne le_top fun h => hne ?_
      apply le_antisymm inf_le_left
      intro x hx
      have : (⟨x, hx⟩ : X) ∈ B.subgroupOf X := by rw [h]; exact Subgroup.mem_top _
      exact this
    have : Group.IsNilpotent X := hXp.isNilpotent
    obtain ⟨⟨g, hgX⟩, hgN, hgB⟩ := IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (B.subgroupOf X) hBlt)
    apply hgB
    rw [Subgroup.mem_subgroupOf]
    apply hNA g hgX
    rw [Subgroup.mem_normalizer_iff]
    have hgB' : ∀ z ∈ B, g * z * g⁻¹ ∈ B := by
      intro z hz
      have hzX : z ∈ X := hz.1
      have h1 := (Subgroup.mem_normalizer_iff.mp hgN ⟨z, hzX⟩).mp
        (Subgroup.mem_subgroupOf.mpr hz)
      rw [Subgroup.mem_subgroupOf] at h1
      simpa using h1
    have hgB'' : ∀ z ∈ B, g⁻¹ * z * g ∈ B := by
      intro z hz
      have hzX : z ∈ X := hz.1
      have h1 := (Subgroup.mem_normalizer_iff.mp hgN ⟨g⁻¹ * z * g, X.mul_mem
        (X.mul_mem (X.inv_mem hgX) hzX) hgX⟩).mpr (by
          rw [Subgroup.mem_subgroupOf]
          have e : (⟨g, hgX⟩ : X) * ⟨g⁻¹ * z * g, X.mul_mem (X.mul_mem (X.inv_mem hgX) hzX) hgX⟩ *
              (⟨g, hgX⟩ : X)⁻¹ = ⟨z, hzX⟩ := Subtype.ext (by simp; group)
          rw [e]
          exact hz)
      rw [Subgroup.mem_subgroupOf] at h1
      exact h1
    have hΩB : ∀ z ∈ B, z ^ p = 1 → z ∈ A := fun z hz hzp =>
      hΩ z hzp fun y hy => (Subgroup.mem_centralizer_iff.mp hz.2 y hy)
    intro y
    constructor
    · intro hy
      have h1 := hgB' y (hAB hy)
      refine hΩB _ h1 ?_
      rw [conj_pow, hAp y hy, mul_one, mul_inv_cancel]
    · intro hy
      have h1 := hgB'' _ (hAB hy)
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e] at h1
      refine hΩB _ h1 ?_
      have h2 := hAp _ hy
      rw [conj_pow] at h2
      calc y ^ p = g⁻¹ * (g * y ^ p * g⁻¹) * g := by group
        _ = 1 := by rw [h2]; group
  apply hQ Q
  intro y hy
  have hyX : (y : G) ∈ X := Subgroup.mem_sup_left ⟨y, hy, rfl⟩
  rw [← hBX] at hyX
  exact Subgroup.mem_centralizer_iff.mp hyX.2 a haA

end CFSG.RankThree.PartTwo.KFacts
