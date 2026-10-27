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
public import Mathlib.Order.CompletePartialOrder
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

open scoped Pointwise

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem inf_eq_bot_of_coprime {p : ℕ} [Fact p.Prime] {A T : Subgroup G} (hA : IsPGroup p A)
    (hT : ¬ p ∣ Nat.card T) : A ⊓ T = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  obtain ⟨k, hk⟩ := hA ⟨y, hy.1⟩
  have hk' : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : orderOf y ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf y ∣ Nat.card T := Subgroup.orderOf_dvd_natCard T hy.2
  have hcop : Nat.Coprime (p ^ k) (Nat.card T) :=
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hT)
  have h3 : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  exact orderOf_eq_one_iff.mp h3

theorem exists_mul_mem_normalizer {p : ℕ} [Fact p.Prime] {A T : Subgroup G} (hA : IsPGroup p A)
    (hT : ¬ p ∣ Nat.card T) (hAT : A ≤ Subgroup.normalizer (T : Set G)) {x : G}
    (hxA : ∀ y ∈ A, x * y * x⁻¹ ∈ A ⊔ T) :
    ∃ t ∈ T, t * x ∈ Subgroup.normalizer (A : Set G) ∧
      ∀ y ∈ A, (t * x) * y * (t * x)⁻¹ * (x * y * x⁻¹)⁻¹ ∈ T := by
  set K := A ⊔ T with hK
  have hKmul : (K : Set G) = (A : Set G) * (T : Set G) :=
    Subgroup.coe_mul_of_left_le_normalizer_right A T hAT
  have hdisj := inf_eq_bot_of_coprime hA hT
  set A' := A.map (MulAut.conj x).toMonoidHom with hA'
  have hA'K : A' ≤ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact hxA y hy
  have hAK : A ≤ K := le_sup_left
  have hA'card : Nat.card A' = Nat.card A :=
    Subgroup.card_map_of_injective (MulAut.conj x).injective
  have hKcard : Nat.card K = Nat.card A * Nat.card T := by
    have hinj : Function.Injective (fun p : A × T => (⟨(p.1 : G) * p.2,
        by rw [← SetLike.mem_coe, hKmul]; exact Set.mul_mem_mul p.1.2 p.2.2⟩ : K)) := by
      rintro ⟨a₁, t₁⟩ ⟨a₂, t₂⟩ h
      have h' : (a₁ : G) * t₁ = a₂ * t₂ := congrArg Subtype.val h
      have hmem : (a₂ : G)⁻¹ * a₁ ∈ A ⊓ T := by
        refine ⟨A.mul_mem (A.inv_mem a₂.2) a₁.2, ?_⟩
        have : (a₂ : G)⁻¹ * a₁ = t₂ * (t₁ : G)⁻¹ := by
          calc (a₂ : G)⁻¹ * a₁ = (a₂ : G)⁻¹ * (a₁ * t₁) * (t₁ : G)⁻¹ := by group
            _ = t₂ * (t₁ : G)⁻¹ := by rw [h']; group
        rw [this]
        exact T.mul_mem t₂.2 (T.inv_mem t₁.2)
      rw [hdisj, Subgroup.mem_bot] at hmem
      have ha : (a₁ : G) = a₂ := by
        calc (a₁ : G) = a₂ * ((a₂ : G)⁻¹ * a₁) := by group
          _ = a₂ := by rw [hmem, mul_one]
      have ht : (t₁ : G) = t₂ := by
        rw [ha] at h'
        exact mul_left_cancel h'
      exact Prod.ext (Subtype.ext ha) (Subtype.ext ht)
    have hsurj : Function.Surjective (fun p : A × T => (⟨(p.1 : G) * p.2,
        by rw [← SetLike.mem_coe, hKmul]; exact Set.mul_mem_mul p.1.2 p.2.2⟩ : K)) := by
      rintro ⟨k, hk⟩
      rw [← SetLike.mem_coe, hKmul] at hk
      obtain ⟨a, ha, t, ht, rfl⟩ := hk
      exact ⟨(⟨a, ha⟩, ⟨t, ht⟩), rfl⟩
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)).symm
  have hindex : ∀ B : Subgroup G, B ≤ K → Nat.card B = Nat.card A →
      ¬ p ∣ (B.subgroupOf K).index := by
    intro B hBK hB
    have h1 := (B.subgroupOf K).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hB, hKcard] at h1
    have hA0 : 0 < Nat.card A := Nat.card_pos
    have h2 : (B.subgroupOf K).index = Nat.card T := Nat.eq_of_mul_eq_mul_left hA0 h1
    rw [h2]
    exact hT
  have hpA : IsPGroup p (A.subgroupOf K) :=
    hA.of_equiv (Subgroup.subgroupOfEquivOfLe hAK).symm
  have hpA' : IsPGroup p (A'.subgroupOf K) :=
    (hA.map (MulAut.conj x).toMonoidHom).of_equiv (Subgroup.subgroupOfEquivOfLe hA'K).symm
  set S₁ := hpA.toSylow (hindex A hAK rfl)
  set S₂ := hpA'.toSylow (hindex A' hA'K hA'card)
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K S₂ S₁
  have hkA : ∀ z ∈ A, (k : G) * x * z * ((k : G) * x)⁻¹ ∈ A := by
    intro z hz
    have hz' : (⟨x * z * x⁻¹, hA'K ⟨z, hz, rfl⟩⟩ : K) ∈ (S₂ : Subgroup K) := ⟨z, hz, rfl⟩
    have h1 : (MulAut.conj k) • (⟨x * z * x⁻¹, hA'K ⟨z, hz, rfl⟩⟩ : K) ∈
        (MulAut.conj k • (S₂ : Subgroup K)) := Subgroup.smul_mem_pointwise_smul _ _ _ hz'
    rw [← Sylow.coe_subgroup_smul, hk] at h1
    have h2 : (((MulAut.conj k) • (⟨x * z * x⁻¹, hA'K ⟨z, hz, rfl⟩⟩ : K) : K) : G) ∈ A := h1
    have e : (((MulAut.conj k) • (⟨x * z * x⁻¹, hA'K ⟨z, hz, rfl⟩⟩ : K) : K) : G) =
        (k : G) * x * z * ((k : G) * x)⁻¹ := by
      show (k : G) * (x * z * x⁻¹) * (k : G)⁻¹ = _
      group
    rwa [e] at h2
  have hkA' : ∀ y ∈ A, ((k : G) * x)⁻¹ * y * ((k : G) * x) ∈ A := by
    intro y hy
    have hy' : (⟨y, hAK hy⟩ : K) ∈ (MulAut.conj k • (S₂ : Subgroup K)) := by
      rw [← Sylow.coe_subgroup_smul, hk]
      exact hy
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hy'
    obtain ⟨z, hz, hzw⟩ := hy'
    have e1 : x * z * x⁻¹ = (k : G)⁻¹ * y * k := by
      rw [← map_inv] at hzw
      have e0 : x * z * x⁻¹ = (k : G)⁻¹ * y * ((k : G)⁻¹)⁻¹ := hzw
      rwa [inv_inv] at e0
    have e2 : ((k : G) * x)⁻¹ * y * ((k : G) * x) = z := by
      calc ((k : G) * x)⁻¹ * y * ((k : G) * x) = x⁻¹ * ((k : G)⁻¹ * y * k) * x := by group
        _ = z := by rw [← e1]; group
    rw [e2]
    exact hz
  have hkxN : (k : G) * x ∈ Subgroup.normalizer (A : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact hkA y hy
    · intro hy
      have := hkA' _ hy
      have e : ((k : G) * x)⁻¹ * ((k : G) * x * y * ((k : G) * x)⁻¹) * ((k : G) * x) = y := by
        group
      rwa [e] at this
  have hkmem : (k : G) ∈ ((A : Set G) * (T : Set G)) := by rw [← hKmul]; exact k.2
  obtain ⟨a, ha, t, ht, hat⟩ := hkmem
  refine ⟨t, ht, ?_, fun y hy => ?_⟩
  · have e : t * x = a⁻¹ * ((k : G) * x) := by rw [← hat]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer (A.inv_mem ha)) hkxN
  ·
    have hKN : K ≤ Subgroup.normalizer (T : Set G) := sup_le hAT (Subgroup.le_normalizer)
    have hm := (Subgroup.mem_normalizer_iff.mp (hKN (hxA y hy)) t⁻¹).mp (T.inv_mem ht)
    have e : (t * x) * y * (t * x)⁻¹ * (x * y * x⁻¹)⁻¹ =
        t * ((x * y * x⁻¹) * t⁻¹ * (x * y * x⁻¹)⁻¹) := by group
    rw [e]
    exact T.mul_mem ht hm

end CFSG.RankThree.PartTwo.KFacts
