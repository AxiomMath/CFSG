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

namespace CFSG.Quasithin.H13.L319.S66

theorem mem_of_simple_normal_blocks {Γ : Type} [Group Γ] (𝓚 : Finset (Subgroup Γ))
    (hcomm : ∀ K ∈ 𝓚, ∀ K' ∈ 𝓚, K ≠ K' → ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKs : ∀ K ∈ 𝓚, IsSimpleGroup ↥K)
    (S : Subgroup Γ) (hSY : S ≤ ⨆ K ∈ 𝓚, K)
    (hSn : ∀ g ∈ (⨆ K ∈ 𝓚, K), ∀ s ∈ S, g * s * g⁻¹ ∈ S)
    (hSs : IsSimpleGroup ↥S) (hSna : ¬ IsMulCommutative ↥S) :
    S ∈ 𝓚 := by
  have hKY : ∀ K ∈ 𝓚, K ≤ ⨆ K ∈ 𝓚, K := fun K hK => le_iSup₂ (f := fun K (_ : K ∈ 𝓚) => K) K hK
  have hnorm : ∀ K ∈ 𝓚, ∀ g ∈ (⨆ K ∈ 𝓚, K), ∀ n ∈ K, g * n * g⁻¹ ∈ K := by
    intro K hK
    have hle : (⨆ K' ∈ 𝓚, K') ≤ Subgroup.normalizer (K : Set Γ) := by
      refine iSup₂_le fun K' hK' => ?_
      by_cases hKK : K' = K
      · subst hKK
        exact Subgroup.le_normalizer
      · have hfwd : ∀ a ∈ K', ∀ x ∈ K, a * x * a⁻¹ ∈ K := by
          intro a ha x hx
          have e : a * x * a⁻¹ = x := by
            rw [hcomm K' hK' K hK hKK a ha x hx, mul_inv_cancel_right]
          rw [e]
          exact hx
        intro a ha
        rw [Subgroup.mem_normalizer_iff]
        intro x
        constructor
        · intro hx
          exact hfwd a ha x hx
        · intro hx
          have h1 := hfwd a⁻¹ (K'.inv_mem ha) _ hx
          have e : a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x := by group
          rwa [e] at h1
    intro g hg n hn
    exact (Subgroup.mem_normalizer_iff.mp (hle hg) n).mp hn
  by_cases hcen : ∃ K ∈ 𝓚, ∃ s ∈ S, ∃ k ∈ K, s * k ≠ k * s
  swap
  ·
    exfalso
    push_neg at hcen
    have hcenY : ∀ s ∈ S, ∀ g ∈ (⨆ K ∈ 𝓚, K), s * g = g * s := by
      intro s hs
      have hle : (⨆ K ∈ 𝓚, K) ≤ Subgroup.centralizer ({s} : Set Γ) := by
        refine iSup₂_le fun K hK => ?_
        intro k hk
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.mp hh]
        exact hcen K hK s hs k hk
      intro g hg
      exact Subgroup.mem_centralizer_iff.mp (hle hg) s (Set.mem_singleton s)
    refine hSna (isMulCommutative_iff.mpr fun a b => ?_)
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact hcenY a.1 a.2 b.1 (hSY b.2)
  obtain ⟨K, hK, s, hs, k, hk, hne⟩ := hcen
  have hsY : s ∈ (⨆ K ∈ 𝓚, K) := hSY hs
  have hkY : k ∈ (⨆ K ∈ 𝓚, K) := hKY K hK hk
  have hcK : s * k * s⁻¹ * k⁻¹ ∈ K :=
    K.mul_mem (hnorm K hK s hsY k hk) (K.inv_mem hk)
  have hcS : s * k * s⁻¹ * k⁻¹ ∈ S := by
    have h1 : k * s⁻¹ * k⁻¹ ∈ S := hSn k hkY s⁻¹ (S.inv_mem hs)
    have h2 := S.mul_mem hs h1
    have e : s * (k * s⁻¹ * k⁻¹) = s * k * s⁻¹ * k⁻¹ := by simp only [mul_assoc]
    rwa [e] at h2
  have hne1 : s * k * s⁻¹ * k⁻¹ ≠ 1 := by
    intro h
    apply hne
    have h2 : s * k * s⁻¹ = k := mul_inv_eq_one.mp h
    calc s * k = s * k * s⁻¹ * s := by rw [inv_mul_cancel_right]
      _ = k * s := by rw [h2]
  haveI := hKs K hK
  have hKS : K ≤ S := by
    have hN : ((S ⊓ K).subgroupOf K).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnS, hnK⟩ := Subgroup.mem_inf.mp hn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.mpr
        ⟨hSn g.1 (hKY K hK g.2) n.1 hnS, K.mul_mem (K.mul_mem g.2 hnK) (K.inv_mem g.2)⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top ((S ⊓ K).subgroupOf K) with hbot | htop
    · exfalso
      have hmem : (⟨s * k * s⁻¹ * k⁻¹, hcK⟩ : ↥K) ∈ (S ⊓ K).subgroupOf K :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hcS, hcK⟩)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hne1 (congrArg Subtype.val hmem)
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥K) ∈ (S ⊓ K).subgroupOf K := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).1
  have hSK : S ≤ K := by
    have hM : ((S ⊓ K).subgroupOf S).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      obtain ⟨hnS, hnK⟩ := Subgroup.mem_inf.mp hn
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mem_inf.mpr
        ⟨S.mul_mem (S.mul_mem g.2 hnS) (S.inv_mem g.2), hnorm K hK g.1 (hSY g.2) n.1 hnK⟩
    rcases Subgroup.Normal.eq_bot_or_eq_top ((S ⊓ K).subgroupOf S) with hbot | htop
    · exfalso
      have hmem : (⟨s * k * s⁻¹ * k⁻¹, hcS⟩ : ↥S) ∈ (S ⊓ K).subgroupOf S :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hcS, hcK⟩)
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hne1 (congrArg Subtype.val hmem)
    · intro x hx
      have hmem : (⟨x, hx⟩ : ↥S) ∈ (S ⊓ K).subgroupOf S := by
        rw [htop]
        exact Subgroup.mem_top _
      exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hmem)).2
  rw [le_antisymm hSK hKS]
  exact hK

end CFSG.Quasithin.H13.L319.S66

end
