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

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup

variable {G : Type} [Group G]

@[expose] def conjOn {M : Subgroup G} (k : G) (hk : k ∈ normalizer (M : Set G)) : ↥M →* ↥M where
  toFun m := ⟨k * m * k⁻¹, (Subgroup.mem_normalizer_iff.1 hk m).1 m.2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply Subtype.ext
    simp [mul_assoc]

theorem commutes_of_cocycle [Finite G] {K P' M : Subgroup G} (hPK : P' ≤ K)
    (hKM : K ≤ normalizer (M : Set G)) (hM : ∀ a ∈ M, ∀ b ∈ M, a * b = b * a)
    (hM2 : ∀ a ∈ M, a * a = 1) (hodd : ¬ 2 ∣ P'.relIndex K) {z : G}
    (hc : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ M) (hP : ∀ p ∈ P', p * z = z * p)
    (hfix : ∀ m ∈ M, (∀ p ∈ P', p * m * p⁻¹ = m) → ∀ k ∈ K, k * m * k⁻¹ = m) :
    ∀ k ∈ K, k * z = z * k := by
  classical
  let _ : CommGroup ↥M := { (inferInstance : Group ↥M) with
    mul_comm := fun a b => Subtype.ext (hM _ a.2 _ b.2) }
  set H : Subgroup ↥K := P'.subgroupOf K with hH
  have : Fintype (↥K ⧸ H) := Fintype.ofFinite _
  let c : ↥K → ↥M := fun k => ⟨(k : G) * z * (k : G)⁻¹ * z⁻¹, hc k k.2⟩
  have hcval : ∀ k : ↥K, ((c k : ↥M) : G) = (k : G) * z * (k : G)⁻¹ * z⁻¹ := fun _ => rfl
  let κ : ↥K → ↥M →* ↥M := fun k => conjOn (k : G) (hKM k.2)
  have hcmul : ∀ k₁ k₂ : ↥K, c (k₁ * k₂) = κ k₁ (c k₂) * c k₁ := by
    intro k₁ k₂
    apply Subtype.ext
    show ((k₁ * k₂ : ↥K) : G) * z * ((k₁ * k₂ : ↥K) : G)⁻¹ * z⁻¹ =
      (k₁ : G) * ((k₂ : G) * z * (k₂ : G)⁻¹ * z⁻¹) * (k₁ : G)⁻¹ * ((k₁ : G) * z * (k₁ : G)⁻¹ * z⁻¹)
    simp only [Subgroup.coe_mul, mul_inv_rev]
    group
  have hc2 : ∀ k : ↥K, c k * c k = 1 := fun k => Subtype.ext (hM2 _ (c k).2)
  have hcH : ∀ p : ↥K, p ∈ H → c p = 1 := by
    intro p hp
    have hp' : (p : G) ∈ P' := Subgroup.mem_subgroupOf.1 hp
    apply Subtype.ext
    show (p : G) * z * (p : G)⁻¹ * z⁻¹ = 1
    rw [hP _ hp']
    group
  let out : ↥K ⧸ H → ↥K := Quotient.out
  have hout : ∀ t : ↥K ⧸ H, (QuotientGroup.mk (out t) : ↥K ⧸ H) = t := fun t => Quotient.out_eq' t
  have hcos : ∀ (k : ↥K) (t : ↥K ⧸ H), ∃ p ∈ H, k * out t = out (k • t) * p := by
    intro k t
    have h1 : (QuotientGroup.mk (k * out t) : ↥K ⧸ H) = QuotientGroup.mk (out (k • t)) := by
      rw [hout (k • t)]
      calc (QuotientGroup.mk (k * out t) : ↥K ⧸ H) = k • (QuotientGroup.mk (out t) : ↥K ⧸ H) :=
          rfl
        _ = k • t := by rw [hout t]
    have h2 := H.inv_mem (QuotientGroup.eq.1 h1)
    refine ⟨((k * out t)⁻¹ * out (k • t))⁻¹, h2, ?_⟩
    group
  have hE1 : ∀ (k : ↥K) (t : ↥K ⧸ H), c (out (k • t)) = κ k (c (out t)) * c k := by
    intro k t
    obtain ⟨p, hp, hpeq⟩ := hcos k t
    have h1 := hcmul k (out t)
    rw [hpeq, hcmul, hcH p hp] at h1
    simpa using h1
  set m : ↥M := ∏ t : ↥K ⧸ H, c (out t) with hm
  have hmk : ∀ k : ↥K, m = κ k m * c k := by
    intro k
    have hperm : ∏ t : ↥K ⧸ H, c (out (k • t)) = m := by
      rw [hm]
      exact Fintype.prod_equiv (MulAction.toPerm k) _ _ (fun t => rfl)
    have hprod : ∏ t : ↥K ⧸ H, c (out (k • t)) = κ k m * c k ^ Fintype.card (↥K ⧸ H) := by
      simp_rw [hE1]
      rw [Finset.prod_mul_distrib, map_prod, Finset.prod_const, Finset.card_univ]
    have hcard : c k ^ Fintype.card (↥K ⧸ H) = c k := by
      have hodd' : ¬ 2 ∣ Fintype.card (↥K ⧸ H) := by
        rw [← Nat.card_eq_fintype_card]
        exact fun h2 => hodd (by
          rw [← Subgroup.index_eq_card] at h2
          exact h2)
      obtain ⟨n, hn⟩ : ∃ n, Fintype.card (↥K ⧸ H) = 2 * n + 1 := by
        rcases Nat.even_or_odd (Fintype.card (↥K ⧸ H)) with ⟨n, hn⟩ | ⟨n, hn⟩
        · exact absurd ⟨n, by omega⟩ hodd'
        · exact ⟨n, hn⟩
      rw [hn, pow_succ, pow_mul, sq, hc2 k, one_pow, one_mul]
    rw [hcard] at hprod
    exact hperm.symm.trans hprod
  have hmfix : ∀ p ∈ P', (p : G) * m * (p : G)⁻¹ = m := by
    intro p hp
    have hpK : p ∈ K := hPK hp
    have h1 := hmk ⟨p, hpK⟩
    have h2 : c ⟨p, hpK⟩ = 1 := hcH _ (Subgroup.mem_subgroupOf.2 hp)
    rw [h2, mul_one] at h1
    have := congrArg Subtype.val h1
    exact this.symm
  intro k hk
  have hmk' := hfix m m.2 hmfix k hk
  have h1 := hmk ⟨k, hk⟩
  have h2 : κ ⟨k, hk⟩ m = m := Subtype.ext hmk'
  rw [h2] at h1
  have h3 : c ⟨k, hk⟩ = 1 := mul_left_cancel (a := m) (h1.symm.trans (mul_one m).symm)
  have h4 := congrArg Subtype.val h3
  have h5 : k * z * k⁻¹ * z⁻¹ = 1 := h4
  calc k * z = (k * z * k⁻¹ * z⁻¹) * (z * k) := by group
    _ = z * k := by rw [h5, one_mul]

end CFSG.Quasithin.H13.U3.GC137
