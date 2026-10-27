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
public import Mathlib.GroupTheory.IndexNormal
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

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

variable {Γ : Type*} [Group Γ]

theorem commutator_mem_of_card_eq_nine {P S : Subgroup Γ} (hSP : S ≤ P) (hP : Nat.card P = 27)
    (hS : Nat.card S = 9) {x y : Γ} (hx : x ∈ P) (hy : y ∈ P) :
    x * y * x⁻¹ * y⁻¹ ∈ S := by
  classical
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; norm_num)
  set S' : Subgroup P := S.subgroupOf P with hS'
  have hS'card : Nat.card S' = 9 := by
    rw [← hS]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv
  have hidx : S'.index = 3 := by
    have h := Subgroup.card_mul_index S'
    rw [hS'card, hP] at h
    omega
  have hmin : (Nat.card P).minFac = 3 := by rw [hP]; norm_num
  have : S'.Normal := Subgroup.normal_of_index_eq_minFac_card (by rw [hidx, hmin])
  have hQcard : Nat.card (P ⧸ S') = 3 := by rw [← Subgroup.index_eq_card]; exact hidx
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic (P ⧸ S') := isCyclic_of_prime_card hQcard
  let xP : P := ⟨x, hx⟩
  let yP : P := ⟨y, hy⟩
  have hcomm : (QuotientGroup.mk xP : P ⧸ S') * QuotientGroup.mk yP =
      QuotientGroup.mk yP * QuotientGroup.mk xP :=
    (IsCyclic.commGroup (α := P ⧸ S')).mul_comm _ _
  have hmem : xP * yP * xP⁻¹ * yP⁻¹ ∈ S' := by
    rw [← QuotientGroup.eq_one_iff]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [hcomm]
    group
  exact Subgroup.mem_subgroupOf.1 hmem

theorem eq_one_or_eq_or_eq_inv_of_mem_zpowers {a b : Γ} (ha3 : a ^ 3 = 1)
    (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a ∨ b = a⁻¹ := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h3 : a ^ (3 : ℤ) = 1 := by rw [zpow_ofNat]; exact ha3
  rw [zpow_eq_zpow_emod k h3]
  have hk : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hk with h | h | h
  · left; rw [h]; simp
  · right; left; rw [h]; simp
  · right; right
    rw [h, zpow_two]
    exact eq_inv_of_mul_eq_one_left (show a * a * a = 1 by rw [mul_assoc, ← pow_three]; exact ha3)

theorem card_le_fourteen_of_not_mem (B P : Subgroup Γ) [Finite B] (hPB : P ≤ B)
    (hnorm : ∀ x ∈ B, ∀ p ∈ P, x * p * x⁻¹ ∈ P) (hP : Nat.card P = 27) (hB : Nat.card B = 216)
    (hexp : ∀ p ∈ P, p ^ 3 = 1) {z : Γ} (hz : ∃ x ∈ P, ∃ y ∈ P, z = x * y * x⁻¹ * y⁻¹)
    (hN : ∀ a ∈ P, a ≠ 1 → a ≠ z → a⁻¹ ≠ z → ∃ N : Finset Γ, N.card ≤ 11 ∧
      ∀ x ∈ B, x ∉ P → (x * a * x⁻¹ = a ∨ x * a * x⁻¹ = a⁻¹) → x ∈ N)
    (K : Subgroup Γ) (hKB : K ≤ B) (hzK : z ∉ K) : Nat.card K ≤ 14 := by
  classical
  obtain ⟨x0, hx0, y0, hy0, hzxy⟩ := hz
  have hzP : z ∈ P := by
    rw [hzxy]
    exact mul_mem (mul_mem (mul_mem hx0 hy0) (inv_mem hx0)) (inv_mem hy0)
  have hfinP : Finite P := Finite.of_injective (Subgroup.inclusion hPB)
    (Subgroup.inclusion_injective hPB)
  have hfinK : Finite K := Finite.of_injective (Subgroup.inclusion hKB)
    (Subgroup.inclusion_injective hKB)
  obtain ⟨S, hS⟩ : ∃ S : Subgroup Γ, S = K ⊓ P := ⟨_, rfl⟩
  have hSK : S ≤ K := hS ▸ inf_le_left
  have hSP : S ≤ P := hS ▸ inf_le_right
  have hmemS : ∀ g, g ∈ S ↔ g ∈ K ∧ g ∈ P := fun g => by rw [hS, Subgroup.mem_inf]
  have hfinS : Finite S := Finite.of_injective (Subgroup.inclusion hSP)
    (Subgroup.inclusion_injective hSP)
  have hSdvd : Nat.card S ∣ 3 ^ 3 := by
    have := Subgroup.card_dvd_of_le hSP
    rwa [hP] at this
  obtain ⟨m, hm, hSm⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hSdvd
  interval_cases m
  ·
    have hS1 : Nat.card S = 1 := by simpa using hSm
    have hSbot : S = ⊥ := (Subgroup.card_eq_one).1 hS1
    have hinj : Function.Injective (fun kp : K × P =>
        (⟨(kp.1 : Γ) * kp.2, mul_mem (hKB kp.1.2) (hPB kp.2.2)⟩ : B)) := by
      intro kp kp' h
      have h1 : (kp.1 : Γ) * kp.2 = kp'.1 * kp'.2 := congrArg Subtype.val h
      have h2 : ((kp'.1 : Γ))⁻¹ * kp.1 = kp'.2 * (kp.2 : Γ)⁻¹ := by
        have := congrArg (fun g => (kp'.1 : Γ)⁻¹ * g * (kp.2 : Γ)⁻¹) h1
        simpa [mul_assoc] using this
      have h3 : ((kp'.1 : Γ))⁻¹ * kp.1 ∈ S := by
        rw [hmemS]
        refine ⟨mul_mem (inv_mem kp'.1.2) kp.1.2, ?_⟩
        rw [h2]
        exact mul_mem kp'.2.2 (inv_mem kp.2.2)
      rw [hSbot, Subgroup.mem_bot, inv_mul_eq_one] at h3
      have h4 : kp.1 = kp'.1 := Subtype.ext h3.symm
      have h5 : (kp.2 : Γ) = kp'.2 := by
        have : (kp.1 : Γ) * kp.2 = kp.1 * kp'.2 := by rw [h1, ← h3]
        exact mul_left_cancel this
      exact Prod.ext h4 (Subtype.ext h5)
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hP, hB] at hle
    omega
  ·
    have hS3 : Nat.card S = 3 := by simpa using hSm
    obtain ⟨a, haS, ha1⟩ : ∃ a ∈ S, a ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : S = ⊥ := (Subgroup.eq_bot_iff_forall S).2 hcon
      rw [this] at hS3
      simp at hS3
    have haP : a ∈ P := hSP haS
    have haK : a ∈ K := hSK haS
    have ha3 : a ^ 3 = 1 := hexp a haP
    have haz : a ≠ z := fun h => hzK (h ▸ haK)
    have haz' : a⁻¹ ≠ z := fun h => hzK (h ▸ inv_mem haK)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf a = 3 := orderOf_eq_prime ha3 ha1
    have hSz : S = Subgroup.zpowers a := by
      refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 haS) ?_).symm
      rw [hS3, Nat.card_zpowers, hord]
    obtain ⟨N, hNcard, hNmem⟩ := hN a haP ha1 haz haz'
    have hsub : (K : Set Γ) ⊆ (S : Set Γ) ∪ ↑N := by
      intro x hx
      by_cases hxP : x ∈ P
      · exact Or.inl ((hmemS x).2 ⟨hx, hxP⟩)
      · right
        refine hNmem x (hKB hx) hxP ?_
        have hb : x * a * x⁻¹ ∈ S := (hmemS _).2 ⟨mul_mem (mul_mem hx haK) (inv_mem hx),
          hnorm x (hKB hx) a haP⟩
        rw [hSz] at hb
        rcases eq_one_or_eq_or_eq_inv_of_mem_zpowers ha3 hb with h | h | h
        · exact absurd (by simpa using h) ha1
        · exact Or.inl h
        · exact Or.inr h
    have hfinS' : (S : Set Γ).Finite := Set.toFinite _
    have hle : (K : Set Γ).ncard ≤ ((S : Set Γ) ∪ ↑N).ncard :=
      Set.ncard_le_ncard hsub (hfinS'.union N.finite_toSet)
    have h1 : ((S : Set Γ) ∪ ↑N).ncard ≤ (S : Set Γ).ncard + (N : Set Γ).ncard :=
      Set.ncard_union_le _ _
    rw [Set.ncard_coe_finset] at h1
    have h2 : (S : Set Γ).ncard = 3 := by rw [← Nat.card_coe_set_eq]; exact hS3
    have h3 : Nat.card K = (K : Set Γ).ncard := Nat.card_coe_set_eq _
    omega
  ·
    have hS9 : Nat.card S = 9 := by simpa using hSm
    exact absurd (hSK (hzxy ▸ commutator_mem_of_card_eq_nine hSP hP hS9 hx0 hy0)) hzK
  ·
    have hS27 : Nat.card S = 27 := by simpa using hSm
    have hSP' : S = P := Subgroup.eq_of_le_of_card_ge hSP (by rw [hP, hS27])
    exact absurd (hSK (hSP' ▸ hzP)) hzK

end CFSG.SignalizerFunctorTheorem.NonLocalExc
