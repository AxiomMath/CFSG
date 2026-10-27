module

import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.LocalAnalysis.RankThreeEvenClassification.FrattiniFoundations
import CFSG.CharacterTheory.Semidihedral.Local.QuaternionNormalForm
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
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
public import Mathlib.GroupTheory.Frattini
public import Mathlib.GroupTheory.SpecificGroups.Quaternion
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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
public import Mathlib.Topology.Sheaves.Init

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Source

variable {G : Type*} [Group G]

theorem eq_one_of_pow_three_eq_one {S : Subgroup G} (hS : IsPGroup 2 S) {g : G} (hg : g ∈ S)
    (h3 : g ^ 3 = 1) : g = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨g, hg⟩
  have h1 : orderOf g ∣ 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one]
    simpa using congrArg Subtype.val hk
  have h2 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem not_three_dvd_card_of_isPGroup_two [Finite G] {R : Subgroup G} (hR : IsPGroup 2 R) :
    ¬ 3 ∣ Nat.card R := by
  obtain ⟨k, hk⟩ := hR.exists_card_eq
  rw [hk]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega

theorem mem_normalizer_closure_of_pow_three {x : G} (hx : x ^ 3 = 1) {s : Set G}
    (hs : ∀ g ∈ s, x * g * x⁻¹ ∈ Subgroup.closure s) :
    x ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  set K := Subgroup.closure s
  have hK : ∀ h ∈ K, x * h * x⁻¹ ∈ K := by
    intro h hh
    induction hh using Subgroup.closure_induction with
    | mem g hg => exact hs g hg
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact K.one_mem
    | mul a b _ _ ha hb =>
      have := K.mul_mem ha hb
      rwa [show x * a * x⁻¹ * (x * b * x⁻¹) = x * (a * b) * x⁻¹ by group] at this
    | inv a _ ha =>
      have := K.inv_mem ha
      rwa [show (x * a * x⁻¹)⁻¹ = x * a⁻¹ * x⁻¹ by group] at this
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨hK h, fun hh => ?_⟩
  have h2 := hK _ (hK _ hh)
  have heq : x * (x * (x * h * x⁻¹) * x⁻¹) * x⁻¹ = h := by
    have hx' : x * x * x = 1 := by rw [← pow_three', hx]
    calc x * (x * (x * h * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * h * (x * x * x)⁻¹ := by
          simp only [mul_inv_rev, mul_assoc]
      _ = h := by rw [hx']; simp
  rwa [heq] at h2

theorem commutator_eq_bot_or_eq_of_minimal [Finite G] {X S R : Subgroup G}
    (hX : IsPGroup 3 X) (hS : IsPGroup 2 S)
    (hmin : ∀ S' ≤ S, ⁅S', X⁆ = S' → S' ≠ ⊥ → S' = S) (hRS : R ≤ S)
    (hRX : X ≤ Subgroup.normalizer (R : Set G)) : ⁅R, X⁆ = ⊥ ∨ R = S := by
  have hle : ⁅R, X⁆ ≤ R := Subgroup.le_normalizer_iff_commutator_le_left.mp hRX
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three X R hX (not_three_dvd_card_of_isPGroup_two (hS.to_le hRS)) hRX
  by_cases hbot : ⁅R, X⁆ = ⊥
  · exact Or.inl hbot
  · right
    have hS' := hmin _ (hle.trans hRS) hidem hbot
    exact le_antisymm hRS (hS' ▸ hle)

theorem conj_eq_of_square_relations {u v : G} (hv : v ^ 2 = u ^ 2)
    (huv : (u * v) ^ 2 = (u ^ 2)⁻¹) : v * u * v⁻¹ = u * ((u ^ 2) ^ 3)⁻¹ := by
  simp only [pow_two] at hv huv
  rw [← pow_mul]
  calc v * u * v⁻¹ = u⁻¹ * (u * v * (u * v)) * (v * v)⁻¹ := by group
    _ = u⁻¹ * (u * u)⁻¹ * (u * u)⁻¹ := by rw [huv, hv]
    _ = u * (u ^ (2 * 3))⁻¹ := by group

theorem pow_six_eq_one_of_square_relations {u v : G} (hv : v ^ 2 = u ^ 2)
    (huv : (u * v) ^ 2 = (u ^ 2)⁻¹) : (u ^ 2) ^ 6 = 1 := by
  have hc := conj_eq_of_square_relations hv huv
  set w := ((u ^ 2) ^ 3)⁻¹ with hw_def
  have hw : v * w * v⁻¹ = w := by
    rw [hw_def, ← hv]
    group
  have hu : u = u * w * w := by
    calc u = v ^ 2 * u * (v ^ 2)⁻¹ := by rw [hv]; group
      _ = v * (v * u * v⁻¹) * v⁻¹ := by simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = v * (u * w) * v⁻¹ := by rw [hc]
      _ = (v * u * v⁻¹) * (v * w * v⁻¹) := by group
      _ = u * w * w := by rw [hc, hw]
  have hww : w * w = 1 := by
    have := congrArg (u⁻¹ * ·) hu
    simpa [mul_assoc] using this.symm
  rw [hw_def] at hww
  calc (u ^ 2) ^ 6 = (((u ^ 2) ^ 3)⁻¹ * ((u ^ 2) ^ 3)⁻¹)⁻¹ := by group
    _ = 1 := by rw [hww, inv_one]

theorem kleinFour_or_quaternion_of_relations {u v : G} (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huv : u ≠ v) (hv : v ^ 2 = u ^ 2) (huv2 : (u * v) ^ 2 = (u ^ 2)⁻¹)
    (hz : (u ^ 2) ^ 2 = 1) :
    IsKleinFour (Subgroup.closure ({u, v} : Set G)) ∨
      Nonempty (Subgroup.closure ({u, v} : Set G) ≃* QuaternionGroup 2) := by
  have hc := conj_eq_of_square_relations hv huv2
  by_cases hz1 : u ^ 2 = 1
  ·
    have hu2 : u * u = 1 := by rw [← pow_two, hz1]
    have hv2 : v * v = 1 := by rw [← pow_two, hv, hz1]
    have hcomm : Commute u v := by
      have h1 : u * v * (u * v) = 1 := by rw [← pow_two, huv2, hz1, inv_one]
      have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
      have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
      have h2 : v * u = u * v := by
        calc v * u = u⁻¹ * (u * v * (u * v)) * v⁻¹ := by group
          _ = u * v := by rw [h1, hui, hvi, mul_one]
      exact h2.symm
    left
    have hK : Subgroup.closure ({u, v} : Set G) =
        CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions u v hu2 hv2 hcomm := by
      apply le_antisymm
      · rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        change g ∈ ({u * v, u, v, 1} : Set G)
        rcases hg with rfl | rfl <;> simp
      · intro g hg
        have hg' : g ∈ ({u * v, u, v, 1} : Set G) := hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg'
        rcases hg' with rfl | rfl | rfl | rfl
        · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
            (Subgroup.subset_closure (by simp))
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.subset_closure (by simp)
        · exact Subgroup.one_mem _
    rw [hK]
    exact CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions u v hu2 hv2 hu1 hv1
      huv hcomm
  ·
    right
    set K := Subgroup.closure ({u, v} : Set G) with hK_def
    have huK : u ∈ K := Subgroup.subset_closure (by simp)
    have hvK : v ∈ K := Subgroup.subset_closure (by simp)
    have hgen : Subgroup.closure ({⟨u, huK⟩, ⟨v, hvK⟩} : Set K) = ⊤ := by
      convert Subgroup.closure_closure_coe_preimage (k := ({u, v} : Set G)) using 2
      ext g
      simp [Subtype.ext_iff]
    have hord : orderOf (⟨u, huK⟩ : K) = 2 * 2 := by
      rw [Subgroup.orderOf_mk]
      have : orderOf u = 2 ^ (1 + 1) :=
        orderOf_eq_prime_pow (by rwa [pow_one]) (by rw [pow_succ, pow_one, pow_mul, hz])
      rw [this]
      norm_num
    have hinv : v * u * v⁻¹ = u⁻¹ := by
      have h3 : (u ^ 2) ^ 3 = u ^ 2 := by
        rw [show (u ^ 2) ^ 3 = (u ^ 2) ^ 2 * u ^ 2 from pow_succ _ 2, hz, one_mul]
      rw [hc, h3]
      group
    have hnot : (⟨v, hvK⟩ : K) ∉ Subgroup.zpowers (⟨u, huK⟩ : K) := by
      intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hvk : u ^ k = v := by simpa using congrArg Subtype.val hk
      have hcomm : v * u * v⁻¹ = u := by
        rw [← hvk]
        group
      rw [hinv] at hcomm
      apply hz1
      calc u ^ 2 = u * u := pow_two u
        _ = u * u⁻¹ := by rw [hcomm]
        _ = 1 := mul_inv_cancel u
    have hy2 : (⟨v, hvK⟩ : K) ^ 2 = (⟨u, huK⟩ : K) ^ 2 := Subtype.ext (by simpa using hv)
    have hyx : (⟨v, hvK⟩ : K) * ⟨u, huK⟩ * (⟨v, hvK⟩ : K)⁻¹ = (⟨u, huK⟩ : K)⁻¹ :=
      Subtype.ext (by simpa using hinv)
    obtain ⟨⟨e, -⟩, -⟩ :=
      CFSG.Semidihedral.Local.quaternion_normal_form_isomorphism (m := 2) (by norm_num) hgen
        hord hnot hy2 hyx
    exact ⟨e.symm⟩

theorem kleinFour_or_quaternion_of_minimal_commutator [Finite G] {X S : Subgroup G}
    (hX : Nat.card X = 3) (hS : IsPGroup 2 S) (hSX : ⁅S, X⁆ = S) (hSbot : S ≠ ⊥)
    (hmin : ∀ S' ≤ S, ⁅S', X⁆ = S' → S' ≠ ⊥ → S' = S) :
    IsKleinFour S ∨ Nonempty (S ≃* QuaternionGroup 2) := by
  have hX3 : IsPGroup 3 X := IsPGroup.of_card (n := 1) (by rw [hX, pow_one])
  have hXS : X ≤ Subgroup.normalizer (S : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hSX.le
  obtain ⟨x, hxX, hx1⟩ : ∃ x ∈ X, x ≠ 1 := by
    rcases Subgroup.bot_or_exists_ne_one X with h | h
    · rw [h, Subgroup.card_bot] at hX
      omega
    · exact h
  have hordx : orderOf x = 3 := by
    have hdvd : orderOf x ∣ 3 := hX ▸ Subgroup.orderOf_dvd_natCard X hxX
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hx1
    · exact h
  have hx3 : x ^ 3 = 1 := hordx ▸ pow_orderOf_eq_one x
  have hXeq : Subgroup.zpowers x = X := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxX)
    rw [Nat.card_zpowers, hordx, hX]
  have hxS : ∀ g ∈ S, x * g * x⁻¹ ∈ S := fun g hg =>
    (Subgroup.mem_normalizer_iff.mp (hXS hxX) g).mp hg
  obtain ⟨s, hsS, hs⟩ : ∃ s ∈ S, x * s * x⁻¹ ≠ s := by
    by_contra h
    push Not at h
    apply hSbot
    rw [← hSX, Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer, ← hXeq,
      Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    have := h g hg
    calc g * x = x * g * x⁻¹ * x := by rw [this]
      _ = x * g := by group
  set u := s⁻¹ * (x * s * x⁻¹) with hu_def
  set v := x * u * x⁻¹ with hv_def
  have huS : u ∈ S := S.mul_mem (S.inv_mem hsS) (hxS s hsS)
  have hvS : v ∈ S := hxS u huS
  have hu1 : u ≠ 1 := by
    intro h
    apply hs
    have : s⁻¹ * (x * s * x⁻¹) = 1 := h
    calc x * s * x⁻¹ = s * (s⁻¹ * (x * s * x⁻¹)) := by group
      _ = s := by rw [this, mul_one]
  have hv1 : v ≠ 1 := by
    intro h
    apply hu1
    calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
      _ = 1 := by rw [← hv_def, h]; group
  have hxv : x * v * x⁻¹ = (u * v)⁻¹ := by
    have hx' : x * x * x = 1 := by rw [← pow_three', hx3]
    have key : u * v * (x * v * x⁻¹) = s⁻¹ * (x * x * x) * s * (x * x * x)⁻¹ := by
      rw [hv_def, hu_def]
      group
    rw [hx'] at key
    simp only [mul_one, inv_one, inv_mul_cancel] at key
    exact eq_inv_of_mul_eq_one_right key
  have hxu : x * u * x⁻¹ ≠ u := by
    intro h
    have hvu : v = u := h
    have h' : u = (u * u)⁻¹ := by
      calc u = x * v * x⁻¹ := by rw [hvu, h]
        _ = (u * v)⁻¹ := hxv
        _ = (u * u)⁻¹ := by rw [hvu]
    apply hu1
    apply eq_one_of_pow_three_eq_one hS huS
    calc u ^ 3 = u * (u * u) := pow_three u
      _ = (u * u)⁻¹ * (u * u) := by rw [← h']
      _ = 1 := inv_mul_cancel _
  set R := Subgroup.closure ({u, v} : Set G) with hR_def
  have hRS : R ≤ S := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact huS
    · exact hvS
  have hRX : X ≤ Subgroup.normalizer (R : Set G) := by
    rw [← hXeq, Subgroup.zpowers_le]
    apply mem_normalizer_closure_of_pow_three hx3
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · show v ∈ R
      exact Subgroup.subset_closure (by simp)
    · show x * v * x⁻¹ ∈ R
      rw [hxv]
      exact R.inv_mem (R.mul_mem (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp)))
  have hRS' : R = S := by
    rcases commutator_eq_bot_or_eq_of_minimal hX3 hS hmin hRS hRX with h | h
    · exfalso
      apply hxu
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at h
      have hu : u ∈ Subgroup.centralizer (X : Set G) := h (Subgroup.subset_closure (by simp))
      rw [Subgroup.mem_centralizer_iff] at hu
      have := hu x hxX
      calc x * u * x⁻¹ = u * x * x⁻¹ := by rw [this]
        _ = u := by group
    · exact h
  set Q := Subgroup.closure ({u ^ 2, v ^ 2, (u * v) ^ 2} : Set G) with hQ_def
  have hconj_u2 : x * u ^ 2 * x⁻¹ = v ^ 2 := by rw [← conj_pow]
  have hconj_v2 : x * v ^ 2 * x⁻¹ = ((u * v) ^ 2)⁻¹ := by rw [← conj_pow, hxv, inv_pow]
  have hconj_uv2 : x * (u * v) ^ 2 * x⁻¹ = (u ^ 2)⁻¹ := by
    rw [← conj_pow]
    have : x * (u * v) * x⁻¹ = u⁻¹ := by
      calc x * (u * v) * x⁻¹ = (x * u * x⁻¹) * (x * v * x⁻¹) := by group
        _ = u⁻¹ := by rw [← hv_def, hxv]; group
    rw [this, inv_pow]
  have hQS : Q ≤ S := by
    rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact S.pow_mem huS 2
    · exact S.pow_mem hvS 2
    · exact S.pow_mem (S.mul_mem huS hvS) 2
  have hQX : X ≤ Subgroup.normalizer (Q : Set G) := by
    rw [← hXeq, Subgroup.zpowers_le]
    apply mem_normalizer_closure_of_pow_three hx3
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · rw [hconj_u2]
      exact Subgroup.subset_closure (by simp)
    · rw [hconj_v2]
      exact Q.inv_mem (Subgroup.subset_closure (by simp))
    · rw [hconj_uv2]
      exact Q.inv_mem (Subgroup.subset_closure (by simp))
  have hQne : Q ≠ S := by
    intro hQS'
    have hle : Q ≤ (frattini S).map S.subtype := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact ⟨⟨u, huS⟩ ^ 2, CFSG.RankThreeEvenClassification.Helpers.pGroup_pow_mem_frattini 2
          Nat.prime_two hS _, by simp⟩
      · exact ⟨⟨v, hvS⟩ ^ 2, CFSG.RankThreeEvenClassification.Helpers.pGroup_pow_mem_frattini 2
          Nat.prime_two hS _, by simp⟩
      · exact ⟨(⟨u, huS⟩ * ⟨v, hvS⟩) ^ 2,
          CFSG.RankThreeEvenClassification.Helpers.pGroup_pow_mem_frattini 2 Nat.prime_two hS _,
          by simp⟩
    have htop : frattini S = ⊤ := by
      rw [eq_top_iff]
      intro g _
      have hgQ : (g : G) ∈ Q := by
        rw [hQS']
        exact g.2
      obtain ⟨g', hg', hgg'⟩ := hle hgQ
      have : g' = g := Subtype.ext hgg'
      exact this ▸ hg'
    have hbot : (⊥ : Subgroup S) = ⊤ := frattini_nongenerating (by rw [htop, sup_top_eq])
    apply hSbot
    rw [eq_bot_iff]
    intro g hg
    have : (⟨g, hg⟩ : S) ∈ (⊥ : Subgroup S) := hbot ▸ Subgroup.mem_top _
    rw [Subgroup.mem_bot] at this
    simpa using congrArg Subtype.val this
  have hQc : Q ≤ Subgroup.centralizer (X : Set G) := by
    rcases commutator_eq_bot_or_eq_of_minimal hX3 hS hmin hQS hQX with h | h
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    · exact absurd h hQne
  have hcomm_x : ∀ g ∈ Q, x * g * x⁻¹ = g := by
    intro g hg
    have := Subgroup.mem_centralizer_iff.mp (hQc hg) x hxX
    calc x * g * x⁻¹ = g * x * x⁻¹ := by rw [this]
      _ = g := by group
  have hv2 : v ^ 2 = u ^ 2 := by
    rw [← hconj_u2]
    exact hcomm_x _ (Subgroup.subset_closure (by simp))
  have huv2 : (u * v) ^ 2 = (u ^ 2)⁻¹ := by
    have h1 : x * v ^ 2 * x⁻¹ = v ^ 2 := hcomm_x _ (Subgroup.subset_closure (by simp))
    rw [hconj_v2, hv2] at h1
    rw [← h1, inv_inv]
  have hz : (u ^ 2) ^ 2 = 1 := by
    apply eq_one_of_pow_three_eq_one hS (S.pow_mem (S.pow_mem huS 2) 2)
    rw [← pow_mul]
    exact pow_six_eq_one_of_square_relations hv2 huv2
  rw [← hRS']
  exact kleinFour_or_quaternion_of_relations hu1 hv1 (fun h => hxu h.symm) hv2 huv2 hz

end CFSG.RankThree.PartTwo.Source
