module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.F53Push

open Equiv

abbrev A5 : Type := ↥(alternatingGroup (Fin 5))

theorem a5_fix_two_aux : ∀ g : Perm (Fin 5), Perm.sign g = 1 → ∀ p q : Fin 5, p ≠ q → g p = p →
    g q = q → g ^ 4 = 1 → g = 1 := by
  decide +kernel

theorem a5_exists_moving : ∀ p : Fin 5, ∃ g : Perm (Fin 5), Perm.sign g = 1 ∧ g p ≠ p := by
  decide +kernel

theorem a5_exists_unique_max (B : Subgroup A5) (hB : Nat.card B = 4) :
    ∃ M : Subgroup A5, B ≤ M ∧ M < ⊤ ∧ ∀ T : Subgroup A5, B ≤ T → T < ⊤ → T ≤ M := by
  have h2 : IsPGroup 2 B := IsPGroup.of_card (n := 2) (by simpa using hB)
  have hmod := h2.card_modEq_card_fixedPoints (Fin 5)
  have hp : ∃ p : Fin 5, ∀ b ∈ B, b • p = p := by
    by_contra hne
    push Not at hne
    have : MulAction.fixedPoints B (Fin 5) = ∅ := by
      ext p
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hp
      obtain ⟨b, hb, hbp⟩ := hne p
      exact hbp (by simpa using hp ⟨b, hb⟩)
    rw [this] at hmod
    simp [Nat.ModEq] at hmod
  obtain ⟨p, hp⟩ := hp
  refine ⟨MulAction.stabilizer A5 p, fun b hb => hp b hb, ?_, ?_⟩
  · refine lt_top_iff_ne_top.mpr fun htop => ?_
    obtain ⟨g, hg, hgp⟩ := a5_exists_moving p
    have : (⟨g, Equiv.Perm.mem_alternatingGroup.mpr hg⟩ : A5) ∈ MulAction.stabilizer A5 p := by
      rw [htop]; trivial
    exact hgp (by simpa using this)
  · intro T hBT hT
    by_contra hnle
    rw [IsConcreteLE.not_le_iff_exists] at hnle
    obtain ⟨t, htT, hts⟩ := hnle
    have htp : t • p ≠ p := fun h => hts (by simpa using h)
    have hBp : ∀ b : B, (b : A5) • p = p := fun b => hp b b.2
    have hreg : ∀ x : Fin 5, ∃ τ ∈ T, τ • p = x := by
      intro x
      by_cases hx : x = p
      · exact ⟨1, T.one_mem, by simp [hx]⟩
      · have hq : ∀ b : B, (b : A5) • (t • p) ≠ p := by
          intro b h
          apply htp
          have h1 : (b : A5)⁻¹ • p = p := by
            have := hBp ⟨(b : A5)⁻¹, B.inv_mem b.2⟩
            simpa using this
          calc t • p = (b : A5)⁻¹ • ((b : A5) • (t • p)) := by simp
            _ = p := by rw [h, h1]
        let f : B → {y : Fin 5 // y ≠ p} := fun b => ⟨(b : A5) • (t • p), hq b⟩
        have hinj : Function.Injective f := by
          intro b b' hbb
          have hbb' : (b : A5) • (t • p) = (b' : A5) • (t • p) := congrArg Subtype.val hbb
          set g : A5 := (b : A5)⁻¹ * b' with hg
          have hgB : g ∈ B := B.mul_mem (B.inv_mem b.2) b'.2
          have hgq : g • (t • p) = t • p := by
            rw [hg, mul_smul, ← hbb', inv_smul_smul]
          have hgp : g • p = p := hp g hgB
          have hg4 : g ^ 4 = 1 := by
            have := pow_card_eq_one' (G := B) (x := ⟨g, hgB⟩)
            rw [hB] at this
            exact congrArg Subtype.val this
          have hg1 : g = 1 := by
            have := a5_fix_two_aux g.1 (Equiv.Perm.mem_alternatingGroup.mp g.2) p (t • p)
              (Ne.symm htp) hgp hgq (congrArg Subtype.val hg4)
            exact Subtype.ext this
          have : (b : A5) = b' := by
            rw [hg, inv_mul_eq_one] at hg1
            exact hg1
          exact Subtype.ext this
        have hbij : Function.Bijective f := by
          refine hinj.bijective_of_nat_card_le ?_
          rw [hB, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
          simp
        obtain ⟨b, hb⟩ := hbij.2 ⟨x, hx⟩
        refine ⟨(b : A5) * t, T.mul_mem (hBT b.2) htT, ?_⟩
        rw [mul_smul]
        exact congrArg Subtype.val hb
    have horb : MulAction.orbit T p = Set.univ := by
      ext x
      simp only [Set.mem_univ, iff_true]
      obtain ⟨τ, hτ, hτx⟩ := hreg x
      exact ⟨⟨τ, hτ⟩, hτx⟩
    have h5 : 5 ∣ Nat.card T := by
      have h1 := MulAction.index_stabilizer T p
      have h2 := Subgroup.card_mul_index (MulAction.stabilizer T p)
      rw [h1, horb] at h2
      refine ⟨Nat.card (MulAction.stabilizer T p), ?_⟩
      rw [← h2]
      simp [mul_comm]
    have h4 : 4 ∣ Nat.card T := hB ▸ Subgroup.card_dvd_of_le hBT
    have hcardA : Nat.card A5 = 60 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    have h60 : Nat.card T ∣ 60 := hcardA ▸ Subgroup.card_subgroup_dvd_card T
    have h20 : 20 ∣ Nat.card T := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h4 h5
    have hcases : Nat.card T = 20 ∨ Nat.card T = 60 := by
      obtain ⟨k, hk⟩ := h20
      have hk3 : k ∣ 3 := by
        rw [hk] at h60
        exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 20)).mp (by simpa using h60)
      rcases (Nat.dvd_prime Nat.prime_three).mp hk3 with h | h
      · left; rw [hk, h]
      · right; rw [hk, h]
    rcases hcases with h | h
    ·
      have hidx : T.index = 3 := by
        have := Subgroup.card_mul_index T
        rw [h, hcardA] at this
        omega
      have hfi : T.FiniteIndex := ⟨by omega⟩
      have hdvd := Subgroup.index_normalCore_dvd_factorial_index (H := T)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal T.normalCore with hb | ht
      · rw [hb, Subgroup.index_bot, hcardA, hidx] at hdvd
        norm_num [Nat.factorial] at hdvd
      · have : T = ⊤ := top_unique (ht ▸ Subgroup.normalCore_le T)
        exact absurd this (ne_of_lt hT)
    · exact (ne_of_lt hT) (Subgroup.eq_top_of_card_eq T (by rw [h, hcardA]))


theorem exists_unique_max_of_quotient_a5 {H : Type*} [Group H] (R : Subgroup H) (θ : H →* A5)
    (hθs : Function.Surjective θ) (hker : θ.ker ≤ R) (hcard : Nat.card (R.map θ) = 4) :
    ∃ M : Subgroup H, R ≤ M ∧ M < ⊤ ∧ ∀ Y : Subgroup H, R ≤ Y → Y < ⊤ → Y ≤ M := by
  obtain ⟨M₀, hBM, hM₀, hmax⟩ := a5_exists_unique_max (R.map θ) hcard
  refine ⟨M₀.comap θ, fun r hr => hBM ⟨r, hr, rfl⟩, ?_, fun Y hRY hY => ?_⟩
  · refine lt_top_iff_ne_top.mpr fun h => (lt_top_iff_ne_top.mp hM₀) ?_
    rw [eq_top_iff]
    intro x _
    obtain ⟨y, rfl⟩ := hθs x
    exact (Subgroup.mem_comap.mp (h ▸ Subgroup.mem_top y))
  · have hYM : Y.map θ ≤ M₀ := by
      refine hmax _ (Subgroup.map_mono hRY) (lt_top_iff_ne_top.mpr fun htop => ?_)
      apply (lt_top_iff_ne_top.mp hY)
      rw [eq_top_iff]
      intro y _
      have hy : θ y ∈ Y.map θ := htop ▸ Subgroup.mem_top _
      obtain ⟨y', hy', hyy⟩ := hy
      have hk : y'⁻¹ * y ∈ θ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hyy, inv_mul_cancel]
      have : y = y' * (y'⁻¹ * y) := by group
      rw [this]
      exact Y.mul_mem hy' (hRY (hker hk))
    intro y hy
    exact Subgroup.mem_comap.mpr (hYM ⟨y, hy, rfl⟩)

end CFSG.Quasithin.F53Push
