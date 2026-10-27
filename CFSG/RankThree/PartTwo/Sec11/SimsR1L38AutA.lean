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
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.PiTensorProduct
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Aut

open Module

section Flag

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]

theorem sub_self_mem_of_pow_three {G : V →ₗ[F] V} (hG : G * G * G = 1)
    (hF : ∀ c : F, c ^ 3 = 1 → c = 1) {W₀ W₁ : Submodule F V} (h01 : W₀ ≤ W₁)
    (hG0 : ∀ w ∈ W₀, G w ∈ W₀) (hG1 : ∀ w ∈ W₁, G w ∈ W₁)
    (hdim : finrank F W₁ = finrank F W₀ + 1) : ∀ w ∈ W₁, G w - w ∈ W₀ := by
  obtain ⟨w₁, hw₁, hw₁0⟩ : ∃ w₁ ∈ W₁, w₁ ∉ W₀ := by
    by_contra hcon
    have h10 : W₁ ≤ W₀ := fun w hw => by
      by_contra hw0
      exact hcon ⟨w, hw, hw0⟩
    have := Submodule.finrank_mono h10
    omega
  have hw10 : w₁ ≠ 0 := fun h => hw₁0 (h ▸ W₀.zero_mem)
  have hdisj : W₀ ⊓ (F ∙ w₁) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    rintro w ⟨hw0, hws⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hws
    by_cases hc : c = 0
    · simp [hc]
    · exfalso
      apply hw₁0
      have := W₀.smul_mem c⁻¹ hw0
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
  have hsup : W₀ ⊔ (F ∙ w₁) = W₁ := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le h01 (by rw [Submodule.span_le]; simpa using hw₁)
    · have := Submodule.finrank_sup_add_finrank_inf_eq W₀ (F ∙ w₁)
      rw [hdisj, finrank_bot, finrank_span_singleton hw10] at this
      omega
  have hdec : ∀ w ∈ W₁, ∃ a ∈ W₀, ∃ c : F, w = a + c • w₁ := by
    intro w hw
    have : w ∈ W₀ ⊔ (F ∙ w₁) := hsup ▸ hw
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp this
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hb
    exact ⟨a, ha, c, hab.symm⟩
  obtain ⟨a, ha, c, hc⟩ := hdec (G w₁) (hG1 w₁ hw₁)
  have hG3 : G (G (G w₁)) = w₁ := by
    have := LinearMap.congr_fun hG w₁
    simpa using this
  have h3 : (1 - c ^ 3) • w₁ ∈ W₀ := by
    have e1 : G (G (G w₁)) = (G (G a) + c • G a + c ^ 2 • a) + c ^ 3 • w₁ := by
      rw [hc]
      simp only [map_add, map_smul, hc, smul_add, smul_smul]
      module
    have hmem : G (G a) + c • G a + c ^ 2 • a ∈ W₀ :=
      W₀.add_mem (W₀.add_mem (hG0 _ (hG0 _ ha)) (W₀.smul_mem _ (hG0 _ ha)))
        (W₀.smul_mem _ ha)
    have : (1 - c ^ 3) • w₁ = G (G a) + c • G a + c ^ 2 • a := by
      rw [sub_smul, one_smul]
      exact (eq_sub_of_add_eq (e1.symm.trans hG3)).symm
    rw [this]
    exact hmem
  have hc3 : c ^ 3 = 1 := by
    by_contra hne
    apply hw₁0
    have h1 : (1 - c ^ 3) ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have := W₀.smul_mem (1 - c ^ 3)⁻¹ h3
    rwa [smul_smul, inv_mul_cancel₀ h1, one_smul] at this
  have hc1 : c = 1 := hF c hc3
  have hGw₁ : G w₁ - w₁ ∈ W₀ := by
    rw [hc, hc1, one_smul]
    simpa using ha
  intro w hw
  obtain ⟨a₀, ha₀, b, rfl⟩ := hdec w hw
  have : G (a₀ + b • w₁) - (a₀ + b • w₁) = (G a₀ - a₀) + b • (G w₁ - w₁) := by
    simp only [map_add, map_smul]
    module
  rw [this]
  exact W₀.add_mem (W₀.sub_mem (hG0 _ ha₀) ha₀) (W₀.smul_mem _ hGw₁)

theorem eq_one_of_commute_involution [CharP F 2]
    (hF : ∀ c : F, c ^ 3 = 1 → c = 1) (hV : finrank F V = 3)
    {T G : V →ₗ[F] V} (hT : T * T = 1) (hT1 : T ≠ 1) (hG : G * G * G = 1)
    (hTG : T * G = G * T) : G = 1 := by
  have h2 : ∀ u : V, u + u = 0 := fun u => by
    rw [← two_smul F u, CharTwo.two_eq_zero, zero_smul]
  have h2e : ∀ f : V →ₗ[F] V, f + f = 0 := fun f => LinearMap.ext fun u => by
    simp [h2]
  set n : V →ₗ[F] V := T - 1 with hn
  have hnn : n * n = 0 := by
    have e1 : n * n = T * T - (T + T) + 1 := by rw [hn]; noncomm_ring
    rw [e1, hT, h2e T, sub_zero]
    exact h2e 1
  have hnG : n * G = G * n := by
    rw [hn, sub_mul, mul_sub, hTG, one_mul, mul_one]
  have hn0 : n ≠ 0 := sub_ne_zero.mpr hT1
  have hrk : LinearMap.range n ≤ LinearMap.ker n := LinearMap.range_le_ker_iff.mpr hnn
  have hsum := LinearMap.finrank_range_add_finrank_ker n
  have hle := Submodule.finrank_mono hrk
  have hpos : 0 < finrank F (LinearMap.range n) := by
    rcases Nat.eq_zero_or_pos (finrank F (LinearMap.range n)) with h | h
    · exfalso
      apply hn0
      rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at h
      exact h
    · exact h
  have hr : finrank F (LinearMap.range n) = 1 := by omega
  have hk : finrank F (LinearMap.ker n) = 2 := by omega
  have hcomm : ∀ v, n (G v) = G (n v) := fun v => LinearMap.congr_fun hnG v
  have hinvR : ∀ w ∈ LinearMap.range n, G w ∈ LinearMap.range n := by
    rintro _ ⟨v, rfl⟩
    exact ⟨G v, hcomm v⟩
  have hinvK : ∀ w ∈ LinearMap.ker n, G w ∈ LinearMap.ker n := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hcomm, hw, map_zero]
  have hinvB : ∀ w ∈ (⊥ : Submodule F V), G w ∈ (⊥ : Submodule F V) := by
    intro w hw
    rw [Submodule.mem_bot] at hw ⊢
    rw [hw, map_zero]
  have s1 := sub_self_mem_of_pow_three hG hF (bot_le : ⊥ ≤ LinearMap.range n) hinvB hinvR
    (by rw [hr, finrank_bot])
  have s2 := sub_self_mem_of_pow_three hG hF hrk hinvR hinvK (by rw [hk, hr])
  have s3 := sub_self_mem_of_pow_three hG hF (le_top : LinearMap.ker n ≤ ⊤) hinvK
    (fun w _ => Submodule.mem_top) (by rw [finrank_top, hV, hk])
  refine LinearMap.ext fun v => ?_
  obtain ⟨a, ha⟩ : ∃ a, a = G v - v := ⟨_, rfl⟩
  have haK : a ∈ LinearMap.ker n := ha ▸ s3 v Submodule.mem_top
  obtain ⟨b, hb⟩ : ∃ b, b = G a - a := ⟨_, rfl⟩
  have hbR : b ∈ LinearMap.range n := hb ▸ s2 a haK
  have hGb : G b = b := sub_eq_zero.mp ((Submodule.mem_bot F).mp (s1 b hbR))
  have hGv : G v = v + a := by rw [ha]; abel
  have hGa : G a = a + b := by rw [hb]; abel
  have h3v : G (G (G v)) = v := by
    have := LinearMap.congr_fun hG v
    simpa using this
  have h3a : G (G (G a)) = a := by
    have := LinearMap.congr_fun hG a
    simpa using this
  have hab : a + b = 0 := by
    simp only [map_add, hGv, hGa, hGb] at h3v
    linear_combination (norm := module) h3v - h2 a - h2 b
  have ha0 : a = 0 := by
    have : G a = 0 := by rw [hGa, hab]
    rw [this, map_zero, map_zero] at h3a
    exact h3a.symm
  simpa [ha0] using hGv

end Flag

theorem matrix_eq_one_of_commute_involution {F : Type*} [Field F] [CharP F 2]
    (hF : ∀ c : F, c ^ 3 = 1 → c = 1)
    {T X : Matrix (Fin 3) (Fin 3) F} (hT : T * T = 1) (hT1 : T ≠ 1) (hX : X ^ 3 = 1)
    (hTX : T * X = X * T) : X = 1 := by
  let e := Matrix.toLinAlgEquiv' (R := F) (n := Fin 3)
  have key := eq_one_of_commute_involution (V := Fin 3 → F) hF (by simp) (T := e T) (G := e X)
    (by rw [← map_mul, hT, map_one]) (fun h => hT1 (e.injective (by rw [h, map_one])))
    (by rw [← pow_three', ← map_pow, hX, map_one]) (by rw [← map_mul, hTX, map_mul])
  exact e.injective (by rw [key, map_one])

end CFSG.RankThree.PartTwo.Sec11.SimsR1.L38Aut
