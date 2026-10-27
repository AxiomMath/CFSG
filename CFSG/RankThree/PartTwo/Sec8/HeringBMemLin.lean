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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec8.HeringBMem

theorem zmod2_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  decide +revert

theorem zmod2_zero_ne_one : (0 : ZMod 2) ≠ 1 := by
  decide

theorem tv_core {V : Type*} [AddCommGroup V] (B : V → V → ZMod 2)
    (hBl : ∀ u u' w, B (u + u') w = B u w + B u' w)
    (hBr : ∀ u w w', B u (w + w') = B u w + B u w')
    (hsymm : ∀ u w, B u w = B w u) (halt : ∀ u, B u u = 0)
    (hnd : ∀ a : V, a ≠ 0 → ∃ w, B w a = 1)
    (X : V → V) (hXadd : ∀ u u', X (u + u') = X u + X u') (hXinj : Function.Injective X)
    (hXB : ∀ u w, B (X u) (X w) = B u w) (a : V) (ha : a ≠ 0)
    (hr : ∀ y, X (X y) = y ∨ X (X y) = y + a) (hne : ∃ y, X (X y) ≠ y) : False := by
  have hX0 : X 0 = 0 := by
    have h := hXadd 0 0
    simpa using h
  have hZB : ∀ u w, B (X (X u)) (X (X w)) = B u w := by
    intro u w
    rw [hXB, hXB]
  have claim1 : ∀ w, X (X w) ≠ w → B w a = 1 := by
    intro w hw
    have hZw : X (X w) = w + a := (hr w).resolve_left hw
    by_contra hBw
    have hBw0 : B w a = 0 := (zmod2_cases (B w a)).resolve_right hBw
    obtain ⟨w'', hw''⟩ := hnd a ha
    have h1 : B (X (X w)) (X (X w'')) = B w w'' := hZB w w''
    rw [hZw] at h1
    have hB0 : B a w'' = 0 := by
      rcases hr w'' with hZ'' | hZ''
      · rw [hZ'', hBl] at h1
        linear_combination h1
      · rw [hZ''] at h1
        have e : B (w + a) (w'' + a) = B w w'' + B a w'' + B w a + B a a := by
          rw [hBr, hBl, hBl]
          ring
        linear_combination h1 - e - hBw0 - halt a
    exact zmod2_zero_ne_one (hB0.symm.trans ((hsymm a w'').trans hw''))
  obtain ⟨w₀, hw₀⟩ := hne
  have hZw₀ : X (X w₀) = w₀ + a := (hr w₀).resolve_left hw₀
  have claim2 : X a = a := by
    have h1 : X (X (X w₀)) = X w₀ + X a := by
      rw [hZw₀, hXadd]
    rcases hr (X w₀) with hc | hc
    · exfalso
      have hXa0 : X a = 0 := by
        have h2 := h1.symm.trans hc
        simpa using h2
      exact ha (hXinj (hXa0.trans hX0.symm))
    · exact add_left_cancel (h1.symm.trans hc)
  have hB1 : B (X w₀) (X (X w₀)) = B w₀ (X w₀) := hXB w₀ (X w₀)
  rw [hZw₀, hBr] at hB1
  have hs : B (X w₀) w₀ = B w₀ (X w₀) := hsymm (X w₀) w₀
  have hB2 : B (X w₀) a = 0 := by
    linear_combination hB1 - hs
  have hB3 : B (X w₀) (X a) = B w₀ a := hXB w₀ a
  rw [claim2] at hB3
  have hB4 : B w₀ a = 1 := claim1 w₀ hw₀
  exact zmod2_zero_ne_one (hB2.symm.trans (hB3.trans hB4))

theorem rank_one_of_half {V : Type*} [AddCommGroup V] [DecidableEq V] (f : V → V)
    (hf : ∀ y y', f (y + y') = f y + f y') (A B : Finset V)
    (hdec : ∀ y, ∃ s ∈ A, ∃ b ∈ B, y = s + b) (hA : ∀ s ∈ A, f s = s)
    (hadd : ∀ b ∈ B, ∀ b' ∈ B, b + b' ∈ B) (hB : B.card = 16)
    (hK : (B.filter fun b => f b = b).card = 8) :
    ∃ a : V, a ≠ 0 ∧ ∀ y, f y = y ∨ f y = y + a := by
  have hsplit : (B.filter fun b => f b = b).card + (B.filter fun b => ¬ f b = b).card
      = B.card :=
    Finset.card_filter_add_card_filter_not _
  have hS : (B.filter fun b => ¬ f b = b).card = 8 := by omega
  obtain ⟨y₀, hy₀⟩ := Finset.card_pos.mp (show 0 < (B.filter fun b => ¬ f b = b).card by omega)
  obtain ⟨hy₀B, hy₀f⟩ := Finset.mem_filter.mp hy₀
  obtain ⟨a, ha⟩ : ∃ a : V, a = f y₀ - y₀ := ⟨_, rfl⟩
  have hfa : f y₀ = y₀ + a := by
    rw [ha]
    abel
  have ha0 : a ≠ 0 := by
    intro h
    apply hy₀f
    rw [ha] at h
    exact sub_eq_zero.mp h
  have hsub : (B.filter fun b => f b = b).image (fun k => y₀ + k) ⊆
      B.filter fun b => ¬ f b = b := by
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨hkB, hfk⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨hadd y₀ hy₀B k hkB, ?_⟩
    rw [hf, hfk]
    intro h
    exact hy₀f (add_right_cancel h)
  have himg : ((B.filter fun b => f b = b).image (fun k => y₀ + k)).card = 8 := by
    rw [Finset.card_image_of_injective _ (add_right_injective y₀)]
    exact hK
  have himage : (B.filter fun b => f b = b).image (fun k => y₀ + k)
      = B.filter fun b => ¬ f b = b :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  have hclaim : ∀ b ∈ B, ¬ f b = b → f b = b + a := by
    intro b hb hfb
    have hbS : b ∈ B.filter fun c => ¬ f c = c := Finset.mem_filter.mpr ⟨hb, hfb⟩
    rw [← himage] at hbS
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hbS
    obtain ⟨_, hfk⟩ := Finset.mem_filter.mp hk
    rw [hf, hfk, hfa]
    abel
  refine ⟨a, ha0, fun y => ?_⟩
  obtain ⟨s, hs, b, hb, rfl⟩ := hdec y
  by_cases hfb : f b = b
  · left
    rw [hf, hA s hs, hfb]
  · right
    rw [hf, hA s hs, hclaim b hb hfb]
    abel

end CFSG.RankThree.PartTwo.Sec8.HeringBMem
