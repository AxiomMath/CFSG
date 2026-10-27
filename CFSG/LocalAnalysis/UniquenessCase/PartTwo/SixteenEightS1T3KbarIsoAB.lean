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
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup

theorem s16t3_exists_mulEquiv_of_quotientEquiv
    {J J' : Type*} [CommGroup J] [CommGroup J'] [Finite J] [Finite J']
    {Y : Subgroup J} {Y' : Subgroup J'} [Y.Normal] [Y'.Normal]
    (hJ : ∀ j : J, j * j = 1) (hJ' : ∀ j : J', j * j = 1)
    (hcard : Nat.card ↥Y = Nat.card ↥Y')
    (ψ : J ⧸ Y ≃* J' ⧸ Y') :
    ∃ φ : J ≃* J',
      (∀ u : J, φ u ∈ Y' ↔ u ∈ Y) ∧
      ∀ u : J, QuotientGroup.mk' Y' (φ u) = ψ (QuotientGroup.mk' Y u) := by
  classical
  have htwoJ : ∀ x : Additive J, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    change Additive.ofMul x.toMul + Additive.ofMul x.toMul = 0
    rw [← ofMul_mul, hJ, ofMul_one]
  have htwoJ' : ∀ x : Additive J', (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    change Additive.ofMul x.toMul + Additive.ofMul x.toMul = 0
    rw [← ofMul_mul, hJ', ofMul_one]
  letI : Module (ZMod 2) (Additive J) := AddCommGroup.zmodModule htwoJ
  letI : Module (ZMod 2) (Additive J') := AddCommGroup.zmodModule htwoJ'
  let Ys : Submodule (ZMod 2) (Additive J) :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup Y)
  let Ys' : Submodule (ZMod 2) (Additive J') :=
    AddSubgroup.toZModSubmodule 2 (Subgroup.toAddSubgroup Y')
  obtain ⟨K, hK⟩ := Ys.exists_isCompl
  obtain ⟨K', hK'⟩ := Ys'.exists_isCompl
  have hmemY : ∀ y : J, Additive.ofMul y ∈ Ys ↔ y ∈ Y := by
    intro y; simp [Ys]
  have hmemY' : ∀ y : J', Additive.ofMul y ∈ Ys' ↔ y ∈ Y' := by
    intro y; simp [Ys']
  have hcardYs : Nat.card ↥Ys = Nat.card ↥Y :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun x => hmemY x))
  have hcardYs' : Nat.card ↥Ys' = Nat.card ↥Y' :=
    Nat.card_congr (Equiv.subtypeEquiv Additive.ofMul (fun x => hmemY' x))
  have hcardA : Nat.card ↥Ys = Nat.card ↥Ys' := by rw [hcardYs, hcardYs', hcard]
  have hfr : Module.finrank (ZMod 2) Ys = Module.finrank (ZMod 2) Ys' := by
    have h1 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Ys)
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Ys')
    rw [Nat.card_zmod] at h1 h2
    have hc : (2 : ℕ) ^ Module.finrank (ZMod 2) Ys = 2 ^ Module.finrank (ZMod 2) Ys' := by
      rw [← h1, ← h2, hcardA]
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) hc
  let eY : Ys ≃ₗ[ZMod 2] Ys' := LinearEquiv.ofFinrankEq Ys Ys' hfr
  let q : (Additive J ⧸ Ys) ≃ₗ[ZMod 2] K := Submodule.quotientEquivOfIsCompl Ys K hK
  let q' : (Additive J' ⧸ Ys') ≃ₗ[ZMod 2] K' := Submodule.quotientEquivOfIsCompl Ys' K' hK'
  let eK : K ≃+ K' := q.symm.toAddEquiv.trans (ψ.toAdditive.trans q'.toAddEquiv)
  let eP := Submodule.prodEquivOfIsCompl Ys K hK
  let eP' := Submodule.prodEquivOfIsCompl Ys' K' hK'
  let φA : Additive J ≃+ Additive J' :=
    eP.symm.toAddEquiv.trans ((eY.toAddEquiv.prodCongr eK).trans eP'.toAddEquiv)
  have hfst : ∀ a : Additive J, (eP'.symm (φA a)).2 = eK ((eP.symm a).2) := by
    intro a
    change (eP'.toAddEquiv.symm (φA a)).2 = eK ((eP.toAddEquiv.symm a).2)
    have h : φA a = eP'.toAddEquiv
        ((eY.toAddEquiv.prodCongr eK) (eP.toAddEquiv.symm a)) := rfl
    rw [h, AddEquiv.symm_apply_apply]
    rfl
  have hmemA : ∀ a : Additive J, φA a ∈ Ys' ↔ a ∈ Ys := by
    intro a
    rw [← Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Ys' K' hK' (x := φA a),
      hfst a, ← Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero Ys K hK (x := a)]
    constructor
    · intro h
      exact eK.injective (by rw [h, map_zero])
    · intro h
      rw [h, map_zero]
  have hq : ∀ a : Additive J, q (Submodule.Quotient.mk (p := Ys) a) = (eP.symm a).2 := by
    intro a
    rw [Submodule.quotientEquivOfIsCompl_apply_mk, Submodule.prodEquivOfIsCompl_symm_apply]
  have hq' : ∀ a : Additive J', q' (Submodule.Quotient.mk (p := Ys') a) = (eP'.symm a).2 := by
    intro a
    rw [Submodule.quotientEquivOfIsCompl_apply_mk, Submodule.prodEquivOfIsCompl_symm_apply]
  have hquotA : ∀ a : Additive J,
      Submodule.Quotient.mk (p := Ys') (φA a) =
        ψ.toAdditive (Submodule.Quotient.mk (p := Ys) a) := by
    intro a
    apply q'.injective
    rw [hq' (φA a), hfst a]
    have h2 : q.symm ((eP.symm a).2) = Submodule.Quotient.mk (p := Ys) a := by
      rw [← hq a, LinearEquiv.symm_apply_apply]
    rw [← h2]
    rfl
  refine ⟨(MulEquiv.toAdditive (G := J) (H := J')).symm φA, ?_, ?_⟩
  · intro u
    rw [← hmemY' ((MulEquiv.toAdditive (G := J) (H := J')).symm φA u), ← hmemY u]
    change φA (Additive.ofMul u) ∈ Ys' ↔ Additive.ofMul u ∈ Ys
    exact hmemA (Additive.ofMul u)
  · intro u
    exact hquotA (Additive.ofMul u)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
