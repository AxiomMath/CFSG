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

namespace CFSG.Quasithin.H13.L319.S66

theorem relIndex_centralizer_le_of_local {G : Type} [Group G] [Finite G] {y : G} {A W : Subgroup G}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hyA : ∀ a ∈ A, y * a * y⁻¹ ∈ A) (hy3 : ∀ a ∈ A, y ^ 3 * a * (y ^ 3)⁻¹ = a)
    (hWA : W ≤ A) {M : Type} [CommGroup M] [Finite M] (ι : ↥A →* M)
    (hker : ∀ a : ↥A, ι a = 1 ↔ (a : G) ∈ W)
    (σ : M →* M) (hσ : ∀ a : ↥A, ι ⟨y * (a : G) * y⁻¹, hyA a a.2⟩ = σ (ι a))
    (hM2 : ∀ m : M, m ^ 2 = 1) (b : ℕ)
    (hb : Set.ncard ((fun m => σ m * m⁻¹) '' (Set.range ι)) ≤ b) :
    (Subgroup.centralizer ({y} : Set G)).relIndex A ≤
      b * (Subgroup.centralizer ({y} : Set G)).relIndex W := by
  obtain ⟨C, hC⟩ : ∃ C : Subgroup G, C = Subgroup.centralizer ({y} : Set G) := ⟨_, rfl⟩
  rw [← hC]
  obtain ⟨f, hf⟩ : ∃ f : ↥A →* M, ∀ x, f x = σ (ι x) * (ι x)⁻¹ :=
    ⟨MonoidHom.mk' (fun x => σ (ι x) * (ι x)⁻¹) (fun a c => by
      simp only [map_mul, mul_inv]; ac_rfl), fun x => rfl⟩
  have hsq : ∀ m : M, m * m = 1 := fun m => by
    have h := hM2 m
    rwa [pow_two] at h
  have hCsN : (C.subgroupOf A).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hAc (g : G) g.2 (n : G) n.2,
      mul_inv_cancel_right]
    exact hn
  have hKle : f.ker ≤ (C.subgroupOf A) ⊔ (W.subgroupOf A) := by
    intro x hx
    rw [MonoidHom.mem_ker, hf, mul_inv_eq_one] at hx
    obtain ⟨c1, hc1⟩ : ∃ c : ↥A, (c : G) = y * (x : G) * y⁻¹ := ⟨⟨_, hyA _ x.2⟩, rfl⟩
    obtain ⟨c2, hc2⟩ : ∃ c : ↥A, (c : G) = y * (c1 : G) * y⁻¹ := ⟨⟨_, hyA _ c1.2⟩, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u : ↥A, u = x * c1 * c2 := ⟨_, rfl⟩
    have hι1 : ι c1 = ι x := by
      have e : c1 = ⟨y * (x : G) * y⁻¹, hyA _ x.2⟩ := Subtype.ext hc1
      rw [e, hσ x]
      exact hx
    have hι2 : ι c2 = ι x := by
      have e : c2 = ⟨y * (c1 : G) * y⁻¹, hyA _ c1.2⟩ := Subtype.ext hc2
      rw [e, hσ c1, hι1]
      exact hx
    have hιu : ι u = ι x := by
      rw [hu, map_mul, map_mul, hι1, hι2, hsq (ι x), one_mul]
    have h3 : y * (c2 : G) * y⁻¹ = (x : G) := by
      calc y * (c2 : G) * y⁻¹ = y ^ 3 * (x : G) * (y ^ 3)⁻¹ := by
            rw [pow_three, hc2, hc1]; group
        _ = (x : G) := hy3 _ x.2
    have hyu : y * (u : G) * y⁻¹ = (u : G) := by
      rw [hu, Subgroup.coe_mul, Subgroup.coe_mul]
      calc y * ((x : G) * (c1 : G) * (c2 : G)) * y⁻¹
          = (y * (x : G) * y⁻¹) * (y * (c1 : G) * y⁻¹) * (y * (c2 : G) * y⁻¹) := by group
        _ = (c1 : G) * (c2 : G) * (x : G) := by rw [← hc1, ← hc2, h3]
        _ = (x : G) * (c1 : G) * (c2 : G) := by
          rw [mul_assoc (c1 : G) (c2 : G) (x : G), hAc (c2 : G) c2.2 (x : G) x.2, ← mul_assoc,
            hAc (c1 : G) c1.2 (x : G) x.2]
    have hyu' : (u : G) * y = y * (u : G) := by
      calc (u : G) * y = (y * (u : G) * y⁻¹) * y := by rw [hyu]
        _ = y * (u : G) := by group
    have huC : (u : G) ∈ C := by
      rw [hC]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hyu'
    have huCs : u ∈ C.subgroupOf A := Subgroup.mem_subgroupOf.mpr huC
    have hιw : ι (x⁻¹ * u) = 1 := by
      rw [map_mul, map_inv, hιu, inv_mul_cancel]
    have hwW : ((x⁻¹ * u : ↥A) : G) ∈ W := (hker _).mp hιw
    have hwWs : (x⁻¹ * u)⁻¹ ∈ W.subgroupOf A := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_inv]
      exact inv_mem hwW
    have hxeq : x = u * (x⁻¹ * u)⁻¹ := by group
    rw [hxeq]
    exact mul_mem (Subgroup.mem_sup_left huCs) (Subgroup.mem_sup_right hwWs)
  have hfin : Nat.card f.ker * Nat.card f.range = Nat.card ↥A := by
    rw [← Subgroup.index_ker f]
    exact Subgroup.card_mul_index (H := f.ker)
  have hq : Nat.card f.range ≤ b := by
    have hsub : (f.range : Set M) ⊆ (fun m => σ m * m⁻¹) '' (Set.range ι) := by
      intro m hm'
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hm'
      exact ⟨ι x, ⟨x, rfl⟩, (hf x).symm⟩
    calc Nat.card f.range = (f.range : Set M).ncard := Nat.card_coe_set_eq (f.range : Set M)
      _ ≤ ((fun m => σ m * m⁻¹) '' (Set.range ι)).ncard := Set.ncard_le_ncard hsub
      _ ≤ b := hb
  have hsupW : (C.subgroupOf A).relIndex (C.subgroupOf A ⊔ W.subgroupOf A)
      = (C.subgroupOf A).relIndex (W.subgroupOf A) := by
    haveI := hCsN
    exact Subgroup.relIndex_sup_left (H := W.subgroupOf A) (K := C.subgroupOf A)
  have hne : (C.subgroupOf A).relIndex (C.subgroupOf A ⊔ W.subgroupOf A) ≠ 0 := by
    haveI : (C.subgroupOf A).IsFiniteRelIndex (C.subgroupOf A ⊔ W.subgroupOf A) :=
      Subgroup.isFiniteRelIndex_of_finiteIndex (H := C.subgroupOf A)
        (K := C.subgroupOf A ⊔ W.subgroupOf A)
    exact Subgroup.relIndex_ne_zero
  have hK3 : (C.subgroupOf A).relIndex f.ker ≤ (C.subgroupOf A).relIndex (W.subgroupOf A) := by
    rw [← hsupW]
    exact Subgroup.relIndex_le_of_le_right hKle hne
  have hI : (C.subgroupOf A).index * Nat.card ↥(C.subgroupOf A) = Nat.card ↥A :=
    Subgroup.index_mul_card (H := C.subgroupOf A)
  have hK1 : (C.subgroupOf A).relIndex f.ker * Nat.card ↥((C.subgroupOf A) ⊓ f.ker)
      = Nat.card ↥f.ker :=
    Subgroup.relIndex_mul_card (H := C.subgroupOf A) (K := f.ker)
  have hK2 : Nat.card ↥((C.subgroupOf A) ⊓ f.ker) ≤ Nat.card ↥(C.subgroupOf A) :=
    Subgroup.card_le_of_le (H := (C.subgroupOf A) ⊓ f.ker) (K := C.subgroupOf A) inf_le_left
  have hn : 0 < Nat.card ↥(C.subgroupOf A) := Nat.card_pos
  have key : (C.subgroupOf A).index * Nat.card ↥(C.subgroupOf A)
      ≤ (b * (C.subgroupOf A).relIndex (W.subgroupOf A)) * Nat.card ↥(C.subgroupOf A) := by
    calc (C.subgroupOf A).index * Nat.card ↥(C.subgroupOf A)
        = Nat.card ↥f.ker * Nat.card ↥f.range := hI.trans hfin.symm
      _ ≤ Nat.card ↥f.ker * b := Nat.mul_le_mul le_rfl hq
      _ = ((C.subgroupOf A).relIndex f.ker * Nat.card ↥((C.subgroupOf A) ⊓ f.ker)) * b := by
          rw [hK1]
      _ ≤ ((C.subgroupOf A).relIndex (W.subgroupOf A) * Nat.card ↥(C.subgroupOf A)) * b :=
          Nat.mul_le_mul (Nat.mul_le_mul hK3 hK2) le_rfl
      _ = (b * (C.subgroupOf A).relIndex (W.subgroupOf A)) * Nat.card ↥(C.subgroupOf A) := by
          ring
  have final : (C.subgroupOf A).index ≤ b * (C.subgroupOf A).relIndex (W.subgroupOf A) :=
    Nat.le_of_mul_le_mul_right key hn
  rw [← Subgroup.relIndex_subgroupOf (H := C) (K := W) (L := A) hWA]
  exact final

end CFSG.Quasithin.H13.L319.S66

end
