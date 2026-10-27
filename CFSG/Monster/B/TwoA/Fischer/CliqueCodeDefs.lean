module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.HopfAlgebra.Basic
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

namespace CFSG.Monster.B.TwoA.Fischer

open scoped IsMulCommutative

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

section Defs

variable (lab) (C : Set V) [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]

@[expose] noncomputable def cliqueLabelMap :
    (C →₀ ZMod 2) →ₗ[ZMod 2] Additive (Subgroup.closure (lab '' C)) :=
  Finsupp.linearCombination (ZMod 2) fun z =>
    Additive.ofMul ⟨lab z, Subgroup.subset_closure ⟨z, z.2, rfl⟩⟩

@[expose] noncomputable def cliqueCode : Submodule (ZMod 2) (C →₀ ZMod 2) :=
  LinearMap.ker (cliqueLabelMap lab C)

@[expose] def cliqueBlocks : Set (Set V) :=
  {B | ∃ f ∈ cliqueCode lab C, f.support.card = 6 ∧ B = Subtype.val '' (f.support : Set C)}

end Defs

section Gen

variable {C : Set V}

@[expose] def cliqueGen (z : C) : Subgroup.closure (lab '' C) :=
  ⟨lab z, Subgroup.subset_closure ⟨z, z.2, rfl⟩⟩

theorem coe_cliqueGen (z : C) : (cliqueGen (lab := lab) z : S) = lab z := rfl

@[expose] def conjGen (a : S) (ha : ∀ r ∈ Subgroup.closure (lab '' C),
    a * r * a⁻¹ ∈ Subgroup.closure (lab '' C)) :
    Subgroup.closure (lab '' C) →* Subgroup.closure (lab '' C) where
  toFun r := ⟨a * r * a⁻¹, ha r r.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' r s := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conj_mem_closure (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹) {a : S}
    (haC : ∀ x ∈ C, act a x ∈ C) (r : S) (hr : r ∈ Subgroup.closure (lab '' C)) :
    a * r * a⁻¹ ∈ Subgroup.closure (lab '' C) := by
  induction hr using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨z, hz, rfl⟩ := hx
    rw [← hlab]
    exact Subgroup.subset_closure ⟨_, haC z hz, rfl⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

end Gen

section Basic

variable {C : Set V} [CFSG.IsElementaryAbelian 2 (Subgroup.closure (lab '' C))]

theorem zmod_two_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide

theorem cliqueLabelMap_single (z : C) (a : ZMod 2) :
    cliqueLabelMap lab C (Finsupp.single z a) = a • Additive.ofMul (cliqueGen z) :=
  Finsupp.linearCombination_single _ _ _

theorem cliqueLabelMap_apply (f : C →₀ ZMod 2) :
    cliqueLabelMap lab C f = ∑ z ∈ f.support, Additive.ofMul (cliqueGen z) := by
  rw [cliqueLabelMap, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Finset.sum_congr rfl fun z hz => ?_
  rw [zmod_two_eq_one _ (Finsupp.mem_support_iff.1 hz), one_smul]
  rfl

theorem mem_cliqueCode_iff (f : C →₀ ZMod 2) :
    f ∈ cliqueCode lab C ↔ ∑ z ∈ f.support, Additive.ofMul (cliqueGen (lab := lab) z) = 0 := by
  rw [cliqueCode, LinearMap.mem_ker, cliqueLabelMap_apply]

theorem cliqueLabelMap_surjective : Function.Surjective (cliqueLabelMap lab C) := by
  intro x
  set K : Subgroup (Subgroup.closure (lab '' C)) :=
    AddSubgroup.toSubgroup' (LinearMap.range (cliqueLabelMap lab C)).toAddSubgroup
  have hK : K = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage, Subgroup.closure_le]
    rintro r ⟨z, hz, hr⟩
    refine ⟨Finsupp.single ⟨z, hz⟩ 1, ?_⟩
    rw [cliqueLabelMap_single, one_smul]
    congr 1
    exact Subtype.ext hr
  have hx : Additive.toMul x ∈ K := by
    rw [hK]
    exact Subgroup.mem_top _
  exact hx

theorem finrank_additive_of_natCard {G : Type*} [Group G] [CFSG.IsElementaryAbelian 2 G]
    [Finite G] {n : ℕ} (h : Nat.card G = 2 ^ n) : Module.finrank (ZMod 2) (Additive G) = n := by
  have h2 := FiniteField.pow_finrank_eq_natCard 2 (Additive G)
  rw [show Nat.card (Additive G) = Nat.card G from Nat.card_congr Additive.toMul, h] at h2
  exact Nat.pow_right_injective (le_refl 2) h2

theorem finrank_cliqueCode [Finite C] [Finite (Subgroup.closure (lab '' C))] {n : ℕ}
    (hR : Nat.card (Subgroup.closure (lab '' C)) = 2 ^ n) :
    Module.finrank (ZMod 2) (cliqueCode lab C) + n = Nat.card C := by
  have : Fintype C := Fintype.ofFinite C
  have h := LinearMap.finrank_range_add_finrank_ker (cliqueLabelMap lab C)
  rw [LinearMap.range_eq_top.2 cliqueLabelMap_surjective, finrank_top,
    finrank_additive_of_natCard hR, Module.finrank_finsupp_self, ← Nat.card_eq_fintype_card] at h
  rw [cliqueCode]
  omega

theorem cliqueLabelMap_mapDomain (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹)
    {a : S} (haC : ∀ x ∈ C, act a x ∈ C) (σ : Equiv.Perm C) (hσ : ∀ z, (σ z : V) = act a z)
    (f : C →₀ ZMod 2) :
    cliqueLabelMap lab C (Finsupp.mapDomain σ f) =
      MonoidHom.toAdditive (conjGen a (conj_mem_closure hlab haC)) (cliqueLabelMap lab C f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg, map_add]
  | single z c =>
    rw [Finsupp.mapDomain_single, cliqueLabelMap_single, cliqueLabelMap_single, ZMod.map_smul]
    congr 1
    apply Additive.toMul.injective
    apply Subtype.ext
    change lab (σ z) = a * lab z * a⁻¹
    rw [hσ, hlab]

theorem mapDomain_mem_cliqueCode (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹)
    {a : S} (haC : ∀ x ∈ C, act a x ∈ C) (σ : Equiv.Perm C) (hσ : ∀ z, (σ z : V) = act a z)
    {f : C →₀ ZMod 2} (hf : f ∈ cliqueCode lab C) :
    Finsupp.mapDomain σ f ∈ cliqueCode lab C := by
  rw [cliqueCode, LinearMap.mem_ker] at hf ⊢
  rw [cliqueLabelMap_mapDomain hlab haC σ hσ, hf, map_zero]

theorem support_mapDomain_perm (σ : Equiv.Perm C) (f : C →₀ ZMod 2) :
    Subtype.val '' ((Finsupp.mapDomain σ f).support : Set C) =
      (fun z : C => (σ z : V)) '' (f.support : Set C) := by
  classical
  rw [Finsupp.mapDomain_support_of_injective σ.injective, Finset.coe_image, Set.image_image]

theorem image_mem_cliqueBlocks (hlab : ∀ (a : S) (x : V), lab (act a x) = a * lab x * a⁻¹)
    {a : S} (haC : ∀ x ∈ C, act a x ∈ C) (σ : Equiv.Perm C) (hσ : ∀ z, (σ z : V) = act a z)
    {B : Set V} (hB : B ∈ cliqueBlocks lab C) : act a '' B ∈ cliqueBlocks lab C := by
  classical
  obtain ⟨f, hf, hf6, rfl⟩ := hB
  refine ⟨Finsupp.mapDomain σ f, mapDomain_mem_cliqueCode hlab haC σ hσ hf, ?_, ?_⟩
  · rw [Finsupp.mapDomain_support_of_injective σ.injective,
      Finset.card_image_of_injective _ σ.injective, hf6]
  · rw [support_mapDomain_perm, Set.image_image]
    exact Set.image_congr fun z _ => (hσ z).symm

end Basic

end CFSG.Monster.B.TwoA.Fischer
