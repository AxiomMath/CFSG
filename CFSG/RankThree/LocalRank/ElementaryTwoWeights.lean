module

public import Mathlib.Algebra.Module.StablyFree.Basic
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
public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
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
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.LocalRank

open scoped DirectSum

section SignWeights

variable {A : Type*} [CommGroup A] [Module (ZMod 2) (Additive A)]
  {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def signWeightSpace (ρ : Representation K A V)
    (χ : Module.Dual (ZMod 2) (Additive A)) : Submodule K V :=
  ⨅ a : A, Module.End.eigenspace (ρ a) ((-1 : K) ^ ZMod.val (χ (Additive.ofMul a)))

theorem mem_signWeightSpace (ρ : Representation K A V) (χ : Module.Dual (ZMod 2) (Additive A))
    (v : V) : v ∈ signWeightSpace ρ χ ↔
      ∀ a : A, ρ a v = (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • v := by
  simp only [signWeightSpace, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

omit [Module (ZMod 2) (Additive A)] in
theorem neg_one_pow_val_add (x y : ZMod 2) :
    (-1 : K) ^ ZMod.val (x + y) = (-1) ^ ZMod.val x * (-1) ^ ZMod.val y := by
  rw [ZMod.val_add, ← neg_one_pow_eq_pow_mod_two, pow_add]

omit [Module (ZMod 2) (Additive A)] in
theorem neg_one_pow_val_mul_self (x : ZMod 2) : (-1 : K) ^ ZMod.val x * (-1) ^ ZMod.val x = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

omit [Module (ZMod 2) (Additive A)] in
theorem neg_one_pow_val_eq_one_iff (hK : (2 : K) ≠ 0) (x : ZMod 2) :
    (-1 : K) ^ ZMod.val x = 1 ↔ x = 0 := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) x with rfl | rfl
  · simp
  · have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
    rw [h1, pow_one]
    constructor
    · intro h
      exfalso
      apply hK
      calc (2 : K) = 1 - (-1) := by ring
        _ = 0 := by rw [h, sub_self]
    · intro h
      exact absurd h (by decide)

theorem dual_apply_eq_one {χ : Module.Dual (ZMod 2) (Additive A)} {x : Additive A}
    (hx : χ x ≠ 0) : χ x = 1 := by
  rcases (by decide : ∀ y : ZMod 2, y = 0 ∨ y = 1) (χ x) with h | h
  · exact absurd h hx
  · exact h

theorem exists_dual_apply_eq_one {x : Additive A} (hx : x ≠ 0) :
    ∃ χ : Module.Dual (ZMod 2) (Additive A), χ x = 1 := by
  by_contra h
  push Not at h
  apply hx
  rw [← Module.forall_dual_apply_eq_zero_iff (ZMod 2) x]
  intro φ
  by_contra hφ
  exact h φ (dual_apply_eq_one hφ)

omit [CommGroup A] [Module (ZMod 2) (Additive A)] in
theorem zmod_two_add_self (y : ZMod 2) : y + y = 0 := by
  revert y
  decide

@[expose] def dualTranslate (χ₀ : Module.Dual (ZMod 2) (Additive A)) :
    Module.Dual (ZMod 2) (Additive A) ≃ Module.Dual (ZMod 2) (Additive A) where
  toFun χ := χ₀ + χ
  invFun χ := χ₀ + χ
  left_inv χ := by
    ext x
    simp only [LinearMap.add_apply, ← add_assoc, zmod_two_add_self, zero_add]
  right_inv χ := by
    ext x
    simp only [LinearMap.add_apply, ← add_assoc, zmod_two_add_self, zero_add]

variable [Fintype A]

theorem natCast_card_ne_zero_of_two_module (hK : (2 : K) ≠ 0) : (Fintype.card A : K) ≠ 0 := by
  have h : Nat.card (Additive A) = Nat.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive A) :=
    Module.natCard_eq_pow_finrank
  rw [Nat.card_congr Additive.toMul, Nat.card_zmod, Nat.card_eq_fintype_card] at h
  rw [h, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_ne_zero _ hK

theorem sum_neg_one_pow_dual_eq_zero (hK : (2 : K) ≠ 0)
    {φ : Module.Dual (ZMod 2) (Additive A)} (hφ : φ ≠ 0) :
    ∑ a : A, (-1 : K) ^ ZMod.val (φ (Additive.ofMul a)) = 0 := by
  obtain ⟨x, hx⟩ : ∃ x : Additive A, φ x ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ (LinearMap.ext h)
  have hx1 := dual_apply_eq_one hx
  set S := ∑ a : A, (-1 : K) ^ ZMod.val (φ (Additive.ofMul a)) with hSdef
  have hS : S = -S := by
    calc S = ∑ a : A, (-1 : K) ^ ZMod.val (φ (Additive.ofMul (Additive.toMul x * a))) :=
          (Equiv.sum_comp (Equiv.mulLeft (Additive.toMul x)) _).symm
      _ = ∑ a : A, -((-1 : K) ^ ZMod.val (φ (Additive.ofMul a))) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [ofMul_mul, ofMul_toMul, map_add, hx1, neg_one_pow_val_add]
          have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
          rw [h1, pow_one, neg_one_mul]
      _ = -S := Finset.sum_neg_distrib _
  have h2S : (2 : K) * S = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hS]
    exact add_neg_cancel S
  exact (mul_eq_zero.mp h2S).resolve_left hK

variable [Fintype (Module.Dual (ZMod 2) (Additive A))]

omit [Fintype A] in
theorem sum_dual_neg_one_pow_eq_zero (hK : (2 : K) ≠ 0) {a : A} (ha : a ≠ 1) :
    ∑ χ : Module.Dual (ZMod 2) (Additive A), (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) = 0 := by
  obtain ⟨χ₀, hχ₀⟩ := exists_dual_apply_eq_one (A := A) (x := Additive.ofMul a)
    (fun h => ha (by simpa using h))
  set S := ∑ χ : Module.Dual (ZMod 2) (Additive A), (-1 : K) ^ ZMod.val (χ (Additive.ofMul a))
    with hSdef
  have hS : S = -S := by
    calc S = ∑ χ : Module.Dual (ZMod 2) (Additive A),
          (-1 : K) ^ ZMod.val ((χ₀ + χ) (Additive.ofMul a)) :=
          (Equiv.sum_comp (dualTranslate χ₀) _).symm
      _ = ∑ χ : Module.Dual (ZMod 2) (Additive A),
            -((-1 : K) ^ ZMod.val (χ (Additive.ofMul a))) := by
          refine Finset.sum_congr rfl fun χ _ => ?_
          rw [LinearMap.add_apply, hχ₀, neg_one_pow_val_add]
          have h1 : ZMod.val (1 : ZMod 2) = 1 := rfl
          rw [h1, pow_one, neg_one_mul]
      _ = -S := Finset.sum_neg_distrib _
  have h2S : (2 : K) * S = 0 := by
    rw [two_mul]
    nth_rewrite 2 [hS]
    exact add_neg_cancel S
  exact (mul_eq_zero.mp h2S).resolve_left hK

omit [Fintype A] [Fintype (Module.Dual (ZMod 2) (Additive A))] in
theorem neg_one_pow_val_ofMul_inv (χ : Module.Dual (ZMod 2) (Additive A)) (b : A) :
    (-1 : K) ^ ZMod.val (χ (Additive.ofMul b⁻¹)) = (-1 : K) ^ ZMod.val (χ (Additive.ofMul b)) := by
  have h : χ (Additive.ofMul b⁻¹) + χ (Additive.ofMul b) = 0 := by
    rw [← map_add, ← ofMul_mul, inv_mul_cancel, ofMul_one, map_zero]
  have h' : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
  rw [h' _ _ h]

variable (ρ : Representation K A V)

noncomputable def signProjection (χ : Module.Dual (ZMod 2) (Additive A)) : V →ₗ[K] V :=
  (Fintype.card A : K)⁻¹ • ∑ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • ρ a

omit [Fintype (Module.Dual (ZMod 2) (Additive A))] in
theorem signProjection_apply (χ : Module.Dual (ZMod 2) (Additive A)) (v : V) :
    signProjection ρ χ v = (Fintype.card A : K)⁻¹ •
      ∑ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • ρ a v := by
  simp only [signProjection, LinearMap.smul_apply, LinearMap.sum_apply]

omit [Fintype (Module.Dual (ZMod 2) (Additive A))] in
theorem signProjection_mem (χ : Module.Dual (ZMod 2) (Additive A)) (v : V) :
    signProjection ρ χ v ∈ signWeightSpace ρ χ := by
  rw [mem_signWeightSpace]
  intro b
  have key : ∑ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • ρ b (ρ a v) =
      (-1 : K) ^ ZMod.val (χ (Additive.ofMul b)) •
        ∑ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • ρ a v := by
    calc ∑ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • ρ b (ρ a v) =
          ∑ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul (b⁻¹ * (b * a)))) • ρ (b * a) v := by
          refine Finset.sum_congr rfl fun a _ => ?_
          rw [inv_mul_cancel_left, map_mul, Module.End.mul_apply]
      _ = ∑ c : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul (b⁻¹ * c))) • ρ c v :=
          Equiv.sum_comp (Equiv.mulLeft b)
            (fun c => (-1 : K) ^ ZMod.val (χ (Additive.ofMul (b⁻¹ * c))) • ρ c v)
      _ = ∑ c : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul b)) •
            ((-1 : K) ^ ZMod.val (χ (Additive.ofMul c)) • ρ c v) := by
          refine Finset.sum_congr rfl fun c _ => ?_
          rw [ofMul_mul, map_add, neg_one_pow_val_add, neg_one_pow_val_ofMul_inv, mul_smul]
      _ = _ := (Finset.smul_sum ..).symm
  rw [signProjection_apply, map_smul, map_sum]
  simp only [map_smul]
  rw [key, smul_comm]

omit [Fintype (Module.Dual (ZMod 2) (Additive A))] in
theorem signProjection_of_mem_self (hK : (2 : K) ≠ 0) {χ : Module.Dual (ZMod 2) (Additive A)}
    {v : V} (hv : v ∈ signWeightSpace ρ χ) : signProjection ρ χ v = v := by
  rw [mem_signWeightSpace] at hv
  rw [signProjection_apply]
  have h : ∀ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • ρ a v = v := by
    intro a
    rw [hv a, smul_smul, neg_one_pow_val_mul_self, one_smul]
  simp only [h, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul K, smul_smul,
    inv_mul_cancel₀ (natCast_card_ne_zero_of_two_module hK), one_smul]

omit [Fintype (Module.Dual (ZMod 2) (Additive A))] in
theorem signProjection_of_mem_ne (hK : (2 : K) ≠ 0) {χ ψ : Module.Dual (ZMod 2) (Additive A)}
    (hψχ : ψ ≠ χ) {v : V} (hv : v ∈ signWeightSpace ρ ψ) : signProjection ρ χ v = 0 := by
  rw [mem_signWeightSpace] at hv
  rw [signProjection_apply]
  have hne : χ + ψ ≠ 0 := by
    intro h0
    apply hψχ
    ext x
    have hx := LinearMap.congr_fun h0 x
    rw [LinearMap.add_apply, LinearMap.zero_apply] at hx
    have h' : ∀ y z : ZMod 2, y + z = 0 → z = y := by decide
    exact h' _ _ hx
  have h : ∀ a : A, (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) • ρ a v =
      (-1 : K) ^ ZMod.val ((χ + ψ) (Additive.ofMul a)) • v := by
    intro a
    rw [hv a, smul_smul, LinearMap.add_apply, neg_one_pow_val_add]
  simp only [h]
  rw [← Finset.sum_smul, sum_neg_one_pow_dual_eq_zero hK hne, zero_smul, smul_zero]

theorem sum_signProjection (hK : (2 : K) ≠ 0) (v : V) :
    ∑ χ : Module.Dual (ZMod 2) (Additive A), signProjection ρ χ v =
      ((Fintype.card A : K)⁻¹ * Fintype.card (Module.Dual (ZMod 2) (Additive A))) • v := by
  simp only [signProjection_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  simp only [← Finset.sum_smul]
  rw [Finset.sum_eq_single (1 : A)]
  · simp only [ofMul_one, map_zero, ZMod.val_zero, pow_zero, Finset.sum_const, Finset.card_univ,
      map_one, Module.End.one_apply]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, smul_eq_mul, mul_one]
  · intro a _ ha
    rw [sum_dual_neg_one_pow_eq_zero hK ha, zero_smul]
  · intro h
    exact absurd (Finset.mem_univ 1) h

end SignWeights

section Decomposition

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {A : Type*} [CommGroup A] [Module (ZMod 2) (Additive A)]
  {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem natCast_card_dual_ne_zero [Fintype (Module.Dual (ZMod 2) (Additive A))]
    (hK : (2 : K) ≠ 0) : (Fintype.card (Module.Dual (ZMod 2) (Additive A)) : K) ≠ 0 := by
  have : Module.Finite (ZMod 2) (Module.Dual (ZMod 2) (Additive A)) := Module.Finite.of_finite
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) (Additive A))
  rw [Nat.card_zmod, Nat.card_eq_fintype_card] at h
  rw [h, Nat.cast_pow, Nat.cast_ofNat]
  exact pow_ne_zero _ hK

variable [Fintype A] [Fintype (Module.Dual (ZMod 2) (Additive A))] (ρ : Representation K A V)

theorem iSup_signWeightSpace_eq_top (hK : (2 : K) ≠ 0) : ⨆ χ, signWeightSpace ρ χ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h := sum_signProjection ρ hK v
  have hc : (Fintype.card A : K)⁻¹ * Fintype.card (Module.Dual (ZMod 2) (Additive A)) ≠ 0 :=
    mul_ne_zero (inv_ne_zero (natCast_card_ne_zero_of_two_module hK)) (natCast_card_dual_ne_zero hK)
  have hv : v = ((Fintype.card A : K)⁻¹ * Fintype.card (Module.Dual (ZMod 2) (Additive A)))⁻¹ •
      ∑ χ, signProjection ρ χ v := by
    rw [h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [hv]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun χ _ => ?_)
  exact Submodule.mem_iSup_of_mem χ (signProjection_mem ρ χ v)

omit [Fintype (Module.Dual (ZMod 2) (Additive A))] in
theorem iSupIndep_signWeightSpace (hK : (2 : K) ≠ 0) : iSupIndep (signWeightSpace ρ) := by
  intro χ
  rw [Submodule.disjoint_def]
  intro v hvχ hvS
  have h1 : signProjection ρ χ v = v := signProjection_of_mem_self ρ hK hvχ
  have h2 : (⨆ (ψ) (_ : ψ ≠ χ), signWeightSpace ρ ψ) ≤ LinearMap.ker (signProjection ρ χ) := by
    refine iSup₂_le fun ψ hψ => ?_
    intro w hw
    exact signProjection_of_mem_ne ρ hK hψ hw
  rw [← h1]
  exact h2 hvS

theorem rep_eq_one_iff_signWeightSpace (hK : (2 : K) ≠ 0) (a : A) :
    ρ a = 1 ↔ ∀ χ : Module.Dual (ZMod 2) (Additive A),
      signWeightSpace ρ χ ≠ ⊥ → χ (Additive.ofMul a) = 0 := by
  constructor
  · intro ha χ hχ
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
    have h := (mem_signWeightSpace ρ χ v).mp hv a
    rw [ha, Module.End.one_apply] at h
    have hs : (-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) = 1 := by
      by_contra hne
      apply hv0
      have h0 : ((-1 : K) ^ ZMod.val (χ (Additive.ofMul a)) - 1) • v = 0 := by
        rw [sub_smul, ← h, one_smul, sub_self]
      exact (smul_eq_zero.mp h0).resolve_left (sub_ne_zero.mpr hne)
    exact (neg_one_pow_val_eq_one_iff hK _).mp hs
  · intro h
    apply LinearMap.ext
    intro v
    have hv : v ∈ ⨆ χ, signWeightSpace ρ χ := by
      rw [iSup_signWeightSpace_eq_top ρ hK]
      exact Submodule.mem_top
    rw [Module.End.one_apply]
    refine Submodule.iSup_induction (signWeightSpace ρ) (motive := fun w => ρ a w = w) hv
      (fun χ w hw => ?_) (map_zero _) (fun x y hx hy => by rw [map_add, hx, hy])
    by_cases hχ : signWeightSpace ρ χ = ⊥
    · have hw0 : w = 0 := by
        rw [hχ] at hw
        exact (Submodule.mem_bot K).mp hw
      rw [hw0, map_zero]
    · rw [(mem_signWeightSpace ρ χ w).mp hw a, h χ hχ, ZMod.val_zero, pow_zero, one_smul]

theorem injective_iff_span_signWeightSpace (hK : (2 : K) ≠ 0) :
    Function.Injective ρ ↔
      Submodule.span (ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥} = ⊤ := by
  rw [injective_iff_map_eq_one]
  constructor
  · intro hinj
    have : FiniteDimensional (ZMod 2)
        (Submodule.span (ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥}) := Module.Finite.of_finite
    have hcoann : (Submodule.span (ZMod 2)
        {χ | signWeightSpace ρ χ ≠ ⊥}).dualCoannihilator = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rw [Submodule.mem_dualCoannihilator] at hx
      have h1 : ρ (Additive.toMul x) = 1 :=
        (rep_eq_one_iff_signWeightSpace ρ hK _).mpr fun χ hχ => by
          simpa using hx χ (Submodule.subset_span hχ)
      have h2 := hinj _ h1
      rw [Submodule.mem_bot]
      simpa using congrArg Additive.ofMul h2
    have h := Subspace.dualCoannihilator_dualAnnihilator_eq
      (W := Submodule.span (ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥})
    rw [hcoann, Submodule.dualAnnihilator_bot] at h
    exact h.symm
  · intro hspan a ha
    have h1 := (rep_eq_one_iff_signWeightSpace ρ hK a).mp ha
    have h2 : ∀ φ ∈ Submodule.span (ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥},
        φ (Additive.ofMul a) = 0 := by
      intro φ hφ
      induction hφ using Submodule.span_induction with
      | mem χ hχ => exact h1 χ hχ
      | zero => rfl
      | add φ ψ _ _ hφ hψ => rw [LinearMap.add_apply, hφ, hψ, add_zero]
      | smul c φ _ hφ => rw [LinearMap.smul_apply, hφ, smul_zero]
    rw [hspan] at h2
    have h3 : Additive.ofMul a = 0 :=
      (Module.forall_dual_apply_eq_zero_iff (ZMod 2) _).mp fun φ => h2 φ Submodule.mem_top
    simpa using h3

theorem finrank_le_of_injective_of_two_module (hK : (2 : K) ≠ 0) [FiniteDimensional K V]
    (hinj : Function.Injective ρ) :
    Module.finrank (ZMod 2) (Additive A) ≤ Module.finrank K V := by
  classical
  have hspan := (injective_iff_span_signWeightSpace ρ hK).mp hinj
  have h1 : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) (Additive A)) ≤
      {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset.card := by
    have h := finrank_span_le_card (R := ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥}
    rwa [hspan, finrank_top] at h
  have h2 : Fintype.card {χ // signWeightSpace ρ χ ≠ ⊥} ≤ Module.finrank K V :=
    (iSupIndep_signWeightSpace ρ hK).subtype_ne_bot_le_finrank
  rw [Subspace.dual_finrank_eq] at h1
  calc Module.finrank (ZMod 2) (Additive A) ≤ {χ | signWeightSpace ρ χ ≠ ⊥}.toFinset.card := h1
    _ = Fintype.card {χ // signWeightSpace ρ χ ≠ ⊥} := by
        rw [Set.toFinset_card]
        exact Fintype.card_congr (Equiv.refl _)
    _ ≤ Module.finrank K V := h2

theorem exists_invariant_line_of_two_module (hK : (2 : K) ≠ 0) [Nontrivial V] :
    ∃ L : Submodule K V, Module.finrank K L = 1 ∧ ∀ a : A, ∀ v ∈ L, ρ a v ∈ L := by
  obtain ⟨χ, hχ⟩ : ∃ χ, signWeightSpace ρ χ ≠ ⊥ := by
    by_contra h
    push Not at h
    have htop := iSup_signWeightSpace_eq_top ρ hK
    simp only [h, iSup_bot] at htop
    exact bot_ne_top htop
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hχ
  refine ⟨K ∙ v, finrank_span_singleton hv0, fun a w hw => ?_⟩
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [map_smul, (mem_signWeightSpace ρ χ v).mp hv a, smul_smul]
  exact Submodule.mem_span_singleton.mpr ⟨_, rfl⟩

end Decomposition

open _root_.Classical in
theorem elementary_two_weight_decomposition {A : Type*} [CommGroup A] [Finite A]
    [Module (ZMod 2) (Additive A)] {K : Type*} [Field K] (hK : (2 : K) ≠ 0)
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K A V) :
    Function.Bijective (DirectSum.coeLinearMap (signWeightSpace ρ)) ∧
    (∀ a : A, ρ a = 1 ↔ ∀ χ : Module.Dual (ZMod 2) (Additive A),
      signWeightSpace ρ χ ≠ ⊥ → χ (Additive.ofMul a) = 0) ∧
    (Function.Injective ρ ↔ Submodule.span (ZMod 2) {χ | signWeightSpace ρ χ ≠ ⊥} = ⊤) ∧
    (Function.Injective ρ → Module.finrank (ZMod 2) (Additive A) ≤ Module.finrank K V) ∧
    (Nontrivial V →
      ∃ L : Submodule K V, Module.finrank K L = 1 ∧ ∀ a : A, ∀ v ∈ L, ρ a v ∈ L) := by
  let := Fintype.ofFinite A
  have : Finite (Module.Dual (ZMod 2) (Additive A)) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) (Additive A) => (f : Additive A → ZMod 2))
      DFunLike.coe_injective
  let := Fintype.ofFinite (Module.Dual (ZMod 2) (Additive A))
  exact ⟨DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      (dec_ι := fun a b => Classical.propDecidable (a = b))
      (iSupIndep_signWeightSpace ρ hK) (iSup_signWeightSpace_eq_top ρ hK),
    rep_eq_one_iff_signWeightSpace ρ hK, injective_iff_span_signWeightSpace ρ hK,
    finrank_le_of_injective_of_two_module ρ hK,
    fun _ => exists_invariant_line_of_two_module ρ hK⟩

end CFSG.RankThree.LocalRank
