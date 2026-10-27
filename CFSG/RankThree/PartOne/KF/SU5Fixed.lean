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
public import Mathlib.LinearAlgebra.Matrix.IsDiag
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Coalgebra.IsFrobenius
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
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
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartOne.KFSU5

open Matrix

section FixedVectors

variable {n : ℕ} {K : Type} [Field K]

theorem mulVec_apply_of_isDiag {M : Matrix (Fin n) (Fin n) K} (hM : M.IsDiag) (v : Fin n → K)
    (k : Fin n) : (M *ᵥ v) k = M k k * v k := by
  rw [← hM.diagonal_diag, Matrix.mulVec_diagonal]
  simp [Matrix.diag]

theorem single_mem_of_invariant (Ã : Subgroup (GL (Fin n) K))
    (hdiag : ∀ a ∈ Ã, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hdist : ∀ i j : Fin n, i ≠ j → ∃ a ∈ Ã,
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i ≠
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j)
    (W : Submodule K (Fin n → K))
    (hW : ∀ a ∈ Ã, ∀ v ∈ W, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ W)
    {v : Fin n → K} (hv : v ∈ W) (j : Fin n) : Pi.single j (v j) ∈ W := by
  classical
  have key : ∀ S : Finset (Fin n), j ∉ S → ∀ w ∈ W, ∃ w' ∈ W, w' j = w j ∧ ∀ k ∈ S, w' k = 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro _ w hw; exact ⟨w, hw, rfl, by simp⟩
    | insert i S hi ih =>
      intro hjS w hw
      have hji : j ≠ i := fun h => hjS (h ▸ Finset.mem_insert_self _ _)
      have hjS' : j ∉ S := fun h => hjS (Finset.mem_insert_of_mem h)
      obtain ⟨w₁, hw₁, hw₁j, hw₁S⟩ := ih hjS' w hw
      obtain ⟨a, ha, hne⟩ := hdist i j (Ne.symm hji)
      set c : K := ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j -
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i with hc
      have hc0 : c ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
      refine ⟨c⁻¹ • (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w₁ -
        (((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i) • w₁),
        W.smul_mem _ (W.sub_mem (hW a ha w₁ hw₁) (W.smul_mem _ hw₁)), ?_, ?_⟩
      · simp only [Pi.smul_apply, Pi.sub_apply, mulVec_apply_of_isDiag (hdiag a ha), smul_eq_mul,
          hw₁j]
        rw [hc]
        field_simp
      · intro k hk
        rcases Finset.mem_insert.mp hk with rfl | hk
        · simp [mulVec_apply_of_isDiag (hdiag a ha)]
        · simp [mulVec_apply_of_isDiag (hdiag a ha), hw₁S k hk]
  obtain ⟨w, hw, hwj, hwk⟩ := key (Finset.univ.erase j) (by simp) v hv
  have : w = Pi.single j (v j) := by
    funext k
    by_cases hk : k = j
    · subst hk; simp [hwj]
    · simp [hk, hwk k (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩)]
  rwa [← this]

@[expose] def fixSub (S : Subgroup (GL (Fin n) K)) : Submodule K (Fin n → K) where
  carrier := {v | ∀ s ∈ S, ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  add_mem' := fun {u v} hu hv s hs => by rw [Matrix.mulVec_add, hu s hs, hv s hs]
  zero_mem' := fun s _ => Matrix.mulVec_zero _
  smul_mem' := fun c v hv s hs => by rw [Matrix.mulVec_smul, hv s hs]

theorem mulVec_mem_fixSub {Ã S : Subgroup (GL (Fin n) K)}
    (hnorm : ∀ a ∈ Ã, ∀ s ∈ S, a * s * a⁻¹ ∈ S) {a : GL (Fin n) K} (ha : a ∈ Ã)
    {v : Fin n → K} (hv : v ∈ fixSub S) :
    ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ fixSub S := by
  intro s hs
  have h1 : a⁻¹ * s * a ∈ S := by simpa using hnorm a⁻¹ (Ã.inv_mem ha) s hs
  have h2 : s * a = a * (a⁻¹ * s * a) := by group
  have h3 : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((a⁻¹ * s * a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [← Units.val_mul, ← Units.val_mul, h2]
  rw [Matrix.mulVec_mulVec, h3, ← Matrix.mulVec_mulVec, hv _ h1]

theorem row_eq_of_fixes_single (σ : K →+* K) {s : GL (Fin n) K}
    (hunit : (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ *
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1) {j : Fin n}
    (hj : ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j (1 : K) =
      Pi.single j 1) (k : Fin n) :
    ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j k = if j = k then 1 else 0 := by
  have h2 : (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ *ᵥ Pi.single j (1 : K) =
      Pi.single j 1 := by
    calc _ = (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ *ᵥ
          (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single j (1 : K)) := by rw [hj]
      _ = ((((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ *
          ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) *ᵥ Pi.single j (1 : K) := by
        rw [Matrix.mulVec_mulVec]
      _ = Pi.single j 1 := by rw [hunit, Matrix.one_mulVec]
  have h3 := congrFun h2 k
  rw [Matrix.mulVec_single_one] at h3
  simp only [Matrix.col_apply, Matrix.transpose_apply, Matrix.map_apply] at h3
  apply σ.injective
  rw [h3, Pi.single_apply]
  by_cases hjk : j = k
  · simp [hjk]
  · simp [hjk, Ne.symm hjk]

theorem eq_bot_of_normalized_two_group [Finite K] (hK2 : 2 ∣ Nat.card K) (σ : K →+* K)
    (Ã S : Subgroup (GL (Fin n) K))
    (hdiag : ∀ a ∈ Ã, ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).IsDiag)
    (hdist : ∀ i j : Fin n, i ≠ j → ∃ a ∈ Ã,
      ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i ≠
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) j j)
    (hunit : ∀ s ∈ S, (((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).map σ)ᵀ *
      ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1)
    (hS2 : IsPGroup 2 S) (hnorm : ∀ a ∈ Ã, ∀ s ∈ S, a * s * a⁻¹ ∈ S) : S = ⊥ := by
  classical
  have hA : ∀ v ∈ fixSub S, ∀ j, v j ≠ 0 → Pi.single j (1 : K) ∈ fixSub S := by
    intro v hv j hj
    have h1 := single_mem_of_invariant Ã hdiag hdist (fixSub S)
      (fun a ha v hv => mulVec_mem_fixSub hnorm ha hv) hv j
    have h2 := (fixSub S).smul_mem (v j)⁻¹ h1
    convert h2 using 1
    funext k
    by_cases hk : k = j
    · subst hk; simp [inv_mul_cancel₀ hj]
    · simp [hk]
  have hI : ∀ j : Fin n, Pi.single j (1 : K) ∈ fixSub S := by
    by_contra hcon
    push Not at hcon
    obtain ⟨j₀, hj₀⟩ := hcon
    let U : Submodule K (Fin n → K) :=
      { carrier := {v | ∀ j, Pi.single j (1 : K) ∈ fixSub S → v j = 0}
        add_mem' := fun {u v} hu hv j hj => by simp [hu j hj, hv j hj]
        zero_mem' := fun j _ => rfl
        smul_mem' := fun c v hv j hj => by simp [hv j hj] }
    have hUstable : ∀ s ∈ S, ∀ v ∈ U,
        ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v ∈ U := by
      intro s hs v hv j hj
      have hrow := fun k => row_eq_of_fixes_single σ (hunit s hs) (hj s hs) k
      have h1 := hv j hj
      rw [Matrix.mulVec, dotProduct]
      simp [hrow, h1]
    let P : SubMulAction ↥S (Fin n → K) :=
      { carrier := (U : Set (Fin n → K))
        smul_mem' := fun s v hv => hUstable s s.2 v hv }
    have hUne : U ≠ ⊥ := by
      rw [Submodule.ne_bot_iff]
      refine ⟨Pi.single j₀ 1, fun j hj => ?_, ?_⟩
      · have : j ≠ j₀ := fun h => hj₀ (h ▸ hj)
        simp [this]
      · intro h
        have := congrFun h j₀
        simp at this
    have hdvd : 2 ∣ Nat.card P := by
      have h1 : Nat.card P = Nat.card U := Nat.card_congr (Equiv.refl _)
      rw [h1, Module.natCard_eq_pow_finrank (K := K)]
      exact dvd_pow hK2 (Nat.pos_iff_ne_zero.mp (Submodule.one_le_finrank_iff.mpr hUne))
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Finite P := inferInstance
    have h0 : (⟨0, U.zero_mem⟩ : P) ∈ MulAction.fixedPoints ↥S P := by
      rw [MulAction.mem_fixedPoints]
      intro s
      apply Subtype.ext
      show ((s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ (0 : Fin n → K) = 0
      exact Matrix.mulVec_zero _
    obtain ⟨b, hb, hb0⟩ := hS2.exists_fixed_point_of_prime_dvd_card_of_fixed_point P hdvd h0
    have hbfix : (b : Fin n → K) ∈ fixSub S := by
      intro s hs
      have := (MulAction.mem_fixedPoints.mp hb) ⟨s, hs⟩
      exact congrArg Subtype.val this
    have hbne : (b : Fin n → K) ≠ 0 := fun h => hb0 (Subtype.ext h.symm)
    obtain ⟨j, hj⟩ : ∃ j, (b : Fin n → K) j ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hbne (funext hcon)
    exact hj (b.2 j (hA _ hbfix j hj))
  rw [eq_bot_iff]
  intro s hs
  rw [Subgroup.mem_bot]
  apply Units.ext
  apply Matrix.ext
  intro k j
  have h1 := hI j s hs
  have h2 := congrFun h1 k
  rw [Matrix.mulVec_single_one] at h2
  simpa [Matrix.one_apply, Pi.single_apply] using h2

end FixedVectors

end CFSG.RankThree.PartOne.KFSU5
