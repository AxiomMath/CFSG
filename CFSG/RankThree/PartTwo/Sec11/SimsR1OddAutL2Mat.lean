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
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.PiTensorProduct
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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut

open Matrix
open scoped commutatorElement

section Centralizer

variable {F : Type*} [Field F]

theorem exists_eq_add_smul_of_commute {A B : Matrix (Fin 2) (Fin 2) F}
    (hA : ∀ a : F, A ≠ a • (1 : Matrix (Fin 2) (Fin 2) F)) (hAB : A * B = B * A) :
    ∃ α β : F, B = α • (1 : Matrix (Fin 2) (Fin 2) F) + β • A := by
  have h00 := congrFun (congrFun hAB 0) 0
  have h01 := congrFun (congrFun hAB 0) 1
  have h10 := congrFun (congrFun hAB 1) 0
  have h11 := congrFun (congrFun hAB 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  by_cases hb : A 0 1 = 0
  · by_cases hc : A 1 0 = 0
    · have hd : A 0 0 - A 1 1 ≠ 0 := by
        intro h
        apply hA (A 0 0)
        ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc]
        linear_combination -h
      refine ⟨B 0 0 - (B 0 0 - B 1 1) / (A 0 0 - A 1 1) * A 0 0,
        (B 0 0 - B 1 1) / (A 0 0 - A 1 1), ?_⟩
      have hB01 : B 0 1 = 0 := by
        rw [hb] at h01
        have : B 0 1 * (A 0 0 - A 1 1) = 0 := by linear_combination h01
        simpa [hd] using this
      have hB10 : B 1 0 = 0 := by
        rw [hc] at h10
        have : B 1 0 * (A 0 0 - A 1 1) = 0 := by linear_combination -h10
        simpa [hd] using this
      ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hc, hB01, hB10] <;> field_simp <;> ring
    · have hf : B 0 1 = 0 := by
        rw [hb] at h00
        have : B 0 1 * A 1 0 = 0 := by linear_combination -h00
        simpa [hc] using this
      refine ⟨B 0 0 - B 1 0 / A 1 0 * A 0 0, B 1 0 / A 1 0, ?_⟩
      ext i j; fin_cases i <;> fin_cases j <;> simp [hb, hf] <;> field_simp
      linear_combination -h10
  · refine ⟨B 0 0 - B 0 1 / A 0 1 * A 0 0, B 0 1 / A 0 1, ?_⟩
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> field_simp
    · linear_combination h00
    · linear_combination h01

theorem commute_of_commute_of_nonscalar {A B C : Matrix (Fin 2) (Fin 2) F}
    (hA : ∀ a : F, A ≠ a • (1 : Matrix (Fin 2) (Fin 2) F)) (hB : A * B = B * A)
    (hC : A * C = C * A) : B * C = C * B := by
  obtain ⟨α, β, rfl⟩ := exists_eq_add_smul_of_commute hA hB
  obtain ⟨α', β', rfl⟩ := exists_eq_add_smul_of_commute hA hC
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one]
  module

theorem coe_scalar_eq_smul_one (u : Fˣ) :
    ((GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = (u : F) • (1 : Matrix (Fin 2) (Fin 2) F) := by
  rw [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem coe_mul_scalar (g : GL (Fin 2) F) (u : Fˣ) :
    ((g * GeneralLinearGroup.scalar (Fin 2) u : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = (u : F) • (g : Matrix (Fin 2) (Fin 2) F) := by
  rw [Units.val_mul, coe_scalar_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]

theorem nonscalar_of_ne_one {t : GL (Fin 2) F} (ht : ProjGenLinGroup.mk t ≠ 1) (a : F) :
    (t : Matrix (Fin 2) (Fin 2) F) ≠ a • (1 : Matrix (Fin 2) (Fin 2) F) := by
  intro h
  have ha : a ≠ 0 := by
    rintro rfl
    have := t.ne_zero
    exact this (by simpa using h)
  apply ht
  have : t = GeneralLinearGroup.scalar (Fin 2) (Units.mk0 a ha) := by
    apply Units.ext
    rw [coe_scalar_eq_smul_one, Units.val_mk0]
    exact h
  rw [this, ProjGenLinGroup.mk_scalar]

end Centralizer

section NormScalar

variable {F : Type*} [Field F]

@[expose] def NormScalar (T : Matrix (Fin 2) (Fin 2) F) (g : GL (Fin 2) F) (a : F) : Prop :=
  (g : Matrix (Fin 2) (Fin 2) F) * T = a • (T * (g : Matrix (Fin 2) (Fin 2) F))

theorem NormScalar.mul {T : Matrix (Fin 2) (Fin 2) F} {g g' : GL (Fin 2) F} {a b : F}
    (h : NormScalar T g a) (h' : NormScalar T g' b) : NormScalar T (g * g') (a * b) := by
  unfold NormScalar at *
  rw [Units.val_mul]
  calc (g : Matrix (Fin 2) (Fin 2) F) * g' * T
      = (g : Matrix (Fin 2) (Fin 2) F) * (g' * T) := Matrix.mul_assoc _ _ _
    _ = b • ((g * T) * g') := by rw [h', Matrix.mul_smul, Matrix.mul_assoc]
    _ = b • (a • ((T * g) * g')) := by rw [h, Matrix.smul_mul]
    _ = (a * b) • (T * (g * g')) := by rw [smul_smul, mul_comm b a, Matrix.mul_assoc]

theorem NormScalar.inv {T : Matrix (Fin 2) (Fin 2) F} {g : GL (Fin 2) F} {a : F}
    (h : NormScalar T g a) (ha : a ≠ 0) : NormScalar T g⁻¹ a⁻¹ := by
  unfold NormScalar at *
  have hg : ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hg' : (g : Matrix (Fin 2) (Fin 2) F) *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have h1 : T * ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
      = a • (((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * T) := by
    have := congrArg (fun N => ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * N *
      ((g⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) h
    simp only [Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, hg] at this
    simp only [Matrix.mul_assoc, hg', Matrix.mul_one, Matrix.one_mul] at this
    exact this
  rw [h1, smul_smul, inv_mul_cancel₀ ha, one_smul]

theorem NormScalar.one_iff {T : Matrix (Fin 2) (Fin 2) F} {g : GL (Fin 2) F} :
    NormScalar T g 1 ↔
      (g : Matrix (Fin 2) (Fin 2) F) * T = T * (g : Matrix (Fin 2) (Fin 2) F) := by
  unfold NormScalar
  rw [one_smul]

theorem NormScalar.commutator {T : Matrix (Fin 2) (Fin 2) F} {g g' : GL (Fin 2) F} {a b : F}
    (h : NormScalar T g a) (h' : NormScalar T g' b) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((g * g' * g⁻¹ * g'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * T =
      T * ((g * g' * g⁻¹ * g'⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) := by
  rw [← NormScalar.one_iff]
  have := ((h.mul h').mul (h.inv ha)).mul (h'.inv hb)
  have e : a * b * a⁻¹ * b⁻¹ = 1 := by field_simp
  rwa [e] at this

theorem exists_normScalar_of_commute {g t : GL (Fin 2) F}
    (h : ProjGenLinGroup.mk g * ProjGenLinGroup.mk t =
      ProjGenLinGroup.mk t * ProjGenLinGroup.mk g) :
    ∃ a : Fˣ, NormScalar (t : Matrix (Fin 2) (Fin 2) F) g (a : F) := by
  rw [← map_mul, ← map_mul, ProjGenLinGroup.mk_eq_mk_iff] at h
  obtain ⟨u, hu⟩ := h
  refine ⟨u⁻¹, ?_⟩
  have h1 := congrArg (fun N : GL (Fin 2) F => (N : Matrix (Fin 2) (Fin 2) F)) hu
  rw [coe_mul_scalar, Units.val_mul, Units.val_mul] at h1
  unfold NormScalar
  rw [← h1, smul_smul, Units.val_inv_eq_inv_val, inv_mul_cancel₀ u.ne_zero, one_smul]

end NormScalar

theorem isSolvable_of_commutator_le_comm {G : Type*} [Group G] (S K : Subgroup G)
    (hK : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) (hS : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ K) :
    Group.IsSolvable S := by
  refine ⟨⟨2, ?_⟩⟩
  rw [derivedSeries_succ, derivedSeries_one]
  have hle : commutator S ≤ K.subgroupOf S := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact hS a a.2 b b.2
  refine le_bot_iff.mp ((Subgroup.commutator_mono hle hle).trans (le_of_eq ?_))
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact Subtype.ext (hK y hy x hx)

variable {F : Type*} [Field F]

theorem isSolvable_of_le_centralizer_ne_one {τ : ProjGenLinGroup (Fin 2) F} (hτ : τ ≠ 1)
    {S : Subgroup (ProjGenLinGroup (Fin 2) F)} (hS : ∀ s ∈ S, s * τ = τ * s) :
    Group.IsSolvable S := by
  obtain ⟨t, rfl⟩ := ProjGenLinGroup.mk_surjective τ
  have hT := nonscalar_of_ne_one hτ
  set K : Subgroup (ProjGenLinGroup (Fin 2) F) :=
    (Subgroup.centralizer ({t} : Set (GL (Fin 2) F))).map ProjGenLinGroup.mk with hK
  refine isSolvable_of_commutator_le_comm S K ?_ ?_
  · rintro _ ⟨g, hg, rfl⟩ _ ⟨g', hg', rfl⟩
    have h1 : (t : Matrix (Fin 2) (Fin 2) F) * g = g * t := by
      rw [← Units.val_mul, ← Units.val_mul, Subgroup.mem_centralizer_iff.mp hg t rfl]
    have h2 : (t : Matrix (Fin 2) (Fin 2) F) * g' = g' * t := by
      rw [← Units.val_mul, ← Units.val_mul, Subgroup.mem_centralizer_iff.mp hg' t rfl]
    have h3 := commute_of_commute_of_nonscalar hT h1 h2
    rw [← map_mul, ← map_mul]
    congr 1
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact h3
  · intro s hs s' hs'
    obtain ⟨g, rfl⟩ := ProjGenLinGroup.mk_surjective s
    obtain ⟨g', rfl⟩ := ProjGenLinGroup.mk_surjective s'
    obtain ⟨a, ha⟩ := exists_normScalar_of_commute (hS _ hs)
    obtain ⟨b, hb⟩ := exists_normScalar_of_commute (hS _ hs')
    have hc := NormScalar.commutator ha hb a.ne_zero b.ne_zero
    refine ⟨g * g' * g⁻¹ * g'⁻¹, ?_, by simp [commutatorElement_def]⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hc.symm

end CFSG.RankThree.PartTwo.Sec11.SimsR1.OddAut
