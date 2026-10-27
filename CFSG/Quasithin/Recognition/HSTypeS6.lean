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
public import Mathlib.Tactic.Basify
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
public import Std.Tactic.BVDecide.Normalize.BitVec

public section

namespace CFSG.Quasithin.HSType

abbrev SpV := Fin 4 → ZMod 2

@[expose] def spForm (v w : SpV) : ZMod 2 := v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2

@[expose] def duadPt : Fin 6 → SpV :=
  ![![0, 1, 1, 0], ![1, 1, 1, 0], ![1, 0, 1, 0], ![0, 0, 1, 1], ![0, 0, 0, 1], ![0, 0, 0, 0]]

@[expose] def duadV (i j : Fin 6) : SpV := duadPt i + duadPt j

@[expose] def actS6 (σ : Equiv.Perm (Fin 6)) (v : SpV) : SpV :=
  v 0 • (duadPt (σ 0) + duadPt (σ 1)) + v 1 • (duadPt (σ 1) + duadPt (σ 2)) +
    v 2 • (duadPt (σ 3) + duadPt (σ 4)) + v 3 • (duadPt (σ 4) + duadPt (σ 5))

@[expose] def spE (k : Fin 4) : SpV := Pi.single k 1

theorem spForm_comm : ∀ v w : SpV, spForm v w = spForm w v := by decide

theorem spForm_add_right : ∀ u v w : SpV, spForm u (v + w) = spForm u v + spForm u w := by
  intro u v w
  simp only [spForm, Pi.add_apply]
  ring

theorem spForm_add_left (u v w : SpV) : spForm (u + v) w = spForm u w + spForm v w := by
  rw [spForm_comm, spForm_add_right, spForm_comm w u, spForm_comm w v]

theorem spForm_nondeg : ∀ v : SpV, (∀ k : Fin 4, spForm v (spE k) = 0) → v = 0 := by decide

theorem actS6_add : ∀ (σ : Equiv.Perm (Fin 6)) (v w : SpV),
    actS6 σ (v + w) = actS6 σ v + actS6 σ w := by
  intro σ v w
  funext k
  simp only [actS6, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem actS6_duad : ∀ (σ : Equiv.Perm (Fin 6)) (i j : Fin 6),
    actS6 σ (duadV i j) = duadV (σ i) (σ j) := by
  intro σ i j
  have key : ∀ i j : Fin 6, ∀ q : Fin 6 → ZMod 2, ∑ k, q k = 0 →
      duadV i j 0 * (q 0 + q 1) + duadV i j 1 * (q 1 + q 2) + duadV i j 2 * (q 3 + q 4) +
        duadV i j 3 * (q 4 + q 5) = q i + q j := by
    decide +kernel
  have h1 : ∑ k, duadPt (σ k) = ∑ k, duadPt k := Equiv.sum_comp σ duadPt
  have h2 : ∑ k, duadPt k = 0 := by decide
  funext m
  have hs := congrFun (h1.trans h2) m
  rw [Finset.sum_apply] at hs
  have h := key i j (fun k => duadPt (σ k) m) hs
  simp only [actS6, duadV, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
  exact h

theorem eq_sum_duads (v : SpV) : v = v 0 • duadV 0 1 + v 1 • duadV 1 2 +
    v 2 • duadV 3 4 + v 3 • duadV 4 5 := by
  have : ∀ v : SpV, v = v 0 • duadV 0 1 + v 1 • duadV 1 2 + v 2 • duadV 3 4 +
      v 3 • duadV 4 5 := by decide
  exact this v

theorem actS6_smul (σ : Equiv.Perm (Fin 6)) (c : ZMod 2) (v : SpV) :
    actS6 σ (c • v) = c • actS6 σ v := by
  funext k
  simp only [actS6, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem actS6_one (v : SpV) : actS6 1 v = v := by
  have : ∀ v : SpV, actS6 1 v = v := by decide
  exact this v

theorem actS6_mul (σ τ : Equiv.Perm (Fin 6)) (v : SpV) :
    actS6 (σ * τ) v = actS6 σ (actS6 τ v) := by
  conv_lhs => rw [eq_sum_duads v]
  conv_rhs => rw [eq_sum_duads v]
  simp only [actS6_add, actS6_smul, actS6_duad, Equiv.Perm.mul_apply]

theorem spForm_duad : ∀ i j k l : Fin 6,
    spForm (duadV i j) (duadV k l) =
      (if i = k then 1 else 0) + (if i = l then 1 else 0) + (if j = k then 1 else 0) +
        (if j = l then 1 else 0) := by
  decide

theorem spForm_actS6 (σ : Equiv.Perm (Fin 6)) (v w : SpV) :
    spForm (actS6 σ v) (actS6 σ w) = spForm v w := by
  have hd : ∀ i j k l : Fin 6,
      spForm (duadV (σ i) (σ j)) (duadV (σ k) (σ l)) = spForm (duadV i j) (duadV k l) := by
    intro i j k l
    simp only [spForm_duad, σ.injective.eq_iff]
  have hs : ∀ (c : ZMod 2) (x y : SpV), spForm (c • x) y = c * spForm x y := by
    intro c x y
    simp only [spForm, Pi.smul_apply, smul_eq_mul]
    ring
  have hs' : ∀ (c : ZMod 2) (x y : SpV), spForm x (c • y) = c * spForm x y := by
    intro c x y
    simp only [spForm, Pi.smul_apply, smul_eq_mul]
    ring
  rw [eq_sum_duads v, eq_sum_duads w]
  simp only [actS6_add, actS6_smul, actS6_duad, spForm_add_left, spForm_add_right, hs, hs',
    hd]

theorem actS6_eq_one : ∀ ρ : Equiv.Perm (Fin 6), (∀ k, actS6 ρ (spE k) = spE k) → ρ = 1 := by
  decide +kernel

theorem actS6_injective {σ τ : Equiv.Perm (Fin 6)} (h : ∀ v, actS6 σ v = actS6 τ v) :
    σ = τ := by
  have h1 : τ⁻¹ * σ = 1 := by
    refine actS6_eq_one _ fun k => ?_
    rw [actS6_mul, h, ← actS6_mul, inv_mul_cancel, actS6_one]
  calc σ = τ * (τ⁻¹ * σ) := by group
    _ = τ := by rw [h1, mul_one]

@[expose] def isSympBasis (t : SpV × SpV × SpV × SpV) : Bool :=
  decide (spForm t.1 t.2.1 = 1) && decide (spForm t.1 t.2.2.1 = 0) &&
    decide (spForm t.2.1 t.2.2.1 = 0) && decide (spForm t.2.2.1 t.2.2.2 = 1) &&
    decide (spForm t.1 t.2.2.2 = 0) && decide (spForm t.2.1 t.2.2.2 = 0)

@[expose] def countSympBases : ℕ := ∑ a : SpV, ∑ b : SpV, if spForm a b = 1 then ∑ c : SpV,
  if spForm a c = 0 ∧ spForm b c = 0 then ∑ d : SpV,
    (if spForm c d = 1 ∧ spForm a d = 0 ∧ spForm b d = 0 then 1 else 0) else 0 else 0

theorem countSympBases_eq : countSympBases = 720 := by decide +kernel

theorem card_sympBases :
    (Finset.univ.filter fun t : SpV × SpV × SpV × SpV => isSympBasis t = true).card = 720 := by
  rw [Finset.card_filter, ← countSympBases_eq, countSympBases]
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases hab : spForm a b = 1
  · simp only [hab, ↓reduceIte]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hc : spForm a c = 0 ∧ spForm b c = 0
    · simp only [hc, and_self, ↓reduceIte]
      refine Finset.sum_congr rfl fun d _ => ?_
      simp [isSympBasis, hab, hc.1, hc.2, and_assoc]
    · simp only [hc, ↓reduceIte]
      refine Finset.sum_eq_zero fun d _ => ?_
      simp only [isSympBasis, hab, Bool.and_eq_true, decide_eq_true_eq, ite_eq_right_iff]
      tauto
  · simp only [hab, ↓reduceIte]
    refine Finset.sum_eq_zero fun c _ => Finset.sum_eq_zero fun d _ => ?_
    simp [isSympBasis, hab]

@[expose] def basisImage (σ : Equiv.Perm (Fin 6)) : SpV × SpV × SpV × SpV :=
  (actS6 σ (spE 0), actS6 σ (spE 1), actS6 σ (spE 2), actS6 σ (spE 3))

theorem eq_sum_spE (v : SpV) : v = v 0 • spE 0 + v 1 • spE 1 + v 2 • spE 2 + v 3 • spE 3 := by
  have : ∀ v : SpV, v = v 0 • spE 0 + v 1 • spE 1 + v 2 • spE 2 + v 3 • spE 3 := by decide
  exact this v

theorem basisImage_injective : Function.Injective basisImage := by
  intro σ τ h
  simp only [basisImage, Prod.mk.injEq] at h
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine actS6_injective fun v => ?_
  rw [eq_sum_spE v]
  simp only [actS6_add, actS6_smul, h0, h1, h2, h3]

theorem exists_actS6_of_basis (a b c d : SpV) (hab : spForm a b = 1) (hcd : spForm c d = 1)
    (hac : spForm a c = 0) (had : spForm a d = 0) (hbc : spForm b c = 0)
    (hbd : spForm b d = 0) :
    ∃ σ : Equiv.Perm (Fin 6), actS6 σ (spE 0) = a ∧ actS6 σ (spE 1) = b ∧
      actS6 σ (spE 2) = c ∧ actS6 σ (spE 3) = d := by
  have hsub : Finset.univ.image basisImage ⊆
      Finset.univ.filter fun t : SpV × SpV × SpV × SpV => isSympBasis t = true := by
    intro t ht
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp ht
    have h01 : spForm (spE 0) (spE 1) = 1 := by decide
    have h23 : spForm (spE 2) (spE 3) = 1 := by decide
    have h02 : spForm (spE 0) (spE 2) = 0 := by decide
    have h03 : spForm (spE 0) (spE 3) = 0 := by decide
    have h12 : spForm (spE 1) (spE 2) = 0 := by decide
    have h13 : spForm (spE 1) (spE 3) = 0 := by decide
    simp [basisImage, isSympBasis, spForm_actS6, h01, h23, h02, h03, h12, h13]
  have hcard : (Finset.univ.image basisImage).card = 720 := by
    rw [Finset.card_image_of_injective _ basisImage_injective, Finset.card_univ,
      Fintype.card_perm, Fintype.card_fin]
    rfl
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard, card_sympBases])
  have hmem : (a, b, c, d) ∈ Finset.univ.image basisImage := by
    rw [heq]
    simp [isSympBasis, hab, hcd, hac, had, hbc, hbd]
  obtain ⟨σ, -, hσ⟩ := Finset.mem_image.mp hmem
  simp only [basisImage, Prod.mk.injEq] at hσ
  exact ⟨σ, hσ⟩

theorem exists_actS6_of_isometry (T : SpV → SpV) (hadd : ∀ v w, T (v + w) = T v + T w)
    (hform : ∀ v w, spForm (T v) (T w) = spForm v w) :
    ∃ σ : Equiv.Perm (Fin 6), ∀ v, T v = actS6 σ v := by
  have h01 : spForm (spE 0) (spE 1) = 1 := by decide
  have h23 : spForm (spE 2) (spE 3) = 1 := by decide
  have h02 : spForm (spE 0) (spE 2) = 0 := by decide
  have h03 : spForm (spE 0) (spE 3) = 0 := by decide
  have h12 : spForm (spE 1) (spE 2) = 0 := by decide
  have h13 : spForm (spE 1) (spE 3) = 0 := by decide
  obtain ⟨σ, h0, h1, h2, h3⟩ := exists_actS6_of_basis (T (spE 0)) (T (spE 1)) (T (spE 2))
    (T (spE 3)) (by rw [hform, h01]) (by rw [hform, h23]) (by rw [hform, h02])
    (by rw [hform, h03]) (by rw [hform, h12]) (by rw [hform, h13])
  refine ⟨σ, fun v => ?_⟩
  have hT0 : T 0 = 0 := by
    have := hadd 0 0
    rw [add_zero] at this
    simpa using this
  have hsmul : ∀ (c : ZMod 2) (x : SpV), T (c • x) = c • T x := by
    intro c x
    have hc : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
    rcases hc c with rfl | rfl
    · rw [zero_smul, zero_smul, hT0]
    · rw [one_smul, one_smul]
  rw [eq_sum_spE v, hadd, hadd, hadd, hsmul, hsmul, hsmul, hsmul, actS6_add, actS6_add, actS6_add,
    actS6_smul, actS6_smul, actS6_smul, actS6_smul, h0, h1, h2, h3]

end CFSG.Quasithin.HSType
