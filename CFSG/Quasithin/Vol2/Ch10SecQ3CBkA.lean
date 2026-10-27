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
public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
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

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

namespace C11AmS

open Matrix

section SL2

variable {F : Type*} [Field F] [CharP F 2]

theorem sq_eq_one_of_fix (A : SpecialLinearGroup (Fin 2) F) {v : Fin 2 → F} (hv : v ≠ 0)
    (hA : (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : A ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hdet0 : ((A : Matrix (Fin 2) (Fin 2) F) - 1).det = 0 := by
    refine (Matrix.exists_mulVec_eq_zero_iff).mp ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, hA, Matrix.one_mulVec, sub_self]
  have hdet1 : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet0 hdet1
  simp only [Matrix.sub_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), sub_zero] at hdet0
  have htr : (A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
    linear_combination hdet1 - hdet0 + h2
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two]
  · linear_combination (A : Matrix (Fin 2) (Fin 2) F) 0 0 * htr - hdet1 - h2
  · linear_combination (A : Matrix (Fin 2) (Fin 2) F) 0 1 * htr
  · linear_combination (A : Matrix (Fin 2) (Fin 2) F) 1 0 * htr
  · linear_combination (A : Matrix (Fin 2) (Fin 2) F) 1 1 * htr - hdet1 - h2

theorem sq_eq_one_of_pow (x : SpecialLinearGroup (Fin 2) F) {k : ℕ} (hx : x ^ 2 ^ k = 1) :
    x ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hM
  have hpow : M ^ 2 ^ k = 1 := by
    have := congrArg (fun y : SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) hx
    simpa [hM] using this
  have hN : (M - 1) ^ 2 ^ k = 0 := by
    rw [sub_pow_char_pow_of_commute (p := 2) (h := Commute.one_right M), hpow, one_pow, sub_self]
  have hdet : (M - 1).det = 0 := by
    have h := congrArg Matrix.det hN
    rw [Matrix.det_pow, Matrix.det_zero] at h
    exact pow_eq_zero_iff (pow_ne_zero _ two_ne_zero) |>.mp h
  obtain ⟨v, hv, hMv⟩ := (Matrix.exists_mulVec_eq_zero_iff).mpr hdet
  refine sq_eq_one_of_fix x hv ?_
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hMv
  exact hMv

theorem sq_eq_one_of_commute (A x : SpecialLinearGroup (Fin 2) F) (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hAx : A * x = x * A) : A ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set X : Matrix (Fin 2) (Fin 2) F := (x : Matrix (Fin 2) (Fin 2) F) with hX
  set Y : Matrix (Fin 2) (Fin 2) F := (A : Matrix (Fin 2) (Fin 2) F) with hY
  have hXX : X * X = 1 := by
    have := congrArg (fun y : SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) hx2
    simpa [hX, sq] using this
  have hYX : Y * X = X * Y := by
    have := congrArg (fun y : SpecialLinearGroup (Fin 2) F => (y : Matrix (Fin 2) (Fin 2) F)) hAx
    simpa [hX, hY] using this
  have hdY : Y 0 0 * Y 1 1 - Y 0 1 * Y 1 0 = 1 := by
    have := A.2
    rwa [Matrix.det_fin_two] at this
  have e00 := congrFun (congrFun hXX 0) 0
  have e01 := congrFun (congrFun hXX 0) 1
  have e10 := congrFun (congrFun hXX 1) 0
  have e11 := congrFun (congrFun hXX 1) 1
  have c00 := congrFun (congrFun hYX 0) 0
  have c01 := congrFun (congrFun hYX 0) 1
  have c10 := congrFun (congrFun hYX 1) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)] at e00 e01 e10 e11 c00 c01 c10
  have hbc : X 0 1 ≠ 0 ∨ X 1 0 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hb, hc⟩ := hcon
    apply hx1
    have ha : X 0 0 = 1 := by
      have : (X 0 0 - 1) ^ 2 = 0 := by linear_combination e00 - X 0 1 * hc + (1 - X 0 0) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    have hd : X 1 1 = 1 := by
      have : (X 1 1 - 1) ^ 2 = 0 := by linear_combination e11 - X 1 0 * hb + (1 - X 1 1) * h2
      exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    refine Subtype.ext ?_
    ext i j
    fin_cases i <;> fin_cases j <;> simp [← hX, ha, hb, hc, hd]
  have htr : X 0 0 + X 1 1 = 0 := by
    rcases hbc with hb | hc
    · exact (mul_eq_zero.mp (by linear_combination e01 : X 0 1 * (X 0 0 + X 1 1) = 0)).resolve_left
        hb
    · exact (mul_eq_zero.mp (by linear_combination e10 : X 1 0 * (X 0 0 + X 1 1) = 0)).resolve_left
        hc
  have hpu : Y 0 0 = Y 1 1 := by
    rcases hbc with hb | hc
    · have : X 0 1 * (Y 0 0 - Y 1 1) = 0 := by
        linear_combination c01 - Y 0 1 * htr + Y 0 1 * X 0 0 * h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hb)
    · have : X 1 0 * (Y 0 0 - Y 1 1) = 0 := by
        linear_combination -c10 + Y 1 0 * htr - Y 1 0 * X 1 1 * h2
      exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hc)
  refine Subtype.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sq, Matrix.mul_apply, Fin.sum_univ_two, ← hY]
  · linear_combination hdY + Y 0 0 * hpu + h2 * (Y 0 1 * Y 1 0)
  · linear_combination Y 0 1 * hpu + Y 0 1 * Y 1 1 * h2
  · linear_combination Y 1 0 * hpu + Y 1 0 * Y 1 1 * h2
  · linear_combination hdY - Y 1 1 * hpu + h2 * (Y 0 1 * Y 1 0)

theorem eq_zero_of_fix (A : SpecialLinearGroup (Fin 2) F) (hA : A ^ 2 ≠ 1) {v : Fin 2 → F}
    (hv : (A : Matrix (Fin 2) (Fin 2) F).mulVec v = v) : v = 0 := by
  by_contra h
  exact hA (sq_eq_one_of_fix A h hv)

theorem eq_one_of_commute_of_pow (A x : SpecialLinearGroup (Fin 2) F) (hA : A ^ 2 ≠ 1)
    (hAx : A * x = x * A) {k : ℕ} (hx : x ^ 2 ^ k = 1) : x = 1 := by
  by_contra h
  exact hA (sq_eq_one_of_commute A x (sq_eq_one_of_pow x hx) h hAx)

omit [CharP F 2] in
theorem exists_mulVec_eq (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec (Pi.single 0 1) = v := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, -(v 1)⁻¹; v 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0]
  · refine ⟨⟨!![v 0, 0; v 1, (v 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

omit [CharP F 2] in
theorem exists_mulVec_eq_single (v : Fin 2 → F) (hv : v ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) F,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec v = Pi.single 0 1 := by
  by_cases h0 : v 0 = 0
  · have h1 : v 1 ≠ 0 := fun h1 => hv (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![0, (v 1)⁻¹; -(v 1), 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, h1]
  · refine ⟨⟨!![(v 0)⁻¹, 0; -(v 1), v 0], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h0, mul_comm]

omit [CharP F 2] in
theorem eq_bot_or_eq_top_of_invariant (W : AddSubgroup (Fin 2 → F))
    (hW : ∀ g : SpecialLinearGroup (Fin 2) F, ∀ w ∈ W,
      (g : Matrix (Fin 2) (Fin 2) F).mulVec w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases h : W = ⊥
  · exact Or.inl h
  right
  obtain ⟨⟨w, hwW⟩, hw0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).mp h
  obtain ⟨g, hg⟩ := exists_mulVec_eq_single w (fun h' => hw0 (Subtype.ext h'))
  have he : (Pi.single 0 1 : Fin 2 → F) ∈ W := hg ▸ hW g w hwW
  rw [eq_top_iff]
  intro v _
  by_cases hv : v = 0
  · rw [hv]; exact W.zero_mem
  obtain ⟨g', hg'⟩ := exists_mulVec_eq v hv
  exact hg' ▸ hW g' _ he

end SL2

section Counting

variable {G : Type*} [Group G]

theorem le_commutator_of_fix [Finite G] {P A : Subgroup G} (hPA : P ≤ A) {b : G}
    (hb : b ∈ Subgroup.normalizer (P : Set G)) (hfix : ∀ x ∈ P, x * b = b * x → x = 1) :
    P ≤ ⁅A, Subgroup.zpowers b⁆ := by
  set C := P ⊓ ⁅A, Subgroup.zpowers b⁆
  have hmem : ∀ x ∈ P, x * b * x⁻¹ * b⁻¹ ∈ C := by
    intro x hx
    refine ⟨?_, Subgroup.commutator_mem_commutator (hPA hx) (Subgroup.mem_zpowers b)⟩
    have e : x * b * x⁻¹ * b⁻¹ = x * (b * x⁻¹ * b⁻¹) := by group
    rw [e]
    exact P.mul_mem hx ((Subgroup.mem_normalizer_iff.mp hb x⁻¹).mp (P.inv_mem hx))
  let f : ↥P → ↥C := fun x => ⟨x * b * (x : G)⁻¹ * b⁻¹, hmem x x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have h1 : (x : G) * b * (x : G)⁻¹ * b⁻¹ = y * b * (y : G)⁻¹ * b⁻¹ := congrArg Subtype.val hxy
    have h2 : ((y : G)⁻¹ * x) * b = b * ((y : G)⁻¹ * x) := by
      have h3 : (x : G) * b * (x : G)⁻¹ = y * b * (y : G)⁻¹ := by
        simpa using congrArg (· * b) h1
      calc (y : G)⁻¹ * x * b = (y : G)⁻¹ * ((x : G) * b * (x : G)⁻¹) * x := by group
        _ = (y : G)⁻¹ * (y * b * (y : G)⁻¹) * x := by rw [h3]
        _ = b * ((y : G)⁻¹ * x) := by group
    have := hfix _ (P.mul_mem (P.inv_mem y.2) x.2) h2
    exact Subtype.ext (by simpa [inv_mul_eq_one, eq_comm] using this)
  have hcard : Nat.card P ≤ Nat.card C := Nat.card_le_card_of_injective f hf
  have hCP : C = P := Subgroup.eq_of_le_of_card_ge inf_le_left hcard
  rw [← hCP]
  exact inf_le_right

theorem orderOf_map_eq_of_odd {H : Type*} [Group H] (f : G →* H) (hk : IsPGroup 2 f.ker) {b : G}
    (hb : Odd (orderOf b)) : orderOf (f b) = orderOf b := by
  refine Nat.dvd_antisymm (orderOf_map_dvd f b) ?_
  have h1 : b ^ orderOf (f b) ∈ f.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  obtain ⟨k, hk'⟩ := hk ⟨_, h1⟩
  have h2 : (b ^ orderOf (f b)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk'
  have h3 : orderOf b ∣ orderOf (f b) * 2 ^ k := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
    exact h2
  exact (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hb)).dvd_of_dvd_mul_right h3

end Counting

end C11AmS

end CFSG.Quasithin.Vol2.Ch10.SecB
