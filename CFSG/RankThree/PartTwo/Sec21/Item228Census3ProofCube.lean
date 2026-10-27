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
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof

open Matrix

variable {K : Type} [Field K]

theorem cross_of_cross {u0 u1 u2 w0 w1 w2 m0 m1 m2 : K} (hm : m0 ≠ 0 ∨ m1 ≠ 0 ∨ m2 ≠ 0)
    (hu1 : u0 * m1 = m0 * u1) (hu2 : m0 * u2 = u0 * m2) (hu3 : u1 * m2 = m1 * u2)
    (hw1 : w0 * m1 = m0 * w1) (hw2 : m0 * w2 = w0 * m2) (hw3 : w1 * m2 = m1 * w2) :
    u0 * w1 = w0 * u1 ∧ w0 * u2 = u0 * w2 ∧ u1 * w2 = w1 * u2 := by
  rcases hm with h | h | h
  · have h1 : u0 * w1 = w0 * u1 := mul_left_cancel₀ h (by
      linear_combination (-u0) * hw1 + w0 * hu1)
    refine ⟨h1, mul_left_cancel₀ h (by linear_combination w0 * hu2 - u0 * hw2),
      mul_left_cancel₀ h (by linear_combination u1 * hw2 - w1 * hu2 - m2 * h1)⟩
  · have h1 : u0 * w1 = w0 * u1 := mul_left_cancel₀ h (by
      linear_combination w1 * hu1 - u1 * hw1)
    refine ⟨h1, mul_left_cancel₀ h (by linear_combination (-w0) * hu3 + u0 * hw3 - m2 * h1),
      mul_left_cancel₀ h (by linear_combination (-u1) * hw3 + w1 * hu3)⟩
  · have h2 : w0 * u2 = u0 * w2 := mul_left_cancel₀ h (by
      linear_combination (-u2) * hw2 + w2 * hu2)
    refine ⟨mul_left_cancel₀ h (by linear_combination u0 * hw3 - w0 * hu3 - m1 * h2), h2,
      mul_left_cancel₀ h (by linear_combination w2 * hu3 - u2 * hw3)⟩

theorem commute_conditions {M X : Matrix (Fin 2) (Fin 2) K} (hX : X * M = M * X) :
    X 0 1 * M 1 0 = M 0 1 * X 1 0 ∧ M 0 1 * (X 0 0 - X 1 1) = X 0 1 * (M 0 0 - M 1 1) ∧
      X 1 0 * (M 0 0 - M 1 1) = M 1 0 * (X 0 0 - X 1 1) := by
  have e : ∀ i j, (X * M) i j = (M * X) i j := fun i j => by rw [hX]
  have e00 := e 0 0
  have e01 := e 0 1
  have e10 := e 1 0
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e10
  exact ⟨by linear_combination e00, by linear_combination e01, by linear_combination e10⟩

theorem commute_of_commute_nonscalar {M X Y : Matrix (Fin 2) (Fin 2) K}
    (hM : M 0 1 ≠ 0 ∨ M 1 0 ≠ 0 ∨ M 0 0 - M 1 1 ≠ 0) (hX : X * M = M * X)
    (hY : Y * M = M * Y) : X * Y = Y * X := by
  obtain ⟨x1, x2, x3⟩ := commute_conditions hX
  obtain ⟨y1, y2, y3⟩ := commute_conditions hY
  obtain ⟨k1, k2, k3⟩ := cross_of_cross hM x1 x2 x3 y1 y2 y3
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.mul_apply, Fin.sum_univ_two] <;>
    simp only [Fin.zero_eta, Fin.isValue, Fin.mk_one] <;>
    first | linear_combination k1 | linear_combination k2 | linear_combination -k3 |
      linear_combination -k1 | linear_combination k3

variable (K) in
@[expose] def cubeMat : Matrix (Fin 2) (Fin 2) K := !![0, -1; 1, -1]

theorem cubeMat_sq_add : cubeMat K * cubeMat K + cubeMat K + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeMat]

theorem det_cubeMat : (cubeMat K).det = 1 := by
  simp [cubeMat, Matrix.det_fin_two]

theorem cubeMat_nonscalar :
    cubeMat K 0 1 ≠ 0 ∨ cubeMat K 1 0 ≠ 0 ∨ cubeMat K 0 0 - cubeMat K 1 1 ≠ 0 :=
  Or.inr (Or.inl (by simp [cubeMat]))

theorem eq_of_commute_cubeMat {M : Matrix (Fin 2) (Fin 2) K}
    (h : M * cubeMat K = cubeMat K * M) : M = M 0 0 • 1 + M 1 0 • cubeMat K := by
  have e : ∀ i j, (M * cubeMat K) i j = (cubeMat K * M) i j := fun i j => by rw [h]
  have e00 := e 0 0
  have e01 := e 0 1
  simp [cubeMat, Matrix.mul_apply, Fin.sum_univ_two] at e00 e01
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeMat] <;>
    first | linear_combination e00 | linear_combination -e00 | linear_combination e01 + e00

theorem sq_eq_trace_smul_sub_one {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1) :
    M * M = (M 0 0 + M 1 1) • M - 1 := by
  rw [Matrix.det_fin_two] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    first | linear_combination hdet | linear_combination -hdet | ring

theorem sl2_sq_add_self_add_one {M : Matrix (Fin 2) (Fin 2) K} (hdet : M.det = 1)
    (h3 : M * M * M = 1) (h1 : M ≠ 1) : M * M + M + 1 = 0 := by
  set t := M 0 0 + M 1 1 with ht
  have hCH : M * M = t • M - 1 := sq_eq_trace_smul_sub_one hdet
  have hM3 : M * M * M = (t ^ 2 - 1) • M - t • 1 := by
    calc M * M * M = (t • M - 1) * M := by rw [hCH]
      _ = t • (M * M) - M := by rw [sub_mul, smul_mul_assoc, Matrix.one_mul]
      _ = t • (t • M - 1) - M := by rw [hCH]
      _ = (t ^ 2 - 1) • M - t • 1 := by module
  by_cases ht1 : t + 1 = 0
  · rw [hCH, show t = -1 by linear_combination ht1, neg_one_smul]
    abel
  · exfalso
    have hrel : (t ^ 2 - 1) • M = (t + 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by
      have e := hM3.symm.trans h3
      calc (t ^ 2 - 1) • M = ((t ^ 2 - 1) • M - t • 1) + t • 1 := by abel
        _ = 1 + t • 1 := by rw [e]
        _ = (t + 1) • (1 : Matrix (Fin 2) (Fin 2) K) := by module
    have r00 := congrFun (congrFun hrel 0) 0
    have r01 := congrFun (congrFun hrel 0) 1
    have r10 := congrFun (congrFun hrel 1) 0
    have r11 := congrFun (congrFun hrel 1) 1
    simp at r00 r01 r10 r11
    have ht2 : t ^ 2 - 1 ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at r00
      exact ht1 r00.symm
    have hm01 : M 0 1 = 0 := r01.resolve_left ht2
    have hm10 : M 1 0 = 0 := r10.resolve_left ht2
    have hm11 : M 1 1 = M 0 0 := mul_left_cancel₀ ht2 (r11.trans r00.symm)
    rw [Matrix.det_fin_two, hm01, hm10, hm11] at hdet
    have e3 := congrFun (congrFun h3 0) 0
    simp [Matrix.mul_apply, Fin.sum_univ_two, hm01, hm10] at e3
    have hdet' : M 0 0 * M 0 0 = 1 := by linear_combination hdet
    have hc1 : M 0 0 = 1 := by linear_combination e3 - M 0 0 * hdet'
    apply h1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hm01, hm10, hm11, hc1]

variable (K) in
@[expose] def cubeAlg : Subalgebra K (Matrix (Fin 2) (Fin 2) K) :=
  Subalgebra.centralizer K {cubeMat K}

theorem mem_cubeAlg {M : Matrix (Fin 2) (Fin 2) K} :
    M ∈ cubeAlg K ↔ M * cubeMat K = cubeMat K * M := by
  rw [cubeAlg, Subalgebra.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  exact eq_comm

theorem smul_one_add_smul_mem_cubeAlg (a b : K) : a • (1 : Matrix (Fin 2) (Fin 2) K) +
    b • cubeMat K ∈ cubeAlg K := by
  rw [mem_cubeAlg, add_mul, mul_add, smul_mul_assoc, smul_mul_assoc, mul_smul_comm,
    mul_smul_comm, Matrix.one_mul, Matrix.mul_one]

theorem eq_of_mem_cubeAlg {M : Matrix (Fin 2) (Fin 2) K} (hM : M ∈ cubeAlg K) :
    M = M 0 0 • 1 + M 1 0 • cubeMat K :=
  eq_of_commute_cubeMat (mem_cubeAlg.mp hM)

theorem cubeAlg_mul_comm {M N : Matrix (Fin 2) (Fin 2) K} (hM : M ∈ cubeAlg K)
    (hN : N ∈ cubeAlg K) : M * N = N * M :=
  commute_of_commute_nonscalar cubeMat_nonscalar (mem_cubeAlg.mp hM) (mem_cubeAlg.mp hN)

instance : CommRing (cubeAlg K) :=
  { (inferInstance : Ring (cubeAlg K)) with
    mul_comm := fun x y => Subtype.ext (cubeAlg_mul_comm x.2 y.2) }

@[expose] def cubeBarM (M : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 2) (Fin 2) K :=
  (M 0 0 - M 1 0) • 1 - M 1 0 • cubeMat K

theorem cubeBarM_smul_add (a b : K) :
    cubeBarM (a • (1 : Matrix (Fin 2) (Fin 2) K) + b • cubeMat K) =
      (a - b) • 1 - b • cubeMat K := by
  simp [cubeBarM, cubeMat]

theorem cubeBarM_mem (M : Matrix (Fin 2) (Fin 2) K) : cubeBarM M ∈ cubeAlg K := by
  rw [cubeBarM, sub_eq_add_neg, ← neg_smul]
  exact smul_one_add_smul_mem_cubeAlg _ _

theorem mul_cubeBarM {M : Matrix (Fin 2) (Fin 2) K} (hM : M ∈ cubeAlg K) :
    M * cubeBarM M = (M 0 0 * M 0 0 - M 0 0 * M 1 0 + M 1 0 * M 1 0) • 1 := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : K, M = a • 1 + b • cubeMat K := ⟨_, _, eq_of_mem_cubeAlg hM⟩
  rw [cubeBarM_smul_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeMat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

theorem eq_smul_one_of_cubeBarM_eq (h2 : (2 : K) ≠ 0) {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M ∈ cubeAlg K) (h : cubeBarM M = M) : M = M 0 0 • 1 := by
  have e := congrFun (congrFun h 1) 0
  simp [cubeBarM, cubeMat] at e
  have hb : M 1 0 = 0 := by
    have : 2 * M 1 0 = 0 := by linear_combination -e
    exact (mul_eq_zero.mp this).resolve_left h2
  conv_lhs => rw [eq_of_mem_cubeAlg hM, hb, zero_smul, add_zero]

variable (K) in
@[expose] def gramS : Matrix (Fin 2) (Fin 2) K := !![2, -1; -1, 2]

theorem transpose_mul_gramS {M : Matrix (Fin 2) (Fin 2) K} (hM : M ∈ cubeAlg K) :
    Mᵀ * gramS K = gramS K * cubeBarM M := by
  obtain ⟨a, b, rfl⟩ : ∃ a b : K, M = a • 1 + b • cubeMat K := ⟨_, _, eq_of_mem_cubeAlg hM⟩
  rw [cubeBarM_smul_add]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cubeMat, gramS, Matrix.mul_apply, Fin.sum_univ_two] <;>
    ring

theorem det_gramS : (gramS K).det = 3 := by
  rw [gramS, Matrix.det_fin_two_of]
  norm_num

theorem isField_cubeAlg (hK : ∀ s : K, s * s + s + 1 ≠ 0) : IsField (cubeAlg K) where
  exists_pair_ne := ⟨0, 1, fun h => by
    have := congrArg (fun x : cubeAlg K => (x : Matrix (Fin 2) (Fin 2) K) 0 0) h
    simp at this⟩
  mul_comm := mul_comm
  mul_inv_cancel := by
    intro u hu
    set a := (u : Matrix (Fin 2) (Fin 2) K) 0 0
    set b := (u : Matrix (Fin 2) (Fin 2) K) 1 0
    have hN : a * a - a * b + b * b ≠ 0 := by
      by_cases hb : b = 0
      · have ha : a ≠ 0 := by
          intro ha
          apply hu
          apply Subtype.ext
          rw [eq_of_mem_cubeAlg u.2]
          change a • 1 + b • cubeMat K = 0
          rw [ha, hb, zero_smul, zero_smul, add_zero]
        rw [hb]
        simpa using ha
      · intro h0
        apply hK (-a / b)
        field_simp
        linear_combination h0
    refine ⟨⟨(a * a - a * b + b * b)⁻¹ • cubeBarM (u : Matrix (Fin 2) (Fin 2) K),
      Subalgebra.smul_mem _ (cubeBarM_mem _) _⟩, Subtype.ext ?_⟩
    change (u : Matrix (Fin 2) (Fin 2) K) * ((a * a - a * b + b * b)⁻¹ •
      cubeBarM (u : Matrix (Fin 2) (Fin 2) K)) = 1
    rw [mul_smul_comm, mul_cubeBarM u.2, smul_smul, inv_mul_cancel₀ hN, one_smul]

theorem card_cubeAlg : Nat.card (cubeAlg K) = Nat.card K ^ 2 := by
  have e : K × K ≃ cubeAlg K :=
    { toFun := fun x => ⟨x.1 • 1 + x.2 • cubeMat K, smul_one_add_smul_mem_cubeAlg _ _⟩
      invFun := fun u => ((u : Matrix (Fin 2) (Fin 2) K) 0 0, (u : Matrix (Fin 2) (Fin 2) K) 1 0)
      left_inv := fun x => by simp [cubeMat]
      right_inv := fun u => Subtype.ext (eq_of_mem_cubeAlg u.2).symm }
  rw [← Nat.card_congr e, Nat.card_prod, sq]

end CFSG.RankThree.PartTwo.Sec21.Item228Census3Proof
