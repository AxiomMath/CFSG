module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2PslDefs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.H13.NFa2

open scoped MatrixGroups

lemma psl2Conj_quadForm_ne_zero {F : Type*} [Field F] (x y z : F) (h2 : (2 : F) ≠ 0)
    (hN : x ^ 2 + y * z = -1) : ∃ u v : F, -y * u ^ 2 + 2 * x * u * v + z * v ^ 2 ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  have h10 := hcon 1 0
  have h01 := hcon 0 1
  have h11 := hcon 1 1
  have hy : y = 0 := by linear_combination -h10
  have hz : z = 0 := by linear_combination h01
  have hx : x = 0 := by
    have h2x : 2 * x = 0 := by linear_combination h11 - h10 - h01
    exact (mul_eq_zero.mp h2x).resolve_left h2
  rw [hx, hy, hz] at hN
  norm_num at hN

lemma psl2Conj_rot_comm_S {F : Type*} [CommRing F] (a b : F) :
    !![a, -b; b, a] * !![0, -1; 1, 0] = !![0, -1; 1, 0] * !![a, -b; b, a] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring

lemma psl2Conj_mul_g_eq_S_mul_g {F : Type*} [CommRing F] (u v x y z : F)
    (hN : x ^ 2 + y * z = -1) :
    !![u, v; -(u * x + v * z), v * x - u * y] * !![x, y; z, -x] =
      !![0, -1; 1, 0] * !![u, v; -(u * x + v * z), v * x - u * y] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  all_goals first
    | ring1
    | linear_combination (-u) * hN
    | linear_combination (-v) * hN

lemma psl2Conj_det_rot {F : Type*} [CommRing F] (a b : F) :
    (!![a, -b; b, a] : Matrix (Fin 2) (Fin 2) F).det = a ^ 2 + b ^ 2 := by
  rw [Matrix.det_fin_two_of]; ring

lemma psl2Conj_det_g {F : Type*} [CommRing F] (u v x y z : F) :
    (!![u, v; -(u * x + v * z), v * x - u * y] : Matrix (Fin 2) (Fin 2) F).det =
      -y * u ^ 2 + 2 * x * u * v + z * v ^ 2 := by
  rw [Matrix.det_fin_two_of]; ring

lemma psl2Conj_exists_xyz {F : Type*} [Field F] (x y z : F) (h2 : (2 : F) ≠ 0)
    (hN : x ^ 2 + y * z = -1) (hsum : ∀ d : F, ∃ a b : F, a ^ 2 + b ^ 2 = d) :
    ∃ h : Matrix (Fin 2) (Fin 2) F, h.det = 1 ∧
      h * !![x, y; z, -x] = !![0, -1; 1, 0] * h := by
  obtain ⟨u, v, hQ⟩ := psl2Conj_quadForm_ne_zero x y z h2 hN
  obtain ⟨a, b, hab⟩ := hsum (-y * u ^ 2 + 2 * x * u * v + z * v ^ 2)⁻¹
  refine ⟨!![a, -b; b, a] * !![u, v; -(u * x + v * z), v * x - u * y], ?_, ?_⟩
  · rw [Matrix.det_mul, psl2Conj_det_rot, psl2Conj_det_g, hab, inv_mul_cancel₀ hQ]
  · rw [Matrix.mul_assoc, psl2Conj_mul_g_eq_S_mul_g u v x y z hN, ← Matrix.mul_assoc,
      psl2Conj_rot_comm_S, Matrix.mul_assoc]

def psl2S (F : Type*) [CommRing F] : Matrix.SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, -1; 1, 0], by rw [Matrix.det_fin_two_of]; ring⟩

lemma psl2Conj_exists_matrix {F : Type*} [Field F] (M : Matrix (Fin 2) (Fin 2) F)
    (hdet : M.det = 1) (htr : M 0 0 + M 1 1 = 0) (h2 : (2 : F) ≠ 0)
    (hsum : ∀ d : F, ∃ a b : F, a ^ 2 + b ^ 2 = d) :
    ∃ H : Matrix (Fin 2) (Fin 2) F, H.det = 1 ∧ H * M = !![0, -1; 1, 0] * H := by
  have h11 : M 1 1 = -M 0 0 := by linear_combination htr
  have hN : M 0 0 ^ 2 + M 0 1 * M 1 0 = -1 := by
    rw [Matrix.det_fin_two, h11] at hdet
    linear_combination -hdet
  have hMeq : M = !![M 0 0, M 0 1; M 1 0, -M 0 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h11]
  obtain ⟨H, hH, hHM⟩ := psl2Conj_exists_xyz (M 0 0) (M 0 1) (M 1 0) h2 hN hsum
  refine ⟨H, hH, ?_⟩
  rw [hMeq]
  exact hHM

lemma psl2_two_ne_zero_zmod (q : ℕ) [Fact q.Prime] (hq : 3 ≤ q) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [CharP.cast_eq_zero_iff (ZMod q) q] at h'
  have := Nat.le_of_dvd (by norm_num) h'
  omega

lemma psl2Conj_trace_zero {F : Type*} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (hAA : A ^ 2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))
    (hA : A ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) :
    (A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 0 := by
  by_contra hne
  apply hA
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hAA
  have hM : Matrix.scalar (Fin 2) r =
      (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) := by
    rw [hr, sq, Matrix.SpecialLinearGroup.coe_mul]
  have hdet : (A : Matrix (Fin 2) (Fin 2) F).det = 1 := A.2
  rw [Matrix.det_fin_two] at hdet
  have e00 := congrFun (congrFun hM 0) 0
  have e01 := congrFun (congrFun hM 0) 1
  have e10 := congrFun (congrFun hM 1) 0
  have e11 := congrFun (congrFun hM 1) 1
  simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.mul_apply,
    Fin.sum_univ_two] at e00 e01 e10 e11
  have hy : (A : Matrix (Fin 2) (Fin 2) F) 0 1 = 0 := by
    have h' : (A : Matrix (Fin 2) (Fin 2) F) 0 1 *
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination -e01
    exact (mul_eq_zero.mp h').resolve_right hne
  have hz : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 := by
    have h' : (A : Matrix (Fin 2) (Fin 2) F) 1 0 *
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination -e10
    exact (mul_eq_zero.mp h').resolve_right hne
  have hxw : (A : Matrix (Fin 2) (Fin 2) F) 0 0 = (A : Matrix (Fin 2) (Fin 2) F) 1 1 := by
    have h' : ((A : Matrix (Fin 2) (Fin 2) F) 0 0 - (A : Matrix (Fin 2) (Fin 2) F) 1 1) *
        ((A : Matrix (Fin 2) (Fin 2) F) 0 0 + (A : Matrix (Fin 2) (Fin 2) F) 1 1) = 0 := by
      linear_combination e11 - e00
    exact sub_eq_zero.mp ((mul_eq_zero.mp h').resolve_right hne)
  have hx2 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 = 1 := by
    linear_combination hdet + (A : Matrix (Fin 2) (Fin 2) F) 0 0 * hxw +
      (A : Matrix (Fin 2) (Fin 2) F) 1 0 * hy
  refine Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨(A : Matrix (Fin 2) (Fin 2) F) 0 0, ?_, ?_⟩
  · rw [Fintype.card_fin]
    exact hx2
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.scalar_apply, Matrix.diagonal_apply, hy, hz, hxw]

lemma psl2Conj_isConj_S {F : Type*} [Field F] (c : PSL(2, F)) (h2 : (2 : F) ≠ 0)
    (hsum : ∀ d : F, ∃ a b : F, a ^ 2 + b ^ 2 = d) (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) :
    IsConj c (QuotientGroup.mk (psl2S F)) := by
  obtain ⟨A, rfl⟩ := QuotientGroup.mk_surjective c
  have hAA : A ^ 2 ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) :=
    (QuotientGroup.eq_one_iff (A ^ 2)).mp (by rw [QuotientGroup.mk_pow]; exact hc2)
  have hA : A ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := fun hm =>
    hc1 ((QuotientGroup.eq_one_iff A).mpr hm)
  have htr := psl2Conj_trace_zero A hAA hA
  obtain ⟨H, hH, hHA⟩ :=
    psl2Conj_exists_matrix (A : Matrix (Fin 2) (Fin 2) F) A.2 htr h2 hsum
  obtain ⟨Hs, hHs⟩ : ∃ Hs : Matrix.SpecialLinearGroup (Fin 2) F,
      (Hs : Matrix (Fin 2) (Fin 2) F) = H := ⟨⟨H, hH⟩, rfl⟩
  have hconj : Hs * A * Hs⁻¹ = psl2S F := by
    rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hHs]
    exact hHA
  refine isConj_iff.mpr ⟨(Hs : PSL(2, F)), ?_⟩
  have h' := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 2) F => (X : PSL(2, F))) hconj
  simpa only [QuotientGroup.mk_mul, QuotientGroup.mk_inv] using h'

theorem psl2_involutions_conj : PslConjStmt := by
  intro q _ hq a b ha hb
  have h2 : (2 : ZMod q) ≠ 0 := psl2_two_ne_zero_zmod q hq
  have hsum : ∀ d : ZMod q, ∃ x y : ZMod q, x ^ 2 + y ^ 2 = d := fun d => ZMod.sq_add_sq q d
  have key : ∀ c : PSL(2, ZMod q), orderOf c = 2 →
      IsConj c (QuotientGroup.mk (psl2S (ZMod q))) := fun c hc => by
    obtain ⟨hc2, hc1⟩ := orderOf_eq_prime_iff.mp hc
    exact psl2Conj_isConj_S c h2 hsum hc2 hc1
  exact (key a ha).trans (key b hb).symm

end CFSG.Quasithin.H13.NFa2
