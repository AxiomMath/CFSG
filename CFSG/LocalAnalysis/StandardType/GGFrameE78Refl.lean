module

public import CFSG.LocalAnalysis.StandardType.GGFrameE78Facts
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute

open Matrix

def feCol (n : ℕ) (i : Fin n) : FEVec n := fun p => ((CartanMatrix.E n p i : ℤ) : ZMod 3)

def feRow (n : ℕ) (i : Fin n) : FEVec n := Pi.single i 1

theorem feCol_self (n : ℕ) (i : Fin n) : feCol n i i = 2 := by
  simp [feCol, CartanMatrix.E_diag]

theorem feRow_dot (n : ℕ) (i : Fin n) (v : FEVec n) : feRow n i ⬝ᵥ v = v i := by
  rw [feRow, single_one_dotProduct]

theorem feS_eq (n : ℕ) (i : Fin n) :
    feS n i = 1 - Matrix.vecMulVec (feCol n i) (feRow n i) := by
  ext p q
  simp only [feS, feCol, feRow, Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.one_apply,
    Pi.single_apply]
  by_cases h : q = i <;> simp [h]

theorem feS_mulVec (n : ℕ) (i : Fin n) (v : FEVec n) :
    (feS n i).mulVec v = v - (v i) • feCol n i := by
  rw [feS_eq, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.vecMulVec_mulVec,
    feRow_dot]
  simp

theorem feS_mul_self (n : ℕ) (i : Fin n) : feS n i * feS n i = 1 := by
  rw [feS_eq]
  set u := feCol n i
  set e := feRow n i
  have heu : e ⬝ᵥ u = 2 := by
    rw [feRow_dot]
    simpa [u] using feCol_self n i
  have hAA : Matrix.vecMulVec u e * Matrix.vecMulVec u e =
      (2 : ZMod 3) • Matrix.vecMulVec u e := by
    rw [Matrix.vecMulVec_mul_vecMulVec, heu, Matrix.vecMulVec_smul]
  calc (1 - Matrix.vecMulVec u e) * (1 - Matrix.vecMulVec u e)
      = 1 - Matrix.vecMulVec u e - Matrix.vecMulVec u e
          + Matrix.vecMulVec u e * Matrix.vecMulVec u e := by noncomm_ring
    _ = 1 - Matrix.vecMulVec u e - Matrix.vecMulVec u e
          + (2 : ZMod 3) • Matrix.vecMulVec u e := by rw [hAA]
    _ = 1 := by rw [two_smul]; abel

theorem feS_neg_line (n : ℕ) (i : Fin n) (w : FEVec n)
    (h : (feS n i).mulVec w = -w) :
    w = (2 * w i) • feCol n i := by
  rw [feS_mulVec] at h
  have h2 : (2 : ZMod 3) • w = (w i) • feCol n i := by
    have hc0 : w - (w i) • feCol n i + w = 0 := (eq_neg_iff_add_eq_zero).mp h
    have hc' : (2 : ZMod 3) • w - (w i) • feCol n i = 0 := by
      simpa [two_smul, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hc0
    exact sub_eq_zero.mp hc'
  have h22 : (2 : ZMod 3) * 2 = 1 := by decide
  calc w = ((2 : ZMod 3) * 2) • w := by rw [h22, one_smul]
    _ = (2 : ZMod 3) • ((2 : ZMod 3) • w) := by rw [smul_smul]
    _ = (2 : ZMod 3) • ((w i) • feCol n i) := by rw [h2]
    _ = ((2 : ZMod 3) * w i) • feCol n i := by rw [smul_smul]

private theorem feT_reflect_props {n : ℕ} {r : FEMat n} (hr : FEConjDer n r) :
    r * r = 1 ∧ ∃ v : FEVec n, v ≠ 0 ∧ r.mulVec v = -v ∧
      ∀ w : FEVec n, r.mulVec w = -w → ∃ c : ZMod 3, w = c • v := by
  induction hr with
  | base i =>
      refine ⟨feS_mul_self n i, feCol n i, ?_, ?_, ?_⟩
      · intro h
        have hi := congrFun h i
        rw [feCol_self] at hi
        exact (by decide : (2 : ZMod 3) ≠ 0) hi
      · rw [feS_mulVec, feCol_self, two_smul]
        abel
      · intro w hw
        exact ⟨2 * w i, feS_neg_line n i w hw⟩
  | conj i hr ih =>
      rename_i r
      obtain ⟨hr2, v, hv0, hrv, hline⟩ := ih
      let s := feS n i
      have hs2 : s * s = 1 := feS_mul_self n i
      have hss : ∀ x : FEVec n, s.mulVec (s.mulVec x) = x := by
        intro x
        rw [Matrix.mulVec_mulVec, hs2, Matrix.one_mulVec]
      have hs_conj : s * (s * r * s) = r * s := by
        calc s * (s * r * s) = (s * s) * (r * s) := by noncomm_ring
          _ = r * s := by rw [hs2, one_mul]
      refine ⟨?_, s.mulVec v, ?_, ?_, ?_⟩
      · calc (s * r * s) * (s * r * s)
            = s * (r * (s * s) * r) * s := by noncomm_ring
          _ = s * (r * r) * s := by simp [hs2]
          _ = 1 := by simp [hr2, hs2]
      · intro hv
        have hsv : s.mulVec (s.mulVec v) = v := hss v
        rw [hv, Matrix.mulVec_zero] at hsv
        exact hv0 hsv.symm
      · calc (s * r * s).mulVec (s.mulVec v)
            = (s * r * s * s).mulVec v := by rw [Matrix.mulVec_mulVec]
          _ = (s * r).mulVec v := by rw [mul_assoc, hs2, mul_one]
          _ = s.mulVec (r.mulVec v) := by rw [Matrix.mulVec_mulVec]
          _ = s.mulVec (-v) := by rw [hrv]
          _ = -(s.mulVec v) := Matrix.mulVec_neg v s
      · intro w hw
        have hs_w : s.mulVec ((s * r * s).mulVec w) = -(s.mulVec w) := by
          rw [hw]
          exact Matrix.mulVec_neg w s
        have hleft : s.mulVec ((s * r * s).mulVec w) = r.mulVec (s.mulVec w) := by
          calc s.mulVec ((s * r * s).mulVec w)
              = (s * (s * r * s)).mulVec w := Matrix.mulVec_mulVec w s (s * r * s)
            _ = (r * s).mulVec w := by rw [hs_conj]
            _ = r.mulVec (s.mulVec w) := (Matrix.mulVec_mulVec w r s).symm
        have hneg : r.mulVec (s.mulVec w) = -(s.mulVec w) := by
          rw [hleft] at hs_w
          exact hs_w
        obtain ⟨c, hc⟩ := hline (s.mulVec w) hneg
        refine ⟨c, ?_⟩
        calc w = s.mulVec (s.mulVec w) := (hss w).symm
          _ = s.mulVec (c • v) := by rw [hc]
          _ = c • s.mulVec v := Matrix.mulVec_smul s c v

theorem feT_mul_self {n : ℕ} {r : FEMat n} (hr : r ∈ feT n) : r * r = 1 :=
  (feT_reflect_props (show FEConjDer n r from hr)).1

theorem feT_negative_line {n : ℕ} {r : FEMat n} (hr : r ∈ feT n) :
    ∃ v : FEVec n, v ≠ 0 ∧ r.mulVec v = -v ∧
      ∀ w : FEVec n, r.mulVec w = -w → ∃ c : ZMod 3, w = c • v :=
  (feT_reflect_props (show FEConjDer n r from hr)).2

end CFSG.StandardType.FrameRoute

end
