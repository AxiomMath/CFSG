module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.GGFrameE78Defs

public section

namespace CFSG.StandardType.FrameRoute

theorem fe_reflections_commute_fix_negative {n : ℕ} {r t : FEMat n}
    (hr2 : r * r = 1) (ht2 : t * t = 1)
    (hrline : ∃ v : FEVec n, v ≠ 0 ∧ r.mulVec v = -v ∧
      ∀ w : FEVec n, r.mulVec w = -w → ∃ c : ZMod 3, w = c • v)
    (htline : ∃ v : FEVec n, v ≠ 0 ∧ t.mulVec v = -v ∧
      ∀ w : FEVec n, t.mulVec w = -w → ∃ c : ZMod 3, w = c • v)
    (hcomm : r * t = t * r) (hne : r ≠ t) :
    ∀ v : FEVec n, t.mulVec v = -v → r.mulVec v = v := by
  obtain ⟨u, hu_ne, htu, ht_span⟩ := htline
  obtain ⟨z, hz_ne, hrz, hr_span⟩ := hrline
  have hru : r.mulVec u = u := by
    by_contra hru_ne
    set d : FEVec n := r.mulVec u - u with hd_def
    have hd_ne : d ≠ 0 := sub_ne_zero_of_ne hru_ne
    have htd : t.mulVec d = -d := by
      calc
        t.mulVec d = t.mulVec (r.mulVec u) - t.mulVec u := by
          rw [hd_def, Matrix.mulVec_sub]
        _ = (t * r).mulVec u - t.mulVec u := by
          rw [Matrix.mulVec_mulVec]
        _ = (r * t).mulVec u - t.mulVec u := by rw [← hcomm]
        _ = r.mulVec (t.mulVec u) - t.mulVec u := by
          rw [Matrix.mulVec_mulVec]
        _ = r.mulVec (-u) - (-u) := by rw [htu]
        _ = -(r.mulVec u) - (-u) := by
          exact congrArg (fun z => z - (-u)) (Matrix.mulVec_neg u r)
        _ = -(r.mulVec u - u) := by abel
    obtain ⟨c, hc⟩ := ht_span d htd
    have hc_ne : c ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hc
      exact hd_ne hc
    have hrd : r.mulVec d = -d := by
      calc
        r.mulVec d = r.mulVec (r.mulVec u) - r.mulVec u := by
          rw [hd_def, Matrix.mulVec_sub]
        _ = (r * r).mulVec u - r.mulVec u := by
          rw [Matrix.mulVec_mulVec]
        _ = u - r.mulVec u := by rw [hr2, Matrix.one_mulVec]
        _ = -(r.mulVec u - u) := by abel
    have hstep : c • (r.mulVec u) = c • (-u) := by
      calc
        c • (r.mulVec u) = r.mulVec (c • u) := by rw [Matrix.mulVec_smul]
        _ = r.mulVec d := by rw [← hc]
        _ = -d := hrd
        _ = -(c • u) := by rw [hc]
        _ = c • (-u) := (smul_neg c u).symm
    have hru_neg : r.mulVec u = -u :=
      (IsUnit.smul_left_cancel (isUnit_iff_ne_zero.mpr hc_ne)).mp hstep
    have hz_eq : ∃ c0 : ZMod 3, z = c0 • u := by
      obtain ⟨c0, hc0⟩ := hr_span u hru_neg
      have hc0_ne : c0 ≠ 0 := by
        rintro rfl
        rw [zero_smul] at hc0
        exact hu_ne hc0
      refine ⟨c0⁻¹, ?_⟩
      rw [hc0, smul_smul, inv_mul_cancel₀ hc0_ne, one_smul]
    have hr_neg_span : ∀ w : FEVec n, r.mulVec w = -w → ∃ c : ZMod 3, w = c • u := by
      intro w hw
      obtain ⟨cw, hcw⟩ := hr_span w hw
      obtain ⟨c0, hc0⟩ := hz_eq
      refine ⟨cw * c0, ?_⟩
      rw [hcw, hc0, smul_smul]
    have hrt : r = t := by
      refine Matrix.ext_iff_mulVec.mpr fun w => ?_
      set x : FEVec n := t.mulVec w - w with hx_def
      set y : FEVec n := r.mulVec w - w with hy_def
      have htx : t.mulVec x = -x := by
        calc
          t.mulVec x = t.mulVec (t.mulVec w) - t.mulVec w := by
            rw [hx_def, Matrix.mulVec_sub]
          _ = (t * t).mulVec w - t.mulVec w := by
            rw [Matrix.mulVec_mulVec]
          _ = w - t.mulVec w := by rw [ht2, Matrix.one_mulVec]
          _ = -x := by
            rw [hx_def]
            abel
      have hry : r.mulVec y = -y := by
        calc
          r.mulVec y = r.mulVec (r.mulVec w) - r.mulVec w := by
            rw [hy_def, Matrix.mulVec_sub]
          _ = (r * r).mulVec w - r.mulVec w := by
            rw [Matrix.mulVec_mulVec]
          _ = w - r.mulVec w := by rw [hr2, Matrix.one_mulVec]
          _ = -y := by
            rw [hy_def]
            abel
      obtain ⟨a, ha⟩ := ht_span x htx
      obtain ⟨b, hb⟩ := hr_neg_span y hry
      have hrx : r.mulVec x = -x := by
        rw [ha, Matrix.mulVec_smul, hru_neg]
        exact smul_neg a u
      have hty : t.mulVec y = -y := by
        rw [hb, Matrix.mulVec_smul, htu]
        exact smul_neg b u
      have htw : t.mulVec w = w + x := by
        rw [hx_def]
        abel
      have hrw : r.mulVec w = w + y := by
        rw [hy_def]
        abel
      have hcommw : r.mulVec (t.mulVec w) = t.mulVec (r.mulVec w) := by
        calc
          r.mulVec (t.mulVec w) = (r * t).mulVec w := by
            rw [Matrix.mulVec_mulVec]
          _ = (t * r).mulVec w := by rw [hcomm]
          _ = t.mulVec (r.mulVec w) := by
            rw [Matrix.mulVec_mulVec]
      have e1 : r.mulVec (t.mulVec w) = w + (y - x) := by
        rw [htw, Matrix.mulVec_add, hrw, hrx]
        abel
      have e2 : t.mulVec (r.mulVec w) = w + (x - y) := by
        rw [hrw, Matrix.mulVec_add, htw, hty]
        abel
      have hcancel : y - x = x - y := by
        have h := hcommw
        rw [e1, e2] at h
        exact add_left_cancel h
      have h2 : (2 : ZMod 3) • (y - x) = 0 := by
        calc
          (2 : ZMod 3) • (y - x) = (y - x) + (y - x) := by rw [two_smul]
          _ = (x - y) + (y - x) := by rw [hcancel]
          _ = 0 := by abel
      have h2' : (2 : ZMod 3) • (y - x) = (2 : ZMod 3) • (0 : FEVec n) := by
        simpa using h2
      have h2ne : (2 : ZMod 3) ≠ 0 := by
        intro h
        have hdvd : (3 : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 3).mp h
        norm_num at hdvd
      have hzero : y - x = 0 :=
        (IsUnit.smul_left_cancel (isUnit_iff_ne_zero.mpr h2ne)).mp h2'
      have hyx : y = x := sub_eq_zero.mp hzero
      rw [hrw, htw, hyx]
    exact hne hrt
  intro v hv
  obtain ⟨c, rfl⟩ := ht_span v hv
  rw [Matrix.mulVec_smul, hru]

end CFSG.StandardType.FrameRoute

end
