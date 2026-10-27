module

public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgT

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

@[expose] def zc (c : K) (hc : J.conj c = -c) : Coord J := ⟨(0, c), by rw [hc]; ring⟩

theorem zc_fst {c : K} (hc : J.conj c = -c) : (zc c hc).1.1 = 0 := rfl

theorem zc_snd {c : K} (hc : J.conj c = -c) : (zc c hc).1.2 = c := rfl

theorem eq_zc {z : Coord J} (hz : z.1.1 = 0) :
    z = zc z.1.2 (conj_snd_of_fst_eq_zero hz) :=
  coord_ext hz rfl

variable [Finite K] {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ →* Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp

variable (H : SMapHyp J q F σ h)
include H

omit [Finite K] in
theorem moufang_fst {κ : K} (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
      (F z).1.1 = 0 ∧ (F z).1.2 = κ / z.1.2)
    (hκc : J.conj κ = κ) {c : K} (hc0 : c ≠ 0) (hc : J.conj c = -c)
    {w : Coord J} (hw : w.1.1 ≠ 0) :
    gam J F (w.1.2 + c) = ((h (zc c hc) : K) * (J.conj (h (zc c hc) : K))⁻¹ ^ 2) *
      gam J F (κ / c + emm J F w.1.2) * gam J F w.1.2 := by
  set z := zc c hc with hzdef
  have hz1 : z ≠ 1 := fun e => hc0 (congrArg (fun v : Coord J => v.1.2) e)
  have hM := H.F_moufang z w hz1 rfl hw
  have hzi1 : z⁻¹ ≠ 1 := inv_ne_one.mpr hz1
  obtain ⟨hFi1, hFi2⟩ := hκF z⁻¹ hzi1 (by rw [inv_fst, zc_fst, neg_zero])
  have hr1 : ((F z⁻¹)⁻¹).1.1 = 0 := by rw [inv_fst, hFi1, neg_zero]
  have hr2 : ((F z⁻¹)⁻¹).1.2 = κ / c := by
    rw [inv_snd, hFi2, inv_snd, zc_snd, hc, map_div₀, hκc, map_neg, hc, neg_neg]
  have hFw := H.F_fst_eq hw
  have hFw2 := H.F_snd_eq hw
  set v := (F z⁻¹)⁻¹ * F w with hvdef
  have hv1 : v.1.1 = gam J F w.1.2 * w.1.1 := by rw [hvdef, mul_fst, hr1, hFw, zero_add]
  have hv2 : v.1.2 = κ / c + emm J F w.1.2 := by
    rw [hvdef, mul_snd, hr1, hr2, hFw2, zero_mul, sub_zero]
  have hv : v.1.1 ≠ 0 := by rw [hv1]; exact mul_ne_zero (H.gam_ne_zero hw) hw
  have hzw : (z * w).1.1 ≠ 0 := by rw [mul_fst, zc_fst, zero_add]; exact hw
  have h1 := congrArg (fun u : Coord J => u.1.1) hM
  change (F (z * w)).1.1 = (F z * hermitianTorusAction J (h z) (F v)).1.1 at h1
  rw [mul_fst, (hκF z hz1 rfl).1, zero_add, torus_fst, H.F_fst_eq hzw, H.F_fst_eq hv, hv1,
    hv2] at h1
  have hzw2 : (z * w).1.2 = w.1.2 + c := by
    rw [mul_snd, zc_fst, zc_snd, zero_mul, sub_zero, add_comm]
  rw [hzw2, mul_fst, zc_fst, zero_add] at h1
  have h2 : gam J F (w.1.2 + c) * w.1.1 =
      ((h z : K) * (J.conj (h z : K))⁻¹ ^ 2) * gam J F (κ / c + emm J F w.1.2) *
        gam J F w.1.2 * w.1.1 := by
    rw [h1]; ring
  exact mul_right_cancel₀ hw h2

theorem sgn_sq (y : K) : sgn J σ y = 1 ∨ sgn J σ y = -1 := by
  classical
  by_cases hy : ∃ k : Kˣ, nrm J k = y
  · rw [sgn, dite_eq_left hy]; exact H.eps_sq _
  · left; rw [sgn, dite_eq_right hy]

theorem sgn_mul_self (y : K) : sgn J σ y * sgn J σ y = 1 := by
  rcases H.sgn_sq y with e | e <;> rw [e] <;> ring

omit [Finite K] in
theorem nrm_h_center {κ : K} (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 →
      (F z).1.1 = 0 ∧ (F z).1.2 = κ / z.1.2)
    (hκ0 : κ ≠ 0) (hκc : J.conj κ = κ) {c : K} (hc0 : c ≠ 0) (hc : J.conj c = -c) :
    nrm J (h (zc c hc) : K) = -c ^ 2 / κ := by
  set z := zc c hc with hzdef
  have hz1 : z ≠ 1 := fun e => hc0 (congrArg (fun v : Coord J => v.1.2) e)
  have hR := H.h_rel z hz1 rfl
  have hzi1 : z⁻¹ ≠ 1 := inv_ne_one.mpr hz1
  obtain ⟨hFi1, hFi2⟩ := hκF z⁻¹ hzi1 (by rw [inv_fst, zc_fst, neg_zero])
  have hr1 : ((F z⁻¹)⁻¹).1.1 = 0 := by rw [inv_fst, hFi1, neg_zero]
  have hr2 : ((F z⁻¹)⁻¹).1.2 = κ / c := by
    rw [inv_snd, hFi2, inv_snd, zc_snd, hc, map_div₀, hκc, map_neg, hc, neg_neg]
  have hr0 : (F z⁻¹)⁻¹ ≠ 1 := by
    intro e
    have := congrArg (fun v : Coord J => v.1.2) e
    change ((F z⁻¹)⁻¹).1.2 = 0 at this
    rw [hr2] at this
    exact div_ne_zero hκ0 hc0 this
  obtain ⟨-, hFr2⟩ := hκF _ hr0 hr1
  rw [hr2] at hFr2
  have h2 := congrArg (fun v : Coord J => v.1.2) hR
  change (hermitianTorusAction J (h z) (F (F z⁻¹)⁻¹)).1.2 = ((F z)⁻¹).1.2 at h2
  rw [torus_snd, hFr2, inv_snd, (hκF z hz1 rfl).2, zc_snd, map_div₀, hκc, hc] at h2
  have hh0 : (h z : K) ≠ 0 := (h z).ne_zero
  have hch0 : J.conj (h z : K) ≠ 0 := (map_ne_zero J.conj).2 hh0
  rw [nrm_def]
  field_simp at h2 ⊢
  linear_combination h2

omit H [Finite K] in
theorem conj_div_nrm {c : K} (hc : J.conj c = -c) (k : Kˣ) :
    J.conj (c * (J.conj (k : K))⁻¹ * (k : K)⁻¹) = -(c * (J.conj (k : K))⁻¹ * (k : K)⁻¹) := by
  rw [map_mul, map_mul, map_inv₀, map_inv₀, conj_conj, hc]; ring

omit H [Finite K] in
theorem torus_zc (k : Kˣ) {c : K} (hc : J.conj c = -c) :
    hermitianTorusAction J k (zc c hc) =
      zc (c * (J.conj (k : K))⁻¹ * (k : K)⁻¹) (conj_div_nrm hc k) := by
  apply coord_ext
  · rw [torus_fst, zc_fst, zc_fst, zero_mul, zero_mul]
  · rw [torus_snd, zc_snd, zc_snd]

end SMapHyp

end CFSG.UnitaryThreeRecognition.WeylAlg
