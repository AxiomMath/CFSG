module

public import CFSG.Permutation.UnitaryThreeRecognition.DThreeEps
public import CFSG.Permutation.UnitaryThreeRecognition.DThreeFinal

public section

namespace CFSG.UnitaryThreeRecognition.DThree

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

theorem torus_of_one (m : Kˣ) : hermitianTorusAction J m 1 = 1 := by
  apply coord_ext
  · rw [torus_fst]; change (0 : K) * _ * _ = 0; ring
  · rw [torus_snd]; change (0 : K) * _ * _ = 0; ring

theorem torus_inv_torus (m : Kˣ) (x : Coord J) :
    hermitianTorusAction J m⁻¹ (hermitianTorusAction J m x) = x := by
  rw [← torus_mul_apply, inv_mul_cancel, torus_one_apply]

theorem torus_torus_inv (m : Kˣ) (x : Coord J) :
    hermitianTorusAction J m (hermitianTorusAction J m⁻¹ x) = x := by
  rw [← torus_mul_apply, mul_inv_cancel, torus_one_apply]

theorem torus_ne_one {m : Kˣ} {x : Coord J} (hx : x ≠ 1) : hermitianTorusAction J m x ≠ 1 := by
  intro e
  apply hx
  rw [← torus_inv_torus m x, e, torus_of_one]

variable {q : ℕ} {F : Coord J → Coord J} {σ : Kˣ → Kˣ} {h : Coord J → Kˣ}

namespace SMapHyp3

variable (H : SMapHyp3 J q F σ h)
include H

theorem F_inj {c c' : Coord J} (hc : c ≠ 1) (hc' : c' ≠ 1) (e : F c = F c') : c = c' := by
  rw [← H.F_F c hc, ← H.F_F c' hc', e]

theorem F_jm {c : Coord J} (hc : c ≠ 1) :
    F (hermitianTorusAction J (-1) c) = hermitianTorusAction J (-1) (F c) := by
  rw [H.F_torus (-1) c hc, H.t_sigma', cj_neg_one, inv_neg_one]

theorem fix_moufang {u v : Coord J} (hu : u ≠ 1) (hFu : F u = u) (hv : v ≠ 1) (hvu : v ≠ u⁻¹) :
    F (u * v) = u * F (F u⁻¹ * hermitianTorusAction J (-1) (F v)) := by
  have hui : u⁻¹ ≠ 1 := inv_ne_one.mpr hu
  have hFv1 : F v ≠ 1 := H.F_ne v hv
  have hne1 : u * F (F v) ≠ 1 := by
    rw [H.F_F v hv]; intro e; exact hvu (eq_inv_of_mul_eq_one_right e)
  have hne2 : (F u⁻¹)⁻¹ * F v ≠ 1 := by
    intro e
    have e' : F v = F u⁻¹ := by
      have := eq_inv_of_mul_eq_one_right e; rwa [inv_inv] at this
    exact hvu (H.F_inj hv hui e')
  have e := H.F_moufang u (F v) hu hFv1 hne1 hne2
  rw [H.F_F v hv, hFu, H.fix_tor u hu hFu] at e
  rw [e, ← H.F_jm hne2, torus_mul_hom, H.fix_inv u hu hFu]

theorem core_conj {κ μ : K} (hκc : J.conj κ = κ)
    (hκF : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → (F z).1.1 = 0 ∧ (F z).1.2 * z.1.2 = κ)
    (hμ0 : μ ≠ 0) (hμμ : μ * μ = κ)
    (hμh : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → ((h z : K) * μ / z.1.2) ^ 3 = 1)
    (k₀ : Kˣ) (hk₀ : (k₀ : K) * J.conj (k₀ : K) = μ) :
    Core J q (fun c => hermitianTorusAction J k₀ (F (hermitianTorusAction J k₀⁻¹ c))) where
  card := H.card
  conj_pow := H.conj_pow
  q_odd := H.q_odd
  q_ge := H.q_ge
  three_ne := H.three_ne
  F_ne c hc := torus_ne_one (H.F_ne _ (torus_ne_one hc))
  F_F c hc := by
    rw [torus_inv_torus, H.F_F _ (torus_ne_one hc), torus_torus_inv]
  F_torus k c hc := by
    rw [torus_comm k₀⁻¹ k, H.F_torus k _ (torus_ne_one hc), H.t_sigma', torus_comm]
  F_Z z hz hz0 := by
    have hk := k₀.ne_zero
    have hck : J.conj (k₀ : K) ≠ 0 := (map_ne_zero J.conj).2 hk
    have hz' : hermitianTorusAction J k₀⁻¹ z ≠ 1 := torus_ne_one hz
    have hz'0 : (hermitianTorusAction J k₀⁻¹ z).1.1 = 0 := t_central hz0 _
    obtain ⟨h1, h2⟩ := hκF _ hz' hz'0
    have hb := coord_snd_ne_zero J hz
    refine ⟨t_central h1 _, ?_⟩
    rw [torus_snd]
    rw [torus_snd, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, inv_inv] at h2
    rw [← hμμ, ← hk₀] at h2
    field_simp at h2 ⊢
    linear_combination h2
  F_zm z w hz hz0 hw := by
    have hk := k₀.ne_zero
    have hck : J.conj (k₀ : K) ≠ 0 := (map_ne_zero J.conj).2 hk
    set z' := hermitianTorusAction J k₀⁻¹ z with hz'def
    set w' := hermitianTorusAction J k₀⁻¹ w with hw'def
    have hz' : z' ≠ 1 := torus_ne_one hz
    have hz'0 : z'.1.1 = 0 := t_central hz0 _
    have hw'0 : w'.1.1 ≠ 0 := by
      rw [hw'def, torus_fst]
      exact mul_ne_zero (mul_ne_zero hw (Units.ne_zero _))
        (pow_ne_zero _ (inv_ne_zero ((map_ne_zero J.conj).2 (Units.ne_zero _))))
    have hw' : w' ≠ 1 := ne_one_of_fst hw'0
    have hFz'0 : (F z').1.1 = 0 := (hκF z' hz' hz'0).1
    have hrz := F_inv_inv_center hκc hκF hz' hz'0
    have hne1 : z' * F w' ≠ 1 := by
      have : (z' * w').1.1 ≠ 0 := by rw [central_comm hz'0, mul_central_fst _ hz'0]; exact hw'0
      intro e
      have hFw'0 : (F w').1.1 ≠ 0 := by
        intro h0
        have := (hκF _ (H.F_ne w' hw') h0).1
        rw [H.F_F w' hw'] at this
        exact hw'0 this
      have : (z' * F w').1.1 ≠ 0 := by
        rw [central_comm hz'0, mul_central_fst _ hz'0]; exact hFw'0
      exact this (by rw [e]; rfl)
    have hne2 : (F z'⁻¹)⁻¹ * w' ≠ 1 := by
      rw [hrz]; apply ne_one_of_fst
      rw [central_comm hFz'0, mul_central_fst _ hFz'0]; exact hw'0
    have e := H.F_moufang z' w' hz' hw' hne1 hne2
    rw [hrz] at e
    have L : hermitianTorusAction J k₀⁻¹
        (z * hermitianTorusAction J k₀ (F (hermitianTorusAction J k₀⁻¹ w))) = z' * F w' := by
      rw [torus_mul_hom, torus_inv_torus]
    have R : hermitianTorusAction J k₀⁻¹ (hermitianTorusAction J k₀ (F z') * w) = F z' * w' := by
      rw [torus_mul_hom, torus_inv_torus]
    have hz'2 : z'.1.2 = z.1.2 * μ := by
      rw [hz'def, torus_snd, Units.val_inv_eq_inv_val, map_inv₀, inv_inv, inv_inv, ← hk₀]; ring
    have hb := coord_snd_ne_zero J hz
    have hrel : ∀ Y : Coord J, hermitianTorusAction J (h z') Y =
        hermitianTorusAction J (Units.mk0 z.1.2 (coord_snd_ne_zero J hz)) Y := by
      have hcube := hμh z' hz' hz'0
      rw [hz'2] at hcube
      apply (H.t_eq_iff _ _).mpr
      rw [Units.val_mk0]
      have : (h z' : K) * μ / (z.1.2 * μ) = (h z' : K) / z.1.2 := by field_simp
      rw [← this]; exact hcube
    rw [L, R, e, torus_mul_hom]
    congr 1
    rw [torus_comm k₀ (h z'), hrel]
  F_fix u v hu hFu hv hvu := by
    have hk := k₀.ne_zero
    set u' := hermitianTorusAction J k₀⁻¹ u with hu'def
    have hu'1 : u' ≠ 1 := torus_ne_one (ne_one_of_fst hu)
    have hFu' : F u' = u' := by
      have := congrArg (hermitianTorusAction J k₀⁻¹) hFu
      rwa [torus_inv_torus] at this
    have hv' : hermitianTorusAction J k₀⁻¹ v ≠ 1 := torus_ne_one hv
    have hvu' : hermitianTorusAction J k₀⁻¹ v ≠ u'⁻¹ := by
      intro e; apply hvu
      have := congrArg (hermitianTorusAction J k₀) e
      rwa [torus_torus_inv, torus_inv_hom, hu'def, torus_torus_inv] at this
    have e := H.fix_moufang hu'1 hFu' hv' hvu'
    rw [torus_mul_hom, ← hu'def, e, torus_mul_hom, hu'def, torus_torus_inv, ← hu'def]
    congr 2
    rw [torus_mul_hom, torus_inv_hom, torus_inv_torus, ← hu'def, torus_comm, torus_inv_torus,
      ← torus_inv_hom]
  F_fix_inv u hu hFu := by
    set u' := hermitianTorusAction J k₀⁻¹ u with hu'def
    have hu'1 : u' ≠ 1 := torus_ne_one (ne_one_of_fst hu)
    have hFu' : F u' = u' := by
      have := congrArg (hermitianTorusAction J k₀⁻¹) hFu
      rwa [torus_inv_torus] at this
    have hi := H.fix_inv u' hu'1 hFu'
    have hi' : hermitianTorusAction J (-1) (F u'⁻¹) = (F u'⁻¹)⁻¹ := by
      have := congrArg (·⁻¹) hi
      rwa [← torus_inv_hom, inv_inv] at this
    have hu' : hermitianTorusAction J k₀⁻¹ u⁻¹ = u'⁻¹ := by rw [torus_inv_hom]
    rw [hu', torus_comm (-1) k₀, hi', torus_inv_hom]
  fix_exists := by
    obtain ⟨u₀, hu₀, hFu₀⟩ := H.fix_exists'
    refine ⟨hermitianTorusAction J k₀ u₀, ?_, ?_⟩
    · rw [torus_fst]
      exact mul_ne_zero (mul_ne_zero hu₀ k₀.ne_zero)
        (pow_ne_zero _ (inv_ne_zero ((map_ne_zero J.conj).2 k₀.ne_zero)))
    · rw [torus_inv_torus, hFu₀]

theorem exists_weyl_normalization :
    ∃ k₀ : Kˣ, ∀ c : Coord J, c ≠ 1 →
      hermitianTorusAction J k₀ (F (hermitianTorusAction J k₀⁻¹ c)) = weylCoord J c := by
  have := H.finite
  obtain ⟨κ, hκ0, hκc, hκF⟩ := H.exists_F_center
  obtain ⟨μ, hμ0, hμc, hμμ, hμh⟩ := H.exists_mu hκ0 hκc hκF
  obtain ⟨k₀, hk₀⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega) hμ0 hμc
  exact ⟨k₀, fun c hc => (H.core_conj hκc hκF hμ0 hμμ hμh k₀ hk₀).eq_weyl hc⟩

end SMapHyp3

end CFSG.UnitaryThreeRecognition.DThree
