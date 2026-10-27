module

public import CFSG.Permutation.UnitaryThreeRecognition.BridgeTorus

public section

namespace CFSG.UnitaryThreeRecognition.DThree

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K}

variable (J) in
abbrev cj (k : Kˣ) : Kˣ := Units.map J.conj.toMonoidHom k

theorem cj_val (k : Kˣ) : ((cj J k : Kˣ) : K) = J.conj (k : K) := rfl

theorem cj_of_conj_eq {k : Kˣ} (h : J.conj (k : K) = k) : cj J k = k := Units.ext h

theorem cj_neg_one : cj J (-1) = -1 := Units.ext (by simp)

variable (J) in
structure Core (q : ℕ) (F : Coord J → Coord J) : Prop where
  card : Nat.card K = q ^ 2
  conj_pow : ∀ x, J.conj x = x ^ q
  q_odd : Odd q
  q_ge : 5 ≤ q
  three_ne : (3 : K) ≠ 0
  F_ne : ∀ c, c ≠ 1 → F c ≠ 1
  F_F : ∀ c, c ≠ 1 → F (F c) = c
  F_torus : ∀ (k : Kˣ) (c : Coord J), c ≠ 1 →
    F (hermitianTorusAction J k c) = hermitianTorusAction J (cj J k)⁻¹ (F c)
  F_Z : ∀ z : Coord J, z ≠ 1 → z.1.1 = 0 → (F z).1.1 = 0 ∧ (F z).1.2 = (z.1.2)⁻¹
  F_zm : ∀ (z w : Coord J) (hz : z ≠ 1), z.1.1 = 0 → w.1.1 ≠ 0 →
    F (z * F w) =
      F z * hermitianTorusAction J (Units.mk0 z.1.2 (coord_snd_ne_zero J hz)) (F (F z * w))
  F_fix : ∀ u v : Coord J, u.1.1 ≠ 0 → F u = u → v ≠ 1 → v ≠ u⁻¹ →
    F (u * v) = u * F (F u⁻¹ * hermitianTorusAction J (-1) (F v))
  F_fix_inv : ∀ u : Coord J, u.1.1 ≠ 0 → F u = u →
    hermitianTorusAction J (-1) (F u⁻¹) = (F u⁻¹)⁻¹
  fix_exists : ∃ u : Coord J, u.1.1 ≠ 0 ∧ F u = u

theorem jm_fst (z : Coord J) : (hermitianTorusAction J (-1) z).1.1 = -z.1.1 := by
  rw [torus_fst]; simp

theorem jm_snd (z : Coord J) : (hermitianTorusAction J (-1) z).1.2 = z.1.2 := by
  rw [torus_snd]; simp

theorem ne_one_of_fst {z : Coord J} (hz : z.1.1 ≠ 0) : z ≠ 1 := by
  rintro rfl; exact hz rfl

theorem jm_jm (z : Coord J) :
    hermitianTorusAction J (-1) (hermitianTorusAction J (-1) z) = z := by
  rw [← torus_mul_apply, neg_one_mul, neg_neg, torus_one_apply]

theorem central_comm {z : Coord J} (hz : z.1.1 = 0) (w : Coord J) : z * w = w * z := by
  apply coord_ext
  · rw [mul_fst, mul_fst, hz]; ring
  · rw [mul_snd, mul_snd, hz, map_zero]; ring

theorem mul_central_fst (w : Coord J) {z : Coord J} (hz : z.1.1 = 0) : (w * z).1.1 = w.1.1 := by
  rw [mul_fst, hz, add_zero]

theorem mul_central_snd (w : Coord J) {z : Coord J} (hz : z.1.1 = 0) :
    (w * z).1.2 = w.1.2 + z.1.2 := by
  rw [mul_snd, hz, map_zero, mul_zero, sub_zero]

theorem inv_eq_jm {u : Coord J} (hu : J.conj u.1.2 = u.1.2) :
    u⁻¹ = hermitianTorusAction J (-1) u := by
  apply coord_ext
  · rw [inv_fst, jm_fst]
  · rw [inv_snd, jm_snd, hu]

theorem t_trace_fst {c : K} (hc0 : c ≠ 0) (hc : J.conj c = -c) (X : Coord J) :
    (hermitianTorusAction J (Units.mk0 c hc0) X).1.1 * c = X.1.1 := by
  rw [torus_fst, Units.val_mk0, hc]; field_simp

theorem t_trace_snd {c : K} (hc0 : c ≠ 0) (hc : J.conj c = -c) (X : Coord J) :
    (hermitianTorusAction J (Units.mk0 c hc0) X).1.2 * c ^ 2 = -X.1.2 := by
  rw [torus_snd, Units.val_mk0, hc]; field_simp

theorem t_central {z : Coord J} (hz : z.1.1 = 0) (k : Kˣ) :
    (hermitianTorusAction J k z).1.1 = 0 := by
  rw [torus_fst, hz, zero_mul, zero_mul]

theorem cj_cj (k : Kˣ) : cj J (cj J k) = k := Units.ext (by simp)

theorem cj_inv_cj_inv (k : Kˣ) : (cj J (cj J k)⁻¹)⁻¹ = k :=
  Units.ext (by simp)

theorem t_icj_fst (k : Kˣ) (X : Coord J) :
    (hermitianTorusAction J (cj J k)⁻¹ X).1.1 = X.1.1 * (J.conj (k : K))⁻¹ * (k : K) ^ 2 := by
  rw [torus_fst, Units.val_inv_eq_inv_val, cj_val, map_inv₀, conj_conj, inv_inv]

theorem t_icj_snd (k : Kˣ) (X : Coord J) :
    (hermitianTorusAction J (cj J k)⁻¹ X).1.2 = X.1.2 * ((k : K) * J.conj (k : K)) := by
  rw [torus_snd, Units.val_inv_eq_inv_val, cj_val, map_inv₀, conj_conj, inv_inv, inv_inv]; ring

theorem torus_comm (k m : Kˣ) (z : Coord J) :
    hermitianTorusAction J k (hermitianTorusAction J m z) =
      hermitianTorusAction J m (hermitianTorusAction J k z) := by
  rw [← torus_mul_apply, ← torus_mul_apply, mul_comm]

theorem t_snd_central {z : Coord J} (k : Kˣ) :
    (hermitianTorusAction J k z).1.2 * ((k : K) * J.conj (k : K)) = z.1.2 := by
  have hk := k.ne_zero
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  rw [torus_snd]; field_simp

theorem weylCoord_fst (z : Coord J) : (weylCoord J z).1.1 = -z.1.1 / J.conj z.1.2 :=
  congrArg Prod.fst (weylCoord_val J z)

theorem weylCoord_snd (z : Coord J) : (weylCoord J z).1.2 = (z.1.2)⁻¹ :=
  congrArg Prod.snd (weylCoord_val J z)

theorem weylCoord_torus (k : Kˣ) {z : Coord J} (hz : z ≠ 1) :
    weylCoord J (hermitianTorusAction J k z) =
      hermitianTorusAction J (cj J k)⁻¹ (weylCoord J z) := by
  have hk := k.ne_zero
  have hck : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk
  have hb := coord_snd_ne_zero J hz
  have hcb : J.conj z.1.2 ≠ 0 := (map_ne_zero J.conj).2 hb
  apply coord_ext
  · rw [weylCoord_fst, t_icj_fst, weylCoord_fst, torus_fst, torus_snd, map_mul, map_mul, map_inv₀,
      map_inv₀, conj_conj]
    field_simp
  · rw [weylCoord_snd, t_icj_snd, weylCoord_snd, torus_snd]
    field_simp

theorem one_add_two_mul_ne {e : K} (he : J.conj e = -e) (h2 : (2 : K) ≠ 0) (s : K)
    (hs : s = 1 ∨ s = -1) : 1 + s * 2 * e ≠ 0 := by
  intro h
  have h' : J.conj (1 + s * 2 * e) = 0 := by rw [h, map_zero]
  have hcs : J.conj s = s := by rcases hs with rfl | rfl <;> simp
  rw [map_add, map_one, map_mul, map_mul, hcs, map_ofNat, he] at h'
  exact h2 (by linear_combination h + h')

variable {q : ℕ} {F : Coord J → Coord J}

namespace Core

variable (H : Core J q F)
include H

theorem two_ne : (2 : K) ≠ 0 := by
  classical
  intro h2
  have hfin : Finite K := by
    apply Nat.finite_of_card_ne_zero
    rw [H.card]; have := H.q_ge; positivity
  have : Fintype K := Fintype.ofFinite K
  have hchar : ringChar K = 2 := by
    have := ringChar.dvd (show ((2 : ℕ) : K) = 0 by exact_mod_cast h2)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h | h
    · exact absurd h (CharP.ringChar_ne_one)
    · exact h
  obtain ⟨n, -, hn⟩ := FiniteField.card K (ringChar K)
  rw [← Nat.card_eq_fintype_card, H.card, hchar] at hn
  have hev : Even (q ^ 2) := by rw [hn]; exact (Nat.even_pow.mpr ⟨even_two, n.ne_zero⟩)
  exact (Nat.not_even_iff_odd.mpr (H.q_odd.pow)) hev

theorem F_inj {c c' : Coord J} (hc : c ≠ 1) (hc' : c' ≠ 1) (e : F c = F c') : c = c' := by
  rw [← H.F_F c hc, ← H.F_F c' hc', e]

theorem F_jm {c : Coord J} (hc : c ≠ 1) :
    F (hermitianTorusAction J (-1) c) = hermitianTorusAction J (-1) (F c) := by
  rw [H.F_torus (-1) c hc, cj_neg_one, inv_neg_one]

@[expose] noncomputable def u2 : Kˣ := Units.mk0 2 H.two_ne

theorem u2_val : ((H.u2 : Kˣ) : K) = 2 := rfl

theorem cj_u2 : cj J H.u2 = H.u2 := cj_of_conj_eq (by rw [u2_val, map_ofNat])

theorem four_ne : (4 : K) ≠ 0 := by
  have h := mul_ne_zero H.two_ne H.two_ne
  norm_num at h ⊢
  exact h

theorem t_half_fst (z : Coord J) : (hermitianTorusAction J H.u2⁻¹ z).1.1 = 2 * z.1.1 := by
  have := H.two_ne
  rw [torus_fst, Units.val_inv_eq_inv_val, u2_val, map_inv₀, map_ofNat]; field_simp

theorem t_half_snd (z : Coord J) : (hermitianTorusAction J H.u2⁻¹ z).1.2 = 4 * z.1.2 := by
  have := H.two_ne
  rw [torus_snd, Units.val_inv_eq_inv_val, u2_val, map_inv₀, map_ofNat]; field_simp; ring

theorem t_two_fst (z : Coord J) : 2 * (hermitianTorusAction J H.u2 z).1.1 = z.1.1 := by
  have := H.two_ne
  rw [torus_fst, u2_val, map_ofNat]; field_simp

theorem t_two_snd (z : Coord J) : 4 * (hermitianTorusAction J H.u2 z).1.2 = z.1.2 := by
  have := H.two_ne
  have := H.four_ne
  rw [torus_snd, u2_val, map_ofNat]; field_simp; ring

theorem t_mhalf_fst (z : Coord J) : (hermitianTorusAction J (-H.u2⁻¹) z).1.1 = -2 * z.1.1 := by
  have := H.two_ne
  rw [torus_fst, Units.val_neg, Units.val_inv_eq_inv_val, u2_val, map_neg, map_inv₀, map_ofNat]
  field_simp

theorem t_mhalf_snd (z : Coord J) : (hermitianTorusAction J (-H.u2⁻¹) z).1.2 = 4 * z.1.2 := by
  have := H.two_ne
  rw [torus_snd, Units.val_neg, Units.val_inv_eq_inv_val, u2_val, map_neg, map_inv₀, map_ofNat]
  field_simp; ring

theorem t_mtwo_fst (z : Coord J) : 2 * (hermitianTorusAction J (-H.u2) z).1.1 = -z.1.1 := by
  have := H.two_ne
  rw [torus_fst, Units.val_neg, u2_val, map_neg, map_ofNat]; field_simp

theorem t_mtwo_snd (z : Coord J) : 4 * (hermitianTorusAction J (-H.u2) z).1.2 = z.1.2 := by
  have := H.two_ne
  have := H.four_ne
  rw [torus_snd, Units.val_neg, u2_val, map_neg, map_ofNat]; field_simp; ring

theorem cj_inv_half : (cj J H.u2⁻¹)⁻¹ = H.u2 := by
  rw [show cj J H.u2⁻¹ = (cj J H.u2)⁻¹ from map_inv _ _, inv_inv, H.cj_u2]

theorem cj_inv_mhalf : (cj J (-H.u2⁻¹))⁻¹ = -H.u2 := by
  apply Units.ext
  rw [Units.val_inv_eq_inv_val, cj_val, Units.val_neg, Units.val_neg, Units.val_inv_eq_inv_val,
    u2_val, map_neg, map_inv₀, map_ofNat, inv_neg, inv_inv]

theorem fix_real {u : Coord J} (hu : u.1.1 ≠ 0) (hF : F u = u) :
    J.conj u.1.2 = u.1.2 ∧ F u⁻¹ = u⁻¹ := by
  have h2 := H.two_ne
  have h4 := H.four_ne
  have hu1 : u ≠ 1 := ne_one_of_fst hu
  have hui1 : u⁻¹ ≠ 1 := inv_ne_one.mpr hu1
  have hψ1 : F u⁻¹ ≠ 1 := H.F_ne _ hui1
  have hFψ : F (F u⁻¹) = u⁻¹ := H.F_F _ hui1
  have hjψ : hermitianTorusAction J (-1) (F u⁻¹) = (F u⁻¹)⁻¹ := H.F_fix_inv u hu hF
  have hψb : J.conj (F u⁻¹).1.2 = (F u⁻¹).1.2 := by
    have := congrArg (fun v : Coord J => v.1.2) hjψ
    simp only [jm_snd, inv_snd] at this
    exact this.symm
  have hψrel : 2 * (F u⁻¹).1.2 = -((F u⁻¹).1.1 * J.conj (F u⁻¹).1.1) := by
    have := coord_rel (F u⁻¹); rw [hψb] at this; linear_combination this
  have hurel : u.1.2 + J.conj u.1.2 = -(u.1.1 * J.conj u.1.1) := by
    have := coord_rel u; linear_combination this
  have hju1 : hermitianTorusAction J (-1) u ≠ 1 :=
    ne_one_of_fst (by rw [jm_fst]; exact neg_ne_zero.mpr hu)
  have hFju : F (hermitianTorusAction J (-1) u) = hermitianTorusAction J (-1) u := by
    rw [H.F_jm hu1, hF]
  have hv₁fst : (u⁻¹ * hermitianTorusAction J (-1) u).1.1 = -2 * u.1.1 := by
    rw [mul_fst, inv_fst, jm_fst]; ring
  have hv₁1 : u⁻¹ * hermitianTorusAction J (-1) u ≠ 1 :=
    ne_one_of_fst (by rw [hv₁fst]; exact mul_ne_zero (neg_ne_zero.mpr h2) hu)
  have hv₁u : u⁻¹ * hermitianTorusAction J (-1) u ≠ u⁻¹ := by
    intro e
    apply hju1
    have : u⁻¹ * hermitianTorusAction J (-1) u = u⁻¹ * 1 := by rw [mul_one]; exact e
    exact mul_left_cancel this
  have hX : F u⁻¹ * hermitianTorusAction J (-1) (F (u⁻¹ * hermitianTorusAction J (-1) u)) =
      F (u⁻¹ * hermitianTorusAction J (-1) u) := by
    have e := H.F_fix u _ hu hF hv₁1 hv₁u
    rw [mul_inv_cancel_left, hFju] at e
    have e2 : F (F u⁻¹ * hermitianTorusAction J (-1) (F (u⁻¹ * hermitianTorusAction J (-1) u))) =
        u⁻¹ * hermitianTorusAction J (-1) u := by
      rw [eq_inv_mul_iff_mul_eq]; exact e.symm
    have hne : F u⁻¹ * hermitianTorusAction J (-1) (F (u⁻¹ * hermitianTorusAction J (-1) u)) ≠
        1 := by
      intro e3
      have e4 : hermitianTorusAction J (-1) (F (u⁻¹ * hermitianTorusAction J (-1) u)) =
          (F u⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right e3
      have e5 : F (u⁻¹ * hermitianTorusAction J (-1) u) = F u⁻¹ := by
        have := congrArg (hermitianTorusAction J (-1)) e4
        rw [jm_jm, torus_inv_hom, hjψ, inv_inv] at this
        exact this
      exact hv₁u (H.F_inj hv₁1 hui1 e5)
    rw [← H.F_F _ hne, e2]
  have hA : (F u⁻¹).1.1 = 2 * (F (u⁻¹ * hermitianTorusAction J (-1) u)).1.1 := by
    have := congrArg (fun v : Coord J => v.1.1) hX
    simp only [mul_fst, jm_fst] at this
    linear_combination this
  have hv₂1 : (hermitianTorusAction J (-1) u)⁻¹ ≠ 1 := inv_ne_one.mpr hju1
  have hv₂u : (hermitianTorusAction J (-1) u)⁻¹ ≠ u⁻¹ := by
    intro e
    have e' := inv_injective e
    have := congrArg (fun v : Coord J => v.1.1) e'
    simp only [jm_fst] at this
    have h2x : 2 * u.1.1 = 0 := by linear_combination -this
    exact hu ((mul_eq_zero.mp h2x).resolve_left h2)
  have hFv₂ : F (hermitianTorusAction J (-1) u)⁻¹ = (F u⁻¹)⁻¹ := by
    rw [← torus_inv_hom, H.F_jm hui1, hjψ]
  have h2e : F (u * (hermitianTorusAction J (-1) u)⁻¹) = u * F (F u⁻¹ * F u⁻¹) := by
    rw [H.F_fix u _ hu hF hv₂1 hv₂u, hFv₂, torus_inv_hom, hjψ, inv_inv]
  have h3e : u * (hermitianTorusAction J (-1) u)⁻¹ =
      hermitianTorusAction J (-1) (u⁻¹ * hermitianTorusAction J (-1) u) := by
    apply coord_ext
    · simp only [mul_fst, inv_fst, jm_fst]; ring
    · simp only [mul_snd, inv_snd, inv_fst, jm_fst, jm_snd, map_neg]; ring
  have hF3 : F (u * (hermitianTorusAction J (-1) u)⁻¹) =
      hermitianTorusAction J (-1) (F (u⁻¹ * hermitianTorusAction J (-1) u)) := by
    rw [h3e, H.F_jm hv₁1]
  have h4e : F u⁻¹ * F u⁻¹ = hermitianTorusAction J H.u2⁻¹ (F u⁻¹) := by
    apply coord_ext
    · rw [mul_fst, H.t_half_fst]; ring
    · rw [mul_snd, H.t_half_snd]; linear_combination -hψrel
  have hFψ2 : F (F u⁻¹ * F u⁻¹) = hermitianTorusAction J H.u2 u⁻¹ := by
    rw [h4e, H.F_torus _ _ hψ1, H.cj_inv_half, hFψ]
  have hY : (F u⁻¹).1.1 = -u.1.1 := by
    have e1 := congrArg (fun v : Coord J => v.1.1) h2e
    have e2 := congrArg (fun v : Coord J => v.1.1) hF3
    simp only [mul_fst, hFψ2] at e1
    simp only [jm_fst] at e2
    have e3 := H.t_two_fst u⁻¹
    rw [inv_fst] at e3
    rw [e1] at e2
    linear_combination hA + 2 * e2 - e3
  have h6e : u * (hermitianTorusAction J (-1) u)⁻¹ = hermitianTorusAction J (-H.u2⁻¹) (F u⁻¹) := by
    apply coord_ext
    · rw [mul_fst, H.t_mhalf_fst, hY, inv_fst, jm_fst]; ring
    · rw [mul_snd, H.t_mhalf_snd, inv_snd, inv_fst, jm_snd, jm_fst, neg_neg]
      have hN : (F u⁻¹).1.1 * J.conj (F u⁻¹).1.1 = u.1.1 * J.conj u.1.1 := by
        rw [hY, map_neg]; ring
      linear_combination hurel - 2 * hψrel + 2 * hN
  have hF6 : F (u * (hermitianTorusAction J (-1) u)⁻¹) = hermitianTorusAction J (-H.u2) u⁻¹ := by
    rw [h6e, H.F_torus _ _ hψ1, H.cj_inv_mhalf, hFψ]
  have hb : 2 * u.1.2 = -(u.1.1 * J.conj u.1.1) := by
    have e1 := congrArg (fun v : Coord J => v.1.2) h2e
    have e2 := congrArg (fun v : Coord J => v.1.2) hF6
    simp only [mul_snd, hFψ2] at e1
    rw [e1] at e2
    have hB : (hermitianTorusAction J H.u2 u⁻¹).1.2 = (hermitianTorusAction J (-H.u2) u⁻¹).1.2 :=
      mul_left_cancel₀ h4 ((H.t_two_snd u⁻¹).trans (H.t_mtwo_snd u⁻¹).symm)
    have hA1 := congrArg J.conj (H.t_two_fst u⁻¹)
    rw [map_mul, map_ofNat, inv_fst, map_neg] at hA1
    linear_combination 2 * e2 - 2 * hB + u.1.1 * hA1
  have hbc : J.conj u.1.2 = u.1.2 := by
    have h2b : 2 * J.conj u.1.2 = 2 * u.1.2 := by linear_combination 2 * hurel - 2 * hb
    exact mul_left_cancel₀ h2 h2b
  refine ⟨hbc, ?_⟩
  apply coord_ext
  · rw [hY, inv_fst]
  · rw [inv_snd, hbc]
    have hN : (F u⁻¹).1.1 * J.conj (F u⁻¹).1.1 = u.1.1 * J.conj u.1.1 := by
      rw [hY, map_neg]; ring
    have h2b : 2 * (F u⁻¹).1.2 = 2 * u.1.2 := by linear_combination hψrel - hN - hb
    exact mul_left_cancel₀ h2 h2b

end Core

end CFSG.UnitaryThreeRecognition.DThree
