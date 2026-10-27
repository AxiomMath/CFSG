module

public import CFSG.Permutation.UnitaryThreeRecognition.DThreeLine

public section

namespace CFSG.UnitaryThreeRecognition.DThree

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K} {q : ℕ} {F : Coord J → Coord J}

namespace Core

variable (H : Core J q F)
include H

theorem exists_fixed_over [Finite K] {A : K} (hA : A ≠ 0) :
    ∃ (m : Kˣ) (v : Coord J), v.1.1 ≠ 0 ∧ F v = v ∧ (hermitianTorusAction J m v).1.1 = A := by
  have h2 := H.two_ne
  obtain ⟨u₀, hu₀, hF₀⟩ := H.fix_exists
  set y := A / u₀.1.1 with hydef
  have hy : y ≠ 0 := div_ne_zero hA hu₀
  set y₁ := (y + J.conj y) / 2 with hy₁
  set y₂ := (y - J.conj y) / 2 with hy₂
  have hyy : y = y₁ + y₂ := by rw [hy₁, hy₂]; field_simp; ring
  have hcy₁ : J.conj y₁ = y₁ := by rw [hy₁, map_div₀, map_add, conj_conj, map_ofNat]; ring
  have hcy₂ : J.conj y₂ = -y₂ := by rw [hy₂, map_div₀, map_sub, conj_conj, map_ofNat]; ring
  by_cases hsq : y₁ = 0 ∨ y₂ = 0
  ·
    have hcy2 : J.conj y ^ 2 = y ^ 2 := by
      rcases hsq with h | h
      · have : J.conj y = -y := by
          have e := hyy; rw [h, zero_add] at e; rw [e, hcy₂]
        rw [this, neg_sq]
      · have : J.conj y = y := by
          have e := hyy; rw [h, add_zero] at e; rw [e, hcy₁]
        rw [this]
    refine ⟨Units.mk0 y⁻¹ (inv_ne_zero hy), u₀, hu₀, hF₀, ?_⟩
    have hcy : J.conj y ≠ 0 := (map_ne_zero J.conj).2 hy
    rw [torus_fst, Units.val_mk0, map_inv₀, inv_inv, hcy2, hydef]
    field_simp
  · push Not at hsq
    obtain ⟨h₁, h₂⟩ := hsq
    set c := -y₂ / y₁ with hcdef
    have hc0 : c ≠ 0 := div_ne_zero (neg_ne_zero.mpr h₂) h₁
    have hcc : J.conj c = -c := by rw [hcdef, map_div₀, map_neg, hcy₂, hcy₁]; ring
    set z : Coord J := zc c hcc with hzdef
    have hz : z.1.1 = 0 := rfl
    have hz2 : z.1.2 = c := rfl
    have hz1 : z ≠ 1 := fun e => hc0 (congrArg (fun v : Coord J => v.1.2) e)
    have h1c : 1 - c ^ 2 ≠ 0 := by
      intro e
      have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination -e
      have hreal : J.conj c = c := by
        rcases mul_eq_zero.mp hc2 with h | h
        · have : c = 1 := by linear_combination h
          rw [this, map_one]
        · have : c = -1 := by linear_combination h
          rw [this, map_neg, map_one]
      rw [hcc] at hreal
      exact hc0 (by
        have : 2 * c = 0 := by linear_combination -hreal
        exact (mul_eq_zero.mp this).resolve_left h2)
    have hyc : J.conj (1 - c ^ 2)⁻¹ = (1 - c ^ 2)⁻¹ := by
      rw [map_inv₀, map_sub, map_one, map_pow, hcc, neg_sq]
    obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega)
      (inv_ne_zero h1c) hyc
    have hk' : (k : K) * J.conj (k : K) * (1 - z.1.2 ^ 2) = 1 := by
      rw [hz2, ← nrm_def, hk]; field_simp
    have hfix := H.fix_torus hu₀ hF₀ hz1 hz hk'
    have hVa := (H.vl hu₀ hF₀ hz1 hz).1
    rw [hz2] at hVa
    have hzu : z * u₀ = u₀ * z := central_comm hz u₀
    have hG : (F (u₀ * z)).1.1 ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hVa; exact hu₀ hVa.symm
    have hk0 : (k : K) ≠ 0 := k.ne_zero
    have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
    set lam := y₁ * (1 - c ^ 2) with hlam
    have hlam0 : lam ≠ 0 := mul_ne_zero h₁ h1c
    have hclam : J.conj lam = lam := by
      rw [hlam, map_mul, hcy₁, map_sub, map_one, map_pow, hcc, neg_sq]
    refine ⟨(k * Units.mk0 lam hlam0)⁻¹, z * hermitianTorusAction J k (F (z * u₀)), ?_, hfix, ?_⟩
    · rw [mul_fst, hz, zero_add, torus_fst, hzu]
      exact mul_ne_zero (mul_ne_zero hG hk0) (pow_ne_zero _ (inv_ne_zero hck0))
    · rw [torus_fst, mul_fst, hz, zero_add, torus_fst, hzu, Units.val_inv_eq_inv_val,
        Units.val_mul, Units.val_mk0, map_inv₀, map_mul, hclam, inv_inv]
      have hA' : A = u₀.1.1 * y := by rw [hydef]; field_simp
      rw [hA', hyy, ← hVa]
      have hcy : y₂ = -c * y₁ := by rw [hcdef]; field_simp
      rw [hcy, hlam]
      field_simp
      ring

theorem decomp [Finite K] {P : Coord J} (hP : P.1.1 ≠ 0) :
    ∃ (m : Kˣ) (v z : Coord J), v.1.1 ≠ 0 ∧ F v = v ∧ z.1.1 = 0 ∧
      P = hermitianTorusAction J m (v * z) := by
  obtain ⟨m, v, hv, hFv, hm⟩ := H.exists_fixed_over hP
  refine ⟨m, v, hermitianTorusAction J m⁻¹ ((hermitianTorusAction J m v)⁻¹ * P), hv, hFv, ?_, ?_⟩
  · apply t_central
    rw [mul_fst, inv_fst, hm, neg_add_cancel]
  · rw [torus_mul_hom, ← torus_mul_apply, mul_inv_cancel, torus_one_apply, mul_inv_cancel_left]

theorem eparam [Finite K] {m : Kˣ} {v z : Coord J} (hv : v.1.1 ≠ 0) (hFv : F v = v)
    (hz : z.1.1 = 0) :
    2 * (hermitianTorusAction J m (v * z)).1.2 =
      (z.1.2 - 1) * ((hermitianTorusAction J m (v * z)).1.1 *
        J.conj (hermitianTorusAction J m (v * z)).1.1) := by
  have hb := H.fix_snd hv hFv
  have hn := H.fix_norm hv hFv
  have hm := m.ne_zero
  have hcm : J.conj (m : K) ≠ 0 := (map_ne_zero J.conj).2 hm
  rw [torus_fst, torus_snd, mul_central_fst _ hz, mul_central_snd _ hz, hb, map_mul, map_mul,
    map_pow, map_inv₀, conj_conj]
  have : v.1.1 * (m : K) * (J.conj (m : K))⁻¹ ^ 2 *
      (J.conj v.1.1 * J.conj (m : K) * (m : K)⁻¹ ^ 2) =
      (v.1.1 * J.conj v.1.1) * ((J.conj (m : K))⁻¹ * (m : K)⁻¹) := by
    field_simp
  rw [this, hn]
  ring

theorem eq_weyl_of_decomp [Finite K] {m : Kˣ} {v z : Coord J} (hv : v.1.1 ≠ 0) (hFv : F v = v)
    (hz : z.1.1 = 0) (hpole : 1 + z.1.2 ^ 2 ≠ 0) :
    F (hermitianTorusAction J m (v * z)) = weylCoord J (hermitianTorusAction J m (v * z)) := by
  have hvz1 : v * z ≠ 1 := ne_one_of_fst (by rw [mul_central_fst _ hz]; exact hv)
  rw [H.F_torus m _ hvz1, H.line_weyl hv hFv hz hpole, weylCoord_torus m hvz1]

theorem pole_weyl [Finite K] {v z : Coord J} (hv : v.1.1 ≠ 0) (hFv : F v = v) (hz : z.1.1 = 0)
    (hpole : 1 + z.1.2 ^ 2 = 0) : F (v * z) = weylCoord J (v * z) := by
  have h2 := H.two_ne
  have h3 := H.three_ne
  have hb := H.fix_snd hv hFv
  have hn := H.fix_norm hv hFv
  have hz1 : z ≠ 1 := by
    intro h
    have h0 : z.1.2 = 0 := by rw [h]; rfl
    rw [h0] at hpole
    simp at hpole
  have he0 : z.1.2 ≠ 0 := coord_snd_ne_zero J hz1
  have hec : J.conj z.1.2 = -z.1.2 := conj_snd_of_fst_eq_zero hz
  have he2 : z.1.2 ^ 2 = -1 := by linear_combination hpole
  have hp2e : 1 + 1 * 2 * z.1.2 ≠ 0 := one_add_two_mul_ne hec h2 1 (Or.inl rfl)
  have hm2e : 1 + -1 * 2 * z.1.2 ≠ 0 := one_add_two_mul_ne hec h2 (-1) (Or.inr rfl)
  have hme : J.conj (-z.1.2) = -(-z.1.2) := by rw [map_neg, hec]
  have h2e : J.conj (2 * z.1.2) = -(2 * z.1.2) := by rw [map_mul, map_ofNat, hec]; ring
  obtain ⟨zm, hzm1', hzm2⟩ : ∃ w : Coord J, w.1.1 = 0 ∧ w.1.2 = -z.1.2 := ⟨zc _ hme, rfl, rfl⟩
  obtain ⟨z2, hz21', hz22⟩ : ∃ w : Coord J, w.1.1 = 0 ∧ w.1.2 = 2 * z.1.2 := ⟨zc _ h2e, rfl, rfl⟩
  have hzm1 : zm ≠ 1 := fun h => he0 (by
    have : zm.1.2 = 0 := by rw [h]; rfl
    rw [hzm2] at this; linear_combination -this)
  have hpole2 : 1 + z2.1.2 ^ 2 ≠ 0 := by
    rw [hz22, mul_pow, he2]
    intro h; exact h3 (by linear_combination -h)
  have hw := H.line_weyl hv hFv hz21' hpole2
  have hvz2 : (v * z2).1.1 ≠ 0 := by rw [mul_central_fst _ hz21']; exact hv
  have hvz21 : v * z2 ≠ 1 := ne_one_of_fst hvz2
  have hwa : (F (v * z2)).1.1 * (1 + 1 * 2 * z.1.2) = v.1.1 := by
    rw [hw, weylCoord_fst, mul_central_fst _ hz21', mul_central_snd _ hz21', hb, hz22, map_add,
      map_neg, map_one, map_mul, map_ofNat, hec]
    have hD : -1 + 2 * -z.1.2 ≠ 0 := fun h => hp2e (by linear_combination -h)
    rw [div_mul_eq_mul_div, div_eq_iff hD]; ring
  have hwb : (F (v * z2)).1.2 * (2 * z.1.2 - 1) = 1 := by
    rw [hw, weylCoord_snd, mul_central_snd _ hz21', hb, hz22]
    have : -1 + 2 * z.1.2 ≠ 0 := fun h => hm2e (by linear_combination -h)
    field_simp; ring
  have hwfst : (F (v * z2)).1.1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hwa; exact hv hwa.symm
  have e1 := H.F_zm zm (F (v * z2)) hzm1 hzm1' hwfst
  rw [H.F_F _ hvz21] at e1
  have e2 : zm * (v * z2) = v * z := by
    apply coord_ext
    · rw [mul_fst, mul_central_fst _ hz21', mul_central_fst _ hz, hzm1', zero_add]
    · rw [central_comm hzm1', mul_central_snd _ hzm1', mul_central_snd _ hz21',
        mul_central_snd _ hz, hzm2, hz22]; ring
  rw [e2] at e1
  obtain ⟨hFzm1, hFzm2⟩ := H.F_Z zm hzm1 hzm1'
  rw [hzm2] at hFzm2
  have hFzm2' : (F zm).1.2 = z.1.2 := by
    rw [hFzm2]
    field_simp
    linear_combination -he2
  set P' := F zm * F (v * z2) with hP'def
  have hP'1 : P'.1.1 = (F (v * z2)).1.1 := by rw [hP'def, mul_fst, hFzm1, zero_add]
  have hP'2 : P'.1.2 = z.1.2 + (F (v * z2)).1.2 := by
    rw [hP'def, central_comm hFzm1, mul_central_snd _ hFzm1, hFzm2', add_comm]
  have hP'a : P'.1.1 ≠ 0 := by rw [hP'1]; exact hwfst
  obtain ⟨m, v', z', hv', hFv', hz', hdec⟩ := H.decomp hP'a
  have hE := H.eparam (m := m) hv' hFv' hz'
  rw [← hdec, hP'1, hP'2] at hE
  have hcwa := congrArg J.conj hwa
  rw [map_mul, map_add, map_one, map_mul, map_mul, map_one, map_ofNat, hec] at hcwa
  have hN₂ : (F (v * z2)).1.1 * J.conj (F (v * z2)).1.1 *
      ((1 + 1 * 2 * z.1.2) * (1 + 1 * 2 * -z.1.2)) = 2 := by
    linear_combination (J.conj (F (v * z2)).1.1 * (1 + 1 * 2 * -z.1.2)) * hwa +
      v.1.1 * hcwa + hn
  have hz'3 : 2 * (z'.1.2 - 3 * z.1.2) = 0 := by
    linear_combination -((1 + 1 * 2 * z.1.2) * (1 + 1 * 2 * -z.1.2)) * hE -
      (z'.1.2 - 1) * hN₂ - 2 * (1 + 2 * z.1.2) * hwb - 8 * z.1.2 * he2
  have hz'e : z'.1.2 = 3 * z.1.2 := by
    have := (mul_eq_zero.mp hz'3).resolve_left h2; linear_combination this
  have hpole' : 1 + z'.1.2 ^ 2 ≠ 0 := by
    rw [hz'e, mul_pow, he2]
    intro h
    have h8 : (2 : K) * (2 * 2) = 0 := by linear_combination -h
    exact mul_ne_zero h2 (mul_ne_zero h2 h2) h8
  have hFP' : F P' = weylCoord J P' := by
    rw [hdec]; exact H.eq_weyl_of_decomp hv' hFv' hz' hpole'
  rw [hFP'] at e1
  have hP'2ne : P'.1.2 ≠ 0 := by
    have : (P' : Coord J) ≠ 1 := ne_one_of_fst hP'a
    exact coord_snd_ne_zero J this
  have hcP'2ne : J.conj P'.1.2 ≠ 0 := (map_ne_zero J.conj).2 hP'2ne
  have hP'rel : P'.1.2 * (2 * z.1.2 - 1) = -1 - z.1.2 := by
    rw [hP'2]; linear_combination hwb + 2 * he2
  have hcP'rel : J.conj P'.1.2 * (-2 * z.1.2 - 1) = z.1.2 - 1 := by
    have := congrArg J.conj hP'rel
    rw [map_mul, map_sub, map_mul, map_ofNat, hec, map_one, map_sub, map_neg, map_one, hec] at this
    linear_combination this
  set Y := hermitianTorusAction J (Units.mk0 zm.1.2 (coord_snd_ne_zero J hzm1)) (weylCoord J P')
    with hYdef
  have hm0 : zm.1.2 ≠ 0 := coord_snd_ne_zero J hzm1
  have hmc : J.conj zm.1.2 = -zm.1.2 := conj_snd_of_fst_eq_zero hzm1'
  have hYa := t_trace_fst hm0 hmc (weylCoord J P')
  have hYb := t_trace_snd hm0 hmc (weylCoord J P')
  rw [← hYdef, weylCoord_fst, hzm2, hP'1] at hYa
  rw [← hYdef, weylCoord_snd, hzm2, neg_sq, he2] at hYb
  have hYa' : Y.1.1 * (-z.1.2) * J.conj P'.1.2 = -(F (v * z2)).1.1 := by
    rw [hYa]; field_simp
  have hY1 : Y.1.1 * (1 + z.1.2) = v.1.1 := by
    linear_combination (-2 * z.1.2 - 1) * hYa' + Y.1.1 * z.1.2 * hcP'rel + hwa + Y.1.1 * he2
  have hYP : Y.1.2 * P'.1.2 = 1 := by
    have : Y.1.2 = (P'.1.2)⁻¹ := by linear_combination -hYb
    rw [this, inv_mul_cancel₀ hP'2ne]
  have hY2' : Y.1.2 * (-1 - z.1.2) = 2 * z.1.2 - 1 := by
    linear_combination (2 * z.1.2 - 1) * hYP - Y.1.2 * hP'rel
  rw [e1]
  have hFzm_c : (F zm).1.1 = 0 := hFzm1
  apply coord_ext
  · rw [mul_fst, hFzm_c, zero_add, weylCoord_fst, mul_central_fst _ hz, mul_central_snd _ hz, hb,
      map_add, map_neg, map_one, hec]
    have hden : -1 + -z.1.2 ≠ 0 := by
      intro h
      have := one_add_two_mul_ne hec h2 1 (Or.inl rfl)
      have h' : 1 + z.1.2 = 0 := by linear_combination -h
      have hc' := congrArg J.conj h'
      rw [map_add, map_one, hec, map_zero] at hc'
      exact h2 (by linear_combination h' + hc')
    rw [eq_div_iff hden]
    linear_combination -hY1
  · rw [central_comm hFzm_c, mul_central_snd _ hFzm_c, hFzm2', weylCoord_snd, mul_central_snd _ hz,
      hb]
    have h1e : -1 - z.1.2 ≠ 0 := by
      intro h
      have h' : 1 + z.1.2 = 0 := by linear_combination -h
      have hc' := congrArg J.conj h'
      rw [map_add, map_one, hec, map_zero] at hc'
      exact h2 (by linear_combination h' + hc')
    have hgoal : (-1 - z.1.2) * ((Y.1.2 + z.1.2) * (-1 + z.1.2) - 1) = 0 := by
      linear_combination (-1 + z.1.2) * hY2' + (2 - z.1.2) * he2
    have h3' : (Y.1.2 + z.1.2) * (-1 + z.1.2) = 1 := by
      have := (mul_eq_zero.mp hgoal).resolve_left h1e
      linear_combination this
    exact eq_inv_of_mul_eq_one_left h3'

theorem eq_weyl [Finite K] {c : Coord J} (hc : c ≠ 1) : F c = weylCoord J c := by
  by_cases hc1 : c.1.1 = 0
  · obtain ⟨h1, h2⟩ := H.F_Z c hc hc1
    apply coord_ext
    · rw [h1, weylCoord_fst, hc1, neg_zero, zero_div]
    · rw [h2, weylCoord_snd]
  · obtain ⟨m, v, z, hv, hFv, hz, rfl⟩ := H.decomp hc1
    by_cases hpole : 1 + z.1.2 ^ 2 = 0
    · have hvz1 : v * z ≠ 1 := ne_one_of_fst (by rw [mul_central_fst _ hz]; exact hv)
      rw [H.F_torus m _ hvz1, H.pole_weyl hv hFv hz hpole, weylCoord_torus m hvz1]
    · exact H.eq_weyl_of_decomp hv hFv hz hpole

end Core

end CFSG.UnitaryThreeRecognition.DThree
