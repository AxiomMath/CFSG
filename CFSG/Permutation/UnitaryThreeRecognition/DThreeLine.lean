module

public import CFSG.Permutation.UnitaryThreeRecognition.DThreeCore
public import CFSG.Permutation.UnitaryThreeRecognition.WeylAlgMoufang

public section

namespace CFSG.UnitaryThreeRecognition.DThree

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open CFSG.UnitaryThreeRecognition.Model CFSG.UnitaryThreeRecognition.WeylAlg

variable {K : Type*} [Field K] {J : HermitianForm 3 K} {q : ℕ} {F : Coord J → Coord J}

namespace Core

variable (H : Core J q F)
include H

theorem vl {u : Coord J} (hu : u.1.1 ≠ 0) (hF : F u = u) {z : Coord J} (hz1 : z ≠ 1)
    (hz : z.1.1 = 0) :
    (F (u * z)).1.1 * (1 + z.1.2) = u.1.1 ∧
      2 * (1 - z.1.2) * (1 + z.1.2 ^ 2) * (F (u * z)).1.2 =
        2 * z.1.2 * (1 - z.1.2) - u.1.1 * J.conj u.1.1 * (1 + z.1.2) := by
  obtain ⟨hreal, hinv⟩ := H.fix_real hu hF
  have h2 := H.two_ne
  have hu1 : u ≠ 1 := ne_one_of_fst hu
  have he0 : z.1.2 ≠ 0 := coord_snd_ne_zero J hz1
  have hec : J.conj z.1.2 = -z.1.2 := conj_snd_of_fst_eq_zero hz
  obtain ⟨hFz1, hFz2⟩ := H.F_Z z hz1 hz
  have hFz1' : F z ≠ 1 := H.F_ne z hz1
  have huFz : (u * F z).1.1 ≠ 0 := by rw [mul_central_fst u hFz1]; exact hu
  have hFzc : J.conj (F z).1.2 = -(F z).1.2 := conj_snd_of_fst_eq_zero hFz1
  have hFz0 : (F z).1.2 ≠ 0 := coord_snd_ne_zero J hFz1'
  have hi : F (u * z) = u * hermitianTorusAction J (-1) (F (u * F z)) := by
    have hzu : z ≠ u⁻¹ := by
      intro e'; apply hu
      have := congrArg (fun v : Coord J => v.1.1) e'
      simp only [inv_fst, hz] at this
      linear_combination this
    rw [H.F_fix u z hu hF hz1 hzu, hinv, inv_eq_jm hreal, ← H.F_jm (ne_one_of_fst huFz),
      torus_mul_hom]
  have hii : F (u * F z) = z * hermitianTorusAction J (Units.mk0 (F z).1.2 hFz0) (F (u * z)) := by
    have e1 := H.F_zm (F z) u hFz1' hFz1 hu
    rw [hF, H.F_F z hz1, central_comm hFz1 u, central_comm hz u] at e1
    exact e1
  have hcomb : F (u * z) = u * hermitianTorusAction J (-1)
      (z * hermitianTorusAction J (Units.mk0 (F z).1.2 hFz0) (F (u * z))) := by
    conv_lhs => rw [hi]
    rw [hii]
  set X := F (u * z) with hXdef
  set Y := hermitianTorusAction J (Units.mk0 (F z).1.2 hFz0) X with hYdef
  have hY1 := t_trace_fst hFz0 hFzc X
  have hY2 := t_trace_snd hFz0 hFzc X
  rw [← hYdef, hFz2] at hY1 hY2
  have hfst := congrArg (fun v : Coord J => v.1.1) hcomb
  have hsnd := congrArg (fun v : Coord J => v.1.2) hcomb
  simp only [mul_fst, mul_snd, jm_fst, jm_snd, hz, zero_add] at hfst hsnd
  have hYa : Y.1.1 = X.1.1 * z.1.2 := by
    have := hY1; field_simp at this; linear_combination this
  have hYb : Y.1.2 = -(z.1.2 ^ 2 * X.1.2) := by
    have := hY2; field_simp at this; linear_combination this
  rw [hYa] at hfst
  rw [hYa, hYb, map_neg, map_mul, hec] at hsnd
  have hfst' : X.1.1 * (1 + z.1.2) = u.1.1 := by linear_combination hfst
  refine ⟨hfst', ?_⟩
  have hcX : J.conj X.1.1 * (1 - z.1.2) = J.conj u.1.1 := by
    have := congrArg J.conj hfst'
    rw [map_mul, map_add, map_one, hec] at this
    linear_combination this
  have hurel : 2 * u.1.2 = -(u.1.1 * J.conj u.1.1) := by
    have := coord_rel u; rw [hreal] at this; linear_combination this
  linear_combination 2 * (1 - z.1.2) * hsnd + (1 - z.1.2) * hurel - 2 * z.1.2 * u.1.1 * hcX

theorem fix_torus {u : Coord J} (hu : u.1.1 ≠ 0) (hF : F u = u) {z : Coord J} (hz1 : z ≠ 1)
    (hz : z.1.1 = 0) {k : Kˣ} (hk : (k : K) * J.conj (k : K) * (1 - z.1.2 ^ 2) = 1) :
    F (z * hermitianTorusAction J k (F (z * u))) = z * hermitianTorusAction J k (F (z * u)) := by
  have hu1 : u ≠ 1 := ne_one_of_fst hu
  have hzu : (z * u).1.1 ≠ 0 := by rw [central_comm hz, mul_central_fst u hz]; exact hu
  have hzu1 : z * u ≠ 1 := ne_one_of_fst hzu
  obtain ⟨hFz1, hFz2⟩ := H.F_Z z hz1 hz
  have hFz1' : F z ≠ 1 := H.F_ne z hz1
  have he0 : z.1.2 ≠ 0 := coord_snd_ne_zero J hz1
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have hG : (F (z * u)).1.1 ≠ 0 := by
    intro h0
    have := (H.vl hu hF hz1 hz).1
    rw [← central_comm hz, h0, zero_mul] at this
    exact hu this.symm
  set Y := hermitianTorusAction J k (F (z * u)) with hYdef
  have hYa : Y.1.1 ≠ 0 := by
    rw [hYdef, torus_fst]
    exact mul_ne_zero (mul_ne_zero hG hk0) (pow_ne_zero _ (inv_ne_zero hck0))
  have hY1 : Y ≠ 1 := ne_one_of_fst hYa
  have hw : F Y = hermitianTorusAction J (cj J k)⁻¹ (z * u) := by
    rw [hYdef, H.F_torus k _ (H.F_ne _ hzu1), H.F_F _ hzu1]
  have hwa : (F Y).1.1 ≠ 0 := by
    rw [hw, t_icj_fst]
    exact mul_ne_zero (mul_ne_zero hzu (inv_ne_zero hck0)) (pow_ne_zero _ hk0)
  have hFzw : F z * F Y = hermitianTorusAction J (cj J k)⁻¹ (F z * u) := by
    rw [hw, torus_mul_hom, torus_mul_hom, ← mul_assoc]
    congr 1
    apply coord_ext
    · rw [mul_fst, hFz1, t_central hz, t_central hFz1]; ring
    · rw [mul_central_snd _ (t_central hz _), t_icj_snd, t_icj_snd, hFz2]
      field_simp
      linear_combination (-(1 : K)) * hk
  have hFzu : (F z * u).1.1 ≠ 0 := by rw [mul_fst, hFz1, zero_add]; exact hu
  have e1 := H.F_zm z (F Y) hz1 hz hwa
  rw [H.F_F Y hY1, hFzw, H.F_torus _ _ (ne_one_of_fst hFzu), cj_inv_cj_inv] at e1
  have e2 := H.F_zm z u hz1 hz hu
  rw [hF] at e2
  rw [e1, torus_comm]
  have e3 : hermitianTorusAction J (Units.mk0 z.1.2 (coord_snd_ne_zero J hz1)) (F (F z * u)) =
      (F z)⁻¹ * F (z * u) := by rw [e2]; group
  rw [e3, torus_mul_hom, ← mul_assoc]
  congr 1
  apply coord_ext
  · rw [mul_fst, t_central (by rw [inv_fst, hFz1, neg_zero])]; rw [hFz1, hz]; ring
  · rw [mul_central_snd _ (t_central (by rw [inv_fst, hFz1, neg_zero]) _), torus_snd, inv_snd,
      hFz2, map_inv₀, conj_snd_of_fst_eq_zero hz]
    field_simp
    linear_combination hk

theorem exists_trace_zero [Finite K] : ∃ c : K, c ≠ 0 ∧ J.conj c = -c := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hq := H.q_ge
  have hog : orderOf g = q * q - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
      Fintype.card_units, ← Nat.card_eq_fintype_card, H.card, sq]
  have hne : J.conj (g : K) ≠ g := by
    intro e
    rw [H.conj_pow] at e
    have h1 : g ^ (q - 1) = 1 := by
      apply Units.ext
      have h2 : (g : K) ^ (q - 1) * g = g := by
        rw [← pow_succ, Nat.sub_add_cancel (by omega), e]
      simpa using (mul_eq_right₀ g.ne_zero).mp h2
    have h3 := orderOf_le_of_pow_eq_one (by omega) h1
    rw [hog] at h3
    have : q ≤ q * q - q := by
      have : 3 * q ≤ q * q := Nat.mul_le_mul_right q (by omega)
      omega
    omega
  refine ⟨(g : K) - J.conj g, sub_ne_zero.mpr (Ne.symm hne), ?_⟩
  rw [map_sub, conj_conj]; ring

theorem fix_norm [Finite K] {u : Coord J} (hu : u.1.1 ≠ 0) (hF : F u = u) :
    u.1.1 * J.conj u.1.1 = 2 := by
  have h2 := H.two_ne
  obtain ⟨c, hc0, hc⟩ := H.exists_trace_zero
  set z : Coord J := zc c hc with hzdef
  have hz : z.1.1 = 0 := rfl
  have hz2 : z.1.2 = c := rfl
  have hz1 : z ≠ 1 := fun e => hc0 (congrArg (fun v : Coord J => v.1.2) e)
  have hcc : J.conj c * c = -c ^ 2 := by rw [hc]; ring
  have h1c : 1 - c ^ 2 ≠ 0 := by
    intro e
    have hc2 : (c - 1) * (c + 1) = 0 := by linear_combination -e
    have hreal : J.conj c = c := by
      rcases mul_eq_zero.mp hc2 with h | h
      · have : c = 1 := by linear_combination h
        rw [this, map_one]
      · have : c = -1 := by linear_combination h
        rw [this, map_neg, map_one]
    rw [hc] at hreal
    exact hc0 (by
      have : 2 * c = 0 := by linear_combination -hreal
      exact (mul_eq_zero.mp this).resolve_left h2)
  have hyc : J.conj (1 - c ^ 2)⁻¹ = (1 - c ^ 2)⁻¹ := by
    rw [map_inv₀, map_sub, map_one, map_pow, hc, neg_sq]
  obtain ⟨k, hk⟩ := exists_units_nrm_eq J H.card H.conj_pow (by have := H.q_ge; omega)
    (inv_ne_zero h1c) hyc
  have hk0 : (k : K) ≠ 0 := k.ne_zero
  have hck0 : J.conj (k : K) ≠ 0 := (map_ne_zero J.conj).2 hk0
  have hk' : (k : K) * J.conj (k : K) * (1 - z.1.2 ^ 2) = 1 := by
    rw [hz2, ← nrm_def, hk]; field_simp
  have hfix := H.fix_torus hu hF hz1 hz hk'
  have hzu : z * u = u * z := central_comm hz u
  obtain ⟨hVa, hVb⟩ := H.vl hu hF hz1 hz
  rw [hz2] at hVa hVb
  have hGa : (F (u * z)).1.1 ≠ 0 := by
    intro h0; rw [h0, zero_mul] at hVa; exact hu hVa.symm
  have hu₁a : (z * hermitianTorusAction J k (F (z * u))).1.1 ≠ 0 := by
    rw [mul_fst, hz, zero_add, torus_fst, hzu]
    exact mul_ne_zero (mul_ne_zero hGa hk0) (pow_ne_zero _ (inv_ne_zero hck0))
  have hreal := (H.fix_real hu₁a hfix).1
  have hb1 : (z * hermitianTorusAction J k (F (z * u))).1.2 =
      c + (1 - c ^ 2) * (F (u * z)).1.2 := by
    have hN : (k : K) * J.conj (k : K) = (1 - c ^ 2)⁻¹ := hk
    have hN' : (J.conj (k : K))⁻¹ * (k : K)⁻¹ = 1 - c ^ 2 := by
      rw [← mul_inv, mul_comm (J.conj _), hN, inv_inv]
    rw [mul_snd, hz, zero_mul, sub_zero, torus_snd, hzu, hz2, mul_assoc, hN']; ring
  have hconj1 : J.conj (z * hermitianTorusAction J k (F (z * u))).1.2 =
      -c + (1 - c ^ 2) * J.conj (F (u * z)).1.2 := by
    rw [hb1, map_add, map_mul, map_sub, map_one, map_pow, hc, neg_sq]
  have hrelG := coord_rel (F (u * z))
  have hNA : (F (u * z)).1.1 * J.conj (F (u * z)).1.1 * (1 - c ^ 2) =
      u.1.1 * J.conj u.1.1 := by
    have hc' := congrArg J.conj hVa
    rw [map_mul, map_add, map_one, hc] at hc'
    linear_combination (J.conj (F (u * z)).1.1 * (1 - c)) * hVa + u.1.1 * hc'
  have E1 : 2 * (1 - c ^ 2) * (F (u * z)).1.2 + 2 * c + u.1.1 * J.conj u.1.1 = 0 := by
    linear_combination -hb1 + hconj1 - hreal + (1 - c ^ 2) * hrelG - hNA
  have key : 2 * c * (2 - u.1.1 * J.conj u.1.1) = 0 := by
    linear_combination (1 + c ^ 2) * E1 - (1 + c) * hVb
  have h3 : 2 - u.1.1 * J.conj u.1.1 = 0 :=
    (mul_eq_zero.mp key).resolve_left (mul_ne_zero h2 hc0)
  linear_combination -h3

theorem fix_snd [Finite K] {u : Coord J} (hu : u.1.1 ≠ 0) (hF : F u = u) : u.1.2 = -1 := by
  have h2 := H.two_ne
  have hreal := (H.fix_real hu hF).1
  have hn := H.fix_norm hu hF
  have hrel := coord_rel u
  rw [hreal, hn] at hrel
  have : 2 * (u.1.2 + 1) = 0 := by linear_combination hrel
  linear_combination (mul_eq_zero.mp this).resolve_left h2

theorem line_weyl [Finite K] {u : Coord J} (hu : u.1.1 ≠ 0) (hF : F u = u) {z : Coord J}
    (hz : z.1.1 = 0) (hpole : 1 + z.1.2 ^ 2 ≠ 0) : F (u * z) = weylCoord J (u * z) := by
  have h2 := H.two_ne
  have hb := H.fix_snd hu hF
  have hn := H.fix_norm hu hF
  by_cases hz1 : z = 1
  · subst hz1
    rw [mul_one, hF]
    apply coord_ext
    · rw [weylCoord_fst, hb, map_neg, map_one]; ring
    · rw [weylCoord_snd, hb]; norm_num
  obtain ⟨hVa, hVb⟩ := H.vl hu hF hz1 hz
  have hec : J.conj z.1.2 = -z.1.2 := conj_snd_of_fst_eq_zero hz
  have h1e : 1 + z.1.2 ≠ 0 := by
    intro e
    have : J.conj (1 + z.1.2) = 0 := by rw [e, map_zero]
    rw [map_add, map_one, hec] at this
    exact h2 (by linear_combination e + this)
  have h1e' : 1 - z.1.2 ≠ 0 := by
    intro e
    have : J.conj (1 - z.1.2) = 0 := by rw [e, map_zero]
    rw [map_sub, map_one, hec] at this
    exact h2 (by linear_combination e + this)
  have he1 : z.1.2 - 1 ≠ 0 := fun e => h1e' (by linear_combination -e)
  rw [hn] at hVb
  apply coord_ext
  · rw [weylCoord_fst, mul_central_fst _ hz, mul_central_snd _ hz, map_add, hb, hec, map_neg,
      map_one]
    have hm : -1 + -z.1.2 ≠ 0 := fun e => h1e (by linear_combination -e)
    rw [eq_div_iff hm]
    linear_combination -hVa
  · rw [weylCoord_snd, mul_central_snd _ hz, hb]
    have : 2 * (1 - z.1.2) * (1 + z.1.2 ^ 2) * ((F (u * z)).1.2 * (z.1.2 - 1) - 1) = 0 := by
      linear_combination (z.1.2 - 1) * hVb
    have h3 : (F (u * z)).1.2 * (z.1.2 - 1) - 1 = 0 :=
      (mul_eq_zero.mp this).resolve_left (mul_ne_zero (mul_ne_zero h2 h1e') hpole)
    have h4 : -1 + z.1.2 = z.1.2 - 1 := by ring
    rw [h4]
    field_simp
    linear_combination h3

end Core

end CFSG.UnitaryThreeRecognition.DThree
