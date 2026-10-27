module

public import CFSG.LocalAnalysis.StandardType.ZS.OrthClassGenRoot
public import Mathlib.Algebra.Field.ZMod
import CFSG.ClassicalGroups.Orthogonal.RootGroupChar
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.I294CrossThreeOmSevenRefl
import CFSG.ClassicalGroups.Orthogonal.RootGroupCard
import CFSG.ClassicalGroups.Orthogonal.RootGroupNormalizer
import CFSG.ClassicalGroups.Orthogonal.RootGroupPair

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem threeMinus_map_eq {Q : QuadraticForm (ZMod p) U} (P : HypPair Q) {x : U}
    (hx : x ∈ P.perp) (hx0 : Q x ≠ 0) {c lam t : ZMod p} (hlam : lam ≠ 0) (hlam1 : lam ^ 2 ≠ 1)
    (hκ : -(c / Q x) * (1 - lam ^ 2) = t ^ 2) :
    Q (lam • P.e + (c / lam) • P.f) = c ∧ Q (P.e + c • P.f) = c ∧
      Q (P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x) = c := by
  obtain ⟨hex, hfx⟩ := HypPair.mem_perp.mp hx
  have h1 : (1 : ZMod p) - lam ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm hlam1)
  have hQ2 : ∀ s r : ZMod p, Q (s • P.e + r • P.f) = s * r := by
    intro s r
    rw [QuadraticMap.map_add Q, map_smul_eq_sq, map_smul_eq_sq, P.Q_e, P.Q_f,
      polar_smul_left_eq, polar_smul_right_eq, P.polar_ef]
    ring
  have hQ3 : ∀ s r w : ZMod p, Q (s • P.e + r • P.f + w • x) = s * r + w ^ 2 * Q x := by
    intro s r w
    rw [QuadraticMap.map_add Q, hQ2, map_smul_eq_sq, polar_add_left, polar_smul_left_eq,
      polar_smul_left_eq, polar_smul_right_eq, polar_smul_right_eq, hex, hfx]
    ring
  refine ⟨by rw [hQ2]; field_simp [hlam], by simpa using hQ2 1 c, ?_⟩
  have h3 := hQ3 1 (c / (1 - lam ^ 2)) (lam * -(c / Q x) / t)
  rw [one_smul] at h3
  rw [h3]
  by_cases hc : c = 0
  · subst hc
    simp
  · rw [div_pow, ← hκ]
    field_simp [hc, hx0, h1]
    ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private structure OcgData (Q : QuadraticForm (ZMod p) U) where
  P : HypPair Q
  x : U
  hx : x ∈ P.perp
  hx0 : Q x ≠ 0
  c : ZMod p
  hc : c ≠ 0
  lam : ZMod p
  hlam : lam ≠ 0
  hlam4 : lam ^ 4 ≠ 1
  t : ZMod p
  hκ : -(c / Q x) * (1 - lam ^ 2) = t ^ 2

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private def ocgMu {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : ZMod p := D.lam ^ 2
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private def ocgKappa {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : ZMod p := -(D.c / Q D.x)
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private def ocgGamma {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : ZMod p :=
  D.lam * ocgKappa D / D.t
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private def ocgA1 {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : U :=
  D.lam • D.P.e + (D.c / D.lam) • D.P.f
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private def ocgA2 {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : U := D.P.e + D.c • D.P.f
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private def ocgA3 {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : U :=
  D.P.e + (D.c / (1 - ocgMu D)) • D.P.f + ocgGamma D • D.x
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private noncomputable def ocgRho {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : U ≃ₗ[ZMod p] U :=
  reflect Q (ocgA1 D) * reflect Q (ocgA2 D)
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private noncomputable def ocgG {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : U ≃ₗ[ZMod p] U :=
  reflect Q (ocgA3 D) * ocgRho D * reflect Q (ocgA3 D)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private noncomputable def ocgU {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : U ≃ₗ[ZMod p] U :=
  ocgRho D * ocgG D * ocgRho D * (ocgG D).symm

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_mu_ne_one {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : ocgMu D ≠ 1 := by
  intro h
  apply D.hlam4
  rw [show D.lam ^ 4 = ocgMu D ^ 2 by rw [ocgMu]; ring, h, one_pow]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_mu_ne_neg_one {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgMu D ≠ -1 := by
  intro h
  apply D.hlam4
  rw [show D.lam ^ 4 = ocgMu D ^ 2 by rw [ocgMu]; ring, h]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_mu_ne_zero {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : ocgMu D ≠ 0 := by
  intro h
  have h2 : D.lam * D.lam = 0 := by rw [← pow_two]; exact h
  exact D.hlam (mul_self_eq_zero.mp h2)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_kappa_ne_zero {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgKappa D ≠ 0 := by
  rw [ocgKappa]
  exact neg_ne_zero.mpr (div_ne_zero D.hc D.hx0)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_t_ne_zero {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) : D.t ≠ 0 := by
  intro ht
  have hne : ocgKappa D * (1 - ocgMu D) ≠ 0 :=
    mul_ne_zero (ocg_kappa_ne_zero D) (sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D)))
  apply hne
  show -(D.c / Q D.x) * (1 - D.lam ^ 2) = 0
  rw [← D.hκ.symm, ht]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_gamma_ne_zero {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgGamma D ≠ 0 := by
  rw [ocgGamma]
  exact div_ne_zero (mul_ne_zero D.hlam (ocg_kappa_ne_zero D)) (ocg_t_ne_zero D)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_gamma_sq {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgGamma D ^ 2 * Q D.x = -ocgMu D * D.c / (1 - ocgMu D) := by
  have ht : D.t ^ 2 = ocgKappa D * (1 - ocgMu D) := D.hκ.symm
  have hmu : 1 - D.lam ^ 2 ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  have hk : -(D.c / Q D.x) ≠ 0 := neg_ne_zero.mpr (div_ne_zero D.hc D.hx0)
  rw [ocgGamma, div_pow, ht, ocgKappa, ocgMu]
  field_simp [hmu, hk, D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_two_ne_zero {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    (2 : ZMod p) ≠ 0 := by
  intro h2
  have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdvd
  subst hp2
  have hlam1 : D.lam = 1 := by
    generalize hlam : D.lam = x
    fin_cases x
    · exact False.elim (D.hlam hlam)
    · rfl
  exact D.hlam4 (by rw [hlam1, one_pow])

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_Q_a1 {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    Q (D.lam • D.P.e + (D.c / D.lam) • D.P.f) = D.c :=
  (threeMinus_map_eq D.P D.hx D.hx0 D.hlam (ocg_mu_ne_one D) D.hκ).1

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_Q_a2 {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    Q (D.P.e + D.c • D.P.f) = D.c :=
  (threeMinus_map_eq D.P D.hx D.hx0 D.hlam (ocg_mu_ne_one D) D.hκ).2.1

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_Q_a3 {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    Q (D.P.e + (D.c / (1 - ocgMu D)) • D.P.f + ocgGamma D • D.x) = D.c := by
  have h := (threeMinus_map_eq D.P D.hx D.hx0 D.hlam (ocg_mu_ne_one D) D.hκ).2.2
  simpa [ocgMu, ocgGamma, ocgKappa] using h

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_xe {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q D.x D.P.e = 0 := by rw [polar_comm]; exact (HypPair.mem_perp.mp D.hx).1

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_xf {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q D.x D.P.f = 0 := by rw [polar_comm]; exact (HypPair.mem_perp.mp D.hx).2

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_ex {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q D.P.e D.x = 0 := by rw [polar_comm]; exact ocg_xe D

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_fx {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q D.P.f D.x = 0 := by rw [polar_comm]; exact ocg_xf D

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_refl2_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    reflect Q (ocgA2 D) D.P.e = -D.c • D.P.f := by
  rw [ocgA2, reflect_apply (by rw [ocg_Q_a2 D]; exact D.hc)]
  simp only [polar_add_left, polar_smul_left_eq, D.P.polar_ee, D.P.polar_fe, zero_add, ocg_Q_a2 D]
  match_scalars <;> field_simp [D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D]; ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_refl2_f {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    reflect Q (ocgA2 D) D.P.f = -(D.c)⁻¹ • D.P.e := by
  rw [ocgA2, reflect_apply (by rw [ocg_Q_a2 D]; exact D.hc)]
  simp only [polar_add_left, polar_smul_left_eq, D.P.polar_ef, D.P.polar_ff, ocg_Q_a2 D]
  match_scalars <;> field_simp [D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D] <;> ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_refl1_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    reflect Q (ocgA1 D) D.P.e = -(D.c / ocgMu D) • D.P.f := by
  rw [ocgA1, reflect_apply (by rw [ocg_Q_a1 D]; exact D.hc)]
  simp only [polar_add_left, polar_smul_left_eq, D.P.polar_ee, D.P.polar_fe, ocg_Q_a1 D, ocgMu]
  match_scalars <;> field_simp [D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D] <;> ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_refl1_f {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    reflect Q (ocgA1 D) D.P.f = -(ocgMu D / D.c) • D.P.e := by
  rw [ocgA1, reflect_apply (by rw [ocg_Q_a1 D]; exact D.hc)]
  simp only [polar_add_left, polar_smul_left_eq, D.P.polar_ef, D.P.polar_ff, ocg_Q_a1 D, ocgMu]
  match_scalars <;> field_simp [D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D] <;> ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgRho D D.P.e = ocgMu D • D.P.e := by
  rw [ocgRho, LinearEquiv.mul_apply, ocg_refl2_e, map_smul, ocg_refl1_f, smul_smul]
  congr 1
  field_simp [D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_f {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgRho D D.P.f = (ocgMu D)⁻¹ • D.P.f := by
  rw [ocgRho, LinearEquiv.mul_apply, ocg_refl2_f, map_smul, ocg_refl1_e, smul_smul]
  congr 1
  field_simp [D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_x {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgRho D D.x = D.x := by
  have hx := HypPair.mem_perp.mp D.hx
  have h1 : polar Q (ocgA2 D) D.x = 0 := by
    rw [ocgA2]
    simp only [polar_add_left, polar_smul_left_eq, hx.1, hx.2, mul_zero, add_zero]
  have h2 : polar Q (ocgA1 D) D.x = 0 := by
    rw [ocgA1]
    simp only [polar_add_left, polar_smul_left_eq, hx.1, hx.2, mul_zero, add_zero]
  rw [ocgRho, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero h1,
    reflect_apply_of_polar_eq_zero h2]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_perp {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) {w : U}
    (hw : w ∈ D.P.perp) : ocgRho D w = w := by
  have hw' := HypPair.mem_perp.mp hw
  have h1 : polar Q (ocgA2 D) w = 0 := by
    rw [ocgA2]
    simp only [polar_add_left, polar_smul_left_eq, hw'.1, hw'.2, mul_zero, add_zero]
  have h2 : polar Q (ocgA1 D) w = 0 := by
    rw [ocgA1]
    simp only [polar_add_left, polar_smul_left_eq, hw'.1, hw'.2, mul_zero, add_zero]
  rw [ocgRho, LinearEquiv.mul_apply, reflect_apply_of_polar_eq_zero h1,
    reflect_apply_of_polar_eq_zero h2]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_isom {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgRho D ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [ocgRho]
  exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem (reflect_mem_orthogonalGroup Q _)
    (reflect_mem_orthogonalGroup Q _)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_refl3_f {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    reflect Q (ocgA3 D) D.P.f =
      -(1 / D.c) • D.P.e - (ocgMu D / (1 - ocgMu D)) • D.P.f - (ocgGamma D / D.c) • D.x := by
  rw [ocgA3, reflect_apply (by rw [ocg_Q_a3 D]; exact D.hc)]
  simp only [polar_add_left, polar_smul_left_eq, D.P.polar_ef, D.P.polar_ff, ocg_xf D, ocg_Q_a3 D]
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  match_scalars <;> field_simp [hmu, D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D] <;> ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_refl3_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    reflect Q (ocgA3 D) D.P.e =
      -(ocgMu D / (1 - ocgMu D)) • D.P.e - (D.c / (1 - ocgMu D) ^ 2) • D.P.f
        - (ocgGamma D / (1 - ocgMu D)) • D.x := by
  rw [ocgA3, reflect_apply (by rw [ocg_Q_a3 D]; exact D.hc)]
  simp only [polar_add_left, polar_smul_left_eq, D.P.polar_ee, D.P.polar_fe, ocg_xe D, ocg_Q_a3 D]
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  match_scalars <;> field_simp [hmu, D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D] <;> ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_refl3_f {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgRho D (reflect Q (ocgA3 D) D.P.f) =
      -(ocgMu D / D.c) • D.P.e - (1 / (1 - ocgMu D)) • D.P.f - (ocgGamma D / D.c) • D.x := by
  rw [ocg_refl3_f]
  simp only [map_sub, map_smul]
  rw [ocg_rho_e, ocg_rho_f, ocg_rho_x]
  simp only [smul_smul]
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  match_scalars <;> field_simp [hmu, D.hc, ocg_mu_ne_zero D, D.hlam, D.hx0]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_refl3_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgRho D (reflect Q (ocgA3 D) D.P.e) =
      -(ocgMu D ^ 2 / (1 - ocgMu D)) • D.P.e
        - (D.c / (ocgMu D * (1 - ocgMu D) ^ 2)) • D.P.f
        - (ocgGamma D / (1 - ocgMu D)) • D.x := by
  rw [ocg_refl3_e]
  simp only [map_sub, map_smul]
  rw [ocg_rho_e, ocg_rho_f, ocg_rho_x]
  simp only [smul_smul]
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  match_scalars <;> field_simp [hmu, D.hc, ocg_mu_ne_zero D, D.hlam, D.hx0]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_refl3_x_val {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    reflect Q (ocgA3 D) D.x = D.x - (2 * ocgGamma D * Q D.x / D.c) • ocgA3 D := by
  have hx := HypPair.mem_perp.mp D.hx
  have hQ3 : Q (ocgA3 D) = D.c := ocg_Q_a3 D
  have hpol : polar Q (ocgA3 D) D.x = 2 * ocgGamma D * Q D.x := by
    rw [ocgA3, polar_add_left, polar_add_left, polar_smul_left_eq, polar_smul_left_eq, hx.1, hx.2,
      polar_self_eq_two_mul]
    ring
  rw [reflect_apply (by rw [hQ3]; exact D.hc), hpol, hQ3]

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_polar_refl3 {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) (z : U) :
    polar Q D.x (reflect Q (ocgA3 D) z) = polar Q (reflect Q (ocgA3 D) D.x) z := by
  have hO := reflect_mem_orthogonalGroup Q (ocgA3 D)
  have h33 : reflect Q (ocgA3 D) (reflect Q (ocgA3 D) z) = z := by
    rw [← LinearEquiv.mul_apply, reflect_mul_self]
    rfl
  have h := polar_map_of_mem hO D.x (reflect Q (ocgA3 D) z)
  rw [h33] at h
  exact h.symm

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_a3_rho_refl3_f {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q (ocgA3 D) (ocgRho D (reflect Q (ocgA3 D) D.P.f)) = -1 := by
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  rw [ocg_rho_refl3_f, ocgA3]
  simp only [polar_add_left, polar_add_left, polar_sub_right, polar_sub_right,
    polar_smul_left_eq, polar_smul_left_eq, polar_smul_right_eq, polar_smul_right_eq,
    polar_smul_right_eq, D.P.polar_ee, D.P.polar_ff, D.P.polar_ef, D.P.polar_fe, ocg_ex D,
    ocg_fx D, ocg_xe D, ocg_xf D, polar_self_eq_two_mul]
  ring_nf
  linear_combination (norm := (field_simp [D.hc, hmu, D.hx0, ocg_mu_ne_zero D]; ring))
    (ocg_gamma_sq D) * (-(2 / D.c))

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_g_f {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgG D D.P.f = ((1 - ocgMu D) / D.c) • D.P.e := by
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  have hQ3 : Q (ocgA3 D) = D.c := ocg_Q_a3 D
  rw [ocgG, LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    reflect_apply (by rw [hQ3]; exact D.hc), ocg_a3_rho_refl3_f, hQ3, ocg_rho_refl3_f, ocgA3]
  match_scalars <;> field_simp [hmu, D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D] <;> ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_g_inv_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    (ocgG D).symm D.P.e = (D.c / (1 - ocgMu D)) • D.P.f := by
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  have h : ocgG D ((D.c / (1 - ocgMu D)) • D.P.f) = D.P.e := by
    rw [map_smul, ocg_g_f, smul_smul]
    field_simp [hmu, D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D]
    simp
  calc (ocgG D).symm D.P.e
      = (ocgG D).symm (ocgG D ((D.c / (1 - ocgMu D)) • D.P.f)) := by rw [h]
    _ = (D.c / (1 - ocgMu D)) • D.P.f := by simp

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_u_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgU D D.P.e = D.P.e := by
  rw [ocgU]
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  simp only [LinearEquiv.mul_apply]
  rw [ocg_g_inv_e]
  simp only [map_smul]
  rw [ocg_rho_f]
  simp only [map_smul]
  rw [ocg_g_f]
  simp only [map_smul]
  rw [ocg_rho_e]
  simp only [smul_smul]
  field_simp [hmu, D.hc, ocg_mu_ne_zero D, D.hlam, D.hx0]
  simp

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_proj_eq_of_polar_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) {z : U}
    (hz : polar Q z D.P.e = 0) :
    D.P.proj z = z - polar Q z D.P.f • D.P.e := by
  rw [HypPair.proj, hz]
  simp

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_rho_sub {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) {z : U}
    (hz : polar Q z D.P.e = 0) :
    ocgRho D z - z = (polar Q z D.P.f * (ocgMu D - 1)) • D.P.e := by
  have hρ : ocgRho D z = (polar Q z D.P.f * ocgMu D) • D.P.e + D.P.proj z := by
    conv_lhs => rw [D.P.eq_add_proj z]
    rw [map_add, map_add, map_smul, map_smul, ocg_rho_e, ocg_rho_f,
      ocg_rho_perp D (D.P.proj_mem_perp z), hz]
    simp only [smul_smul, zero_mul, zero_smul, add_zero]
  rw [hρ, ocg_proj_eq_of_polar_e D hz]
  module

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_g_isom {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgG D ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
  rw [ocgG]
  exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
    ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem (reflect_mem_orthogonalGroup Q _)
      (ocg_rho_isom D)) (reflect_mem_orthogonalGroup Q _)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_x_rho_refl3_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q D.x (ocgRho D (reflect Q (ocgA3 D) D.P.e)) =
      -2 * ocgGamma D * Q D.x / (1 - ocgMu D) := by
  rw [ocg_rho_refl3_e]
  simp only [polar_sub_right, polar_smul_right_eq, ocg_xe D, ocg_xf D,
    polar_self_eq_two_mul]
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  field_simp [hmu, D.hc, D.hlam, D.hx0, ocg_mu_ne_zero D]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_a3_rho_refl3_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q (ocgA3 D) (ocgRho D (reflect Q (ocgA3 D) D.P.e)) =
      D.c * (ocgMu D ^ 2 - ocgMu D - 1) / (ocgMu D * (1 - ocgMu D)) := by
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  rw [ocg_rho_refl3_e, ocgA3]
  simp only [polar_add_left, polar_add_left, polar_sub_right, polar_sub_right,
    polar_smul_left_eq, polar_smul_left_eq, polar_smul_right_eq, polar_smul_right_eq,
    polar_smul_right_eq, D.P.polar_ee, D.P.polar_ff, D.P.polar_ef, D.P.polar_fe, ocg_ex D,
    ocg_fx D, ocg_xe D, ocg_xf D, polar_self_eq_two_mul]
  have hmu2 : 1 - ocgMu D * 2 + ocgMu D ^ 2 ≠ 0 := by
    have h : 1 - ocgMu D * 2 + ocgMu D ^ 2 = (1 - ocgMu D) ^ 2 := by ring
    rw [h]; exact pow_ne_zero 2 hmu
  ring_nf
  linear_combination (norm := (field_simp [D.hc, hmu, hmu2, D.hx0, ocg_mu_ne_zero D]; ring))
    (ocg_gamma_sq D) * (-(2 / (1 - ocgMu D)))

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_B_x_ge {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q D.x (ocgG D D.P.e) = 2 * ocgGamma D * Q D.x * (ocgMu D + 1) / ocgMu D := by
  rw [ocgG, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ocg_polar_refl3, ocg_refl3_x_val,
    sub_eq_add_neg, polar_add_left, polar_neg_left, polar_smul_left_eq, ocg_x_rho_refl3_e,
    ocg_a3_rho_refl3_e]
  have hmu : 1 - ocgMu D ≠ 0 := sub_ne_zero.mpr (Ne.symm (ocg_mu_ne_one D))
  field_simp [hmu, D.hc, ocg_mu_ne_zero D, D.hlam, D.hx0]
  ring

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_B_x_ge_ne {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    polar Q D.x (ocgG D D.P.e) ≠ 0 := by
  rw [ocg_B_x_ge]
  have h2 : (2 : ZMod p) ≠ 0 := ocg_two_ne_zero D
  have hmu1 : ocgMu D + 1 ≠ 0 := fun h => ocg_mu_ne_neg_one D (eq_neg_of_add_eq_zero_left h)
  exact div_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero h2 (ocg_gamma_ne_zero D)) D.hx0)
    hmu1) (ocg_mu_ne_zero D)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_u_ne_one {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) :
    ocgU D ≠ 1 := by
  rw [ocgU]
  intro hu
  have hbase : ocgRho D * ocgG D * ocgRho D = ocgG D := by
    have h := congrArg (fun f => f * ocgG D) hu
    rw [mul_assoc ((ocgRho D * ocgG D) * ocgRho D) ((ocgG D).symm) (ocgG D),
      show (ocgG D).symm * ocgG D = 1 by ext x; simp, mul_one, one_mul] at h
    exact h
  have hconj : ocgG D * ocgRho D = (ocgRho D).symm * ocgG D := by
    have h := congrArg (fun f => (ocgRho D).symm * f) hbase
    rw [← mul_assoc ((ocgRho D).symm) (ocgRho D * ocgG D) (ocgRho D),
      ← mul_assoc ((ocgRho D).symm) (ocgRho D) (ocgG D),
      show (ocgRho D).symm * ocgRho D = 1 by ext x; simp, one_mul] at h
    exact h
  have hL : polar Q D.x ((ocgG D * ocgRho D) D.P.e) =
      ocgMu D * polar Q D.x (ocgG D D.P.e) := by
    rw [LinearEquiv.mul_apply, ocg_rho_e, map_smul, polar_smul_right_eq]
  have h2 : polar Q D.x (((ocgRho D).symm * ocgG D) D.P.e) =
      polar Q D.x (ocgG D D.P.e) := by
    rw [LinearEquiv.mul_apply]
    have h := polar_map_of_mem (ocg_rho_isom D) D.x ((ocgRho D).symm (ocgG D D.P.e))
    rw [LinearEquiv.apply_symm_apply, ocg_rho_x] at h
    exact h.symm
  have hEq := congrArg (fun f => polar Q D.x (f D.P.e)) hconj
  rw [hL, h2] at hEq
  have hne := ocg_B_x_ge_ne D
  have hzero : (ocgMu D - 1) * polar Q D.x (ocgG D D.P.e) = 0 := by
    rw [sub_mul, one_mul, hEq, sub_self]
  exact (mul_ne_zero (sub_ne_zero.mpr (ocg_mu_ne_one D)) hne) hzero

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_gw_e {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) {w : U}
    (hw : w ∈ D.P.perp) : polar Q (ocgG D w) D.P.e = 0 := by
  have hgi : (ocgG D).symm ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem (ocg_g_isom D)
  have h := polar_map_of_mem (ocg_g_isom D) w ((ocgG D).symm D.P.e)
  rw [LinearEquiv.apply_symm_apply, ocg_g_inv_e, polar_smul_right_eq,
    polar_comm Q w D.P.f, (HypPair.mem_perp.mp hw).2, mul_zero] at h
  exact h

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_u_sub {Q : QuadraticForm (ZMod p) U} (D : OcgData Q) {y : U}
    (hy : polar Q y D.P.e = 0) :
    ocgU D y - y =
      (polar Q (ocgG D (D.P.proj ((ocgG D).symm y))) D.P.f * (ocgMu D - 1)) • D.P.e := by
  have hgi : (ocgG D).symm ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem (ocg_g_isom D)
  have hgy : polar Q ((ocgG D).symm y) D.P.f = 0 := by
    have h := polar_map_of_mem hgi y (ocgG D D.P.f)
    rw [LinearEquiv.symm_apply_apply, ocg_g_f, polar_smul_right_eq, hy, mul_zero] at h
    exact h
  have hdec : (ocgG D).symm y =
      polar Q ((ocgG D).symm y) D.P.e • D.P.f + D.P.proj ((ocgG D).symm y) := by
    have h := D.P.eq_add_proj ((ocgG D).symm y)
    rw [hgy, zero_smul, zero_add] at h
    exact h
  set s : ZMod p := polar Q ((ocgG D).symm y) D.P.e with hs
  set w : U := D.P.proj ((ocgG D).symm y) with hw
  have hwperp : w ∈ D.P.perp := D.P.proj_mem_perp _
  have huy : ocgU D y = (s * ((1 - ocgMu D) / D.c)) • D.P.e + ocgRho D (ocgG D w) := by
    rw [ocgU, LinearEquiv.mul_apply, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hdec]
    simp only [map_add, map_smul]
    rw [ocg_rho_f, ocg_rho_perp D hwperp]
    simp only [map_smul]
    rw [ocg_g_f]
    simp only [map_smul]
    rw [ocg_rho_e]
    simp only [smul_smul]
    match_scalars <;> field_simp [D.hc, ocg_mu_ne_zero D, D.hlam, D.hx0]
  have hy_eq : y = (s * ((1 - ocgMu D) / D.c)) • D.P.e + ocgG D w := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (ocgG D) y]
    rw [hdec]
    simp only [map_add, map_smul]
    rw [ocg_g_f]
    simp only [smul_smul]
  rw [huy, hy_eq]
  rw [show (s * ((1 - ocgMu D) / D.c)) • D.P.e + ocgRho D (ocgG D w) -
      ((s * ((1 - ocgMu D) / D.c)) • D.P.e + ocgG D w)
      = ocgRho D (ocgG D w) - ocgG D w by module]
  exact ocg_rho_sub D (ocg_gw_e D hwperp)

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_u_root {Q : QuadraticForm (ZMod p) U} (D : OcgData Q)
    (hQ : (polarBilin Q).Nondegenerate)
    (hO : ocgU D ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ocgU D ∈ rootGroup Q D.P.e := by
  have hue : ocgU D D.P.e = D.P.e := ocg_u_e D
  have hgi : (ocgG D).symm ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem (ocg_g_isom D)
  refine (mem_rootGroup_iff hQ D.P.Q_e D.P.e_ne_zero).2 ⟨hO, hue, ?_⟩
  intro y hy
  exact ⟨polar Q (ocgG D (D.P.proj ((ocgG D).symm y))) D.P.f * (ocgMu D - 1), ocg_u_sub D hy⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private theorem ocg_isRootCenter_aux {Q : QuadraticForm (ZMod p) U} (D : OcgData Q)
    [Module.Finite (ZMod p) U] (h3 : Module.finrank (ZMod p) U = 3)
    (hQ : (polarBilin Q).Nondegenerate) :
    IsRootCenter Q (Subgroup.closure {reflect Q (ocgA1 D), reflect Q (ocgA2 D),
        reflect Q (ocgA3 D)}) D.P.e ∧
      IsRootCenter Q (Subgroup.closure {reflect Q (ocgA1 D), reflect Q (ocgA2 D),
        reflect Q (ocgA3 D)}) D.P.f := by
  let X : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure {reflect Q (ocgA1 D), reflect Q (ocgA2 D), reflect Q (ocgA3 D)}
  have hXle : X ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    refine (Subgroup.closure_le _).mpr ?_
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact reflect_mem_orthogonalGroup Q _
    · exact reflect_mem_orthogonalGroup Q _
    · exact reflect_mem_orthogonalGroup Q _
  have hr1 : reflect Q (ocgA1 D) ∈ X := Subgroup.subset_closure (by simp)
  have hr2 : reflect Q (ocgA2 D) ∈ X := Subgroup.subset_closure (by simp)
  have hr3 : reflect Q (ocgA3 D) ∈ X := Subgroup.subset_closure (by simp)
  have hρX : ocgRho D ∈ X := X.mul_mem hr1 hr2
  have hgX : ocgG D ∈ X := X.mul_mem (X.mul_mem hr3 hρX) hr3
  have huX : ocgU D ∈ X := X.mul_mem (X.mul_mem (X.mul_mem hρX hgX) hρX) (X.inv_mem hgX)
  have hO : ocgU D ∈ TauCeti.QuadraticMap.orthogonalGroup Q := hXle huX
  have huroot : ocgU D ∈ rootGroup Q D.P.e := ocg_u_root D hQ hO
  have hue : ocgU D D.P.e = D.P.e := ocg_u_e D
  have hu1 : ocgU D ≠ 1 := ocg_u_ne_one D
  have he_root : IsRootCenter Q X D.P.e :=
    isRootCenter_of_mem_rootGroup_ne_one h3 hQ D.P.e_ne_zero D.P.Q_e huX huroot hu1
  have hf_root : IsRootCenter Q X D.P.f := by
    have hmap := he_root.map hXle hr2
    rw [ocg_refl2_e] at hmap
    have hc' : (-D.c)⁻¹ ≠ 0 := inv_ne_zero (neg_ne_zero.mpr D.hc)
    have hf := hmap.smul hc'
    rwa [smul_smul, inv_mul_cancel₀ (neg_ne_zero.mpr D.hc), one_smul] at hf
  exact ⟨he_root, hf_root⟩

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem isRootCenter_threeMinus [Module.Finite (ZMod p) U]
    (h3 : Module.finrank (ZMod p) U = 3) {Q : QuadraticForm (ZMod p) U}
    (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q) {x : U} (hx : x ∈ P.perp)
    (hx0 : Q x ≠ 0) {c lam t : ZMod p} (hc : c ≠ 0) (hlam : lam ≠ 0) (hlam4 : lam ^ 4 ≠ 1)
    (hκ : -(c / Q x) * (1 - lam ^ 2) = t ^ 2) {a₁ a₂ a₃ : U}
    (ha₁ : a₁ = lam • P.e + (c / lam) • P.f) (ha₂ : a₂ = P.e + c • P.f)
    (ha₃ : a₃ = P.e + (c / (1 - lam ^ 2)) • P.f + (lam * -(c / Q x) / t) • x) :
    IsRootCenter Q (Subgroup.closure {reflect Q a₁, reflect Q a₂, reflect Q a₃}) P.e ∧
      IsRootCenter Q (Subgroup.closure {reflect Q a₁, reflect Q a₂, reflect Q a₃}) P.f := by
  let D : OcgData Q :=
    { P := P, x := x, hx := hx, hx0 := hx0, c := c, hc := hc, lam := lam, hlam := hlam,
      hlam4 := hlam4, t := t, hκ := hκ }
  have ha1 : a₁ = ocgA1 D := by rw [ha₁]; rfl
  have ha2 : a₂ = ocgA2 D := by rw [ha₂]; rfl
  have ha3 : a₃ = ocgA3 D := by rw [ha₃]; rfl
  rw [ha1, ha2, ha3]
  exact ocg_isRootCenter_aux D h3 hQ

open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_five_square (α : ZMod 5) : α ^ 2 = 0 ∨ α ^ 2 = 1 ∨ α ^ 2 = 4 := by
  fin_cases α <;> decide +kernel

private lemma ocg_five_two_ne_zero : (2 : ZMod 5) ≠ 0 := by decide +kernel

private lemma ocg_sixteen : (2 : ZMod 5) ^ 2 * 4 = 1 := by decide +kernel

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmSeven in
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_order_aniso_four {V : Type} [AddCommGroup V] [Module (ZMod 5) V]
    [Fact (Nat.Prime 5)]
    {Q : QuadraticForm (ZMod 5) V} {c : ZMod 5} {a b : V} (ha : Q a = c) (hb : Q b = c)
    (hc : c ≠ 0) {α : ZMod 5} (hB : polar Q a b = 2 * c * α) (h4 : α ^ 2 = 4) :
    orderOf (reflect Q a * reflect Q b) ≤ 3 := by
  have h2α : (2 * α) ^ 2 = 1 := by rw [mul_pow, h4]; exact ocg_sixteen
  rcases sq_eq_one_iff.mp h2α with h2α | h2α
  · have hBa : polar Q a b = c := by
      rw [hB, show (2 : ZMod 5) * c * α = c * (2 * α) by ring, h2α]
      ring
    have hpow : (reflect Q a * reflect Q b) ^ 3 = 1 :=
      reflect_mul_reflect_pow_three (by rw [ha, hb]) (by rw [hBa, hb]) (by rw [hb]; exact hc)
    exact orderOf_le_of_pow_eq_one (by norm_num) hpow
  · have hBneg : polar Q a b = -c := by
      rw [hB, show (2 : ZMod 5) * c * α = c * (2 * α) by ring, h2α]
      ring
    have hxy : Q a = Q (-b) := by rw [QuadraticMap.map_neg, ha, hb]
    have hB' : polar Q a (-b) = Q (-b) := by
      rw [polar_neg_right, hBneg, QuadraticMap.map_neg, hb]
      ring
    have hy : Q (-b) ≠ 0 := by rw [QuadraticMap.map_neg, hb]; exact hc
    have hpow : (reflect Q a * reflect Q (-b)) ^ 3 = 1 :=
      reflect_mul_reflect_pow_three hxy hB' hy
    rw [reflect_neg_vec] at hpow
    exact orderOf_le_of_pow_eq_one (by norm_num) hpow

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmSeven in
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
private lemma ocg_order_aniso_ne_zero (hp5 : p = 5)
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} {a b : U} (ha : Q a = c) (hb : Q b = c)
    (haniso : ∀ u, polar Q a u = 0 → Q u = 0 → u = 0) (hc : c ≠ 0) :
    orderOf (reflect Q a * reflect Q b) ≤ 3 := by
  subst hp5
  have h2 : (2 : ZMod 5) ≠ 0 := ocg_five_two_ne_zero
  have h2c : (2 : ZMod 5) * c ≠ 0 := mul_ne_zero h2 hc
  set α : ZMod 5 := polar Q a b / (2 * c) with hα
  set w : U := b - α • a with hw
  have hB : polar Q a b = 2 * c * α := by
    rw [hα]
    field_simp [h2c]
  have haw : polar Q a w = 0 := by
    rw [hw, polar_sub_right, polar_smul_right_eq, polar_self_eq_two_mul, ha, hB]
    ring
  have hQw : Q w = c * (1 - α ^ 2) := by
    rw [hw, sub_eq_add_neg, QuadraticMap.map_add Q, QuadraticMap.map_neg, map_smul_eq_sq,
      ha, hb, polar_neg_right, polar_smul_right_eq, polar_comm Q b a, hB]
    ring
  rcases ocg_five_square α with h0 | h1 | h4
  · have hα0 : α = 0 := by
      have h : α * α = 0 := by rw [← pow_two, h0]
      exact mul_self_eq_zero.mp h
    have hB0 : polar Q a b = 0 := by rw [hB, hα0, mul_zero]
    have hcomm := reflect_mul_comm_of_polar_eq_zero (Q := Q) (v := a) (w := b) hB0
    have hg2 : (reflect Q a * reflect Q b) ^ 2 = 1 := by
      have h1 : reflect Q a * reflect Q b * (reflect Q a * reflect Q b) = 1 := by
        calc reflect Q a * reflect Q b * (reflect Q a * reflect Q b)
            = reflect Q a * (reflect Q b * reflect Q a) * reflect Q b := by group
          _ = reflect Q a * (reflect Q a * reflect Q b) * reflect Q b := by rw [← hcomm]
          _ = (reflect Q a * reflect Q a) * (reflect Q b * reflect Q b) := by group
          _ = 1 := by rw [reflect_mul_self, reflect_mul_self, one_mul]
      simpa [pow_two] using h1
    exact le_trans (orderOf_le_of_pow_eq_one (by norm_num) hg2) (by norm_num)
  · have hQw0 : Q w = 0 := by rw [hQw, h1]; ring
    have hw0 : w = 0 := haniso w haw hQw0
    have hb' : b = α • a := by
      rw [hw] at hw0
      exact sub_eq_zero.mp hw0
    rcases sq_eq_one_iff.mp h1 with h1 | h1
    · rw [hb', h1, one_smul]
      rw [reflect_mul_self, orderOf_one]
      norm_num
    · rw [hb', h1, neg_smul, reflect_neg_vec, one_smul, reflect_mul_self, orderOf_one]
      norm_num
  · exact ocg_order_aniso_four ha hb hc hB h4

open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.OmSeven in
open CFSG.ClassicalGroups.Orthogonal QuadraticMap in
theorem orderOf_reflect_mul_le_three_of_anisotropic (hp5 : p = 5)
    {Q : QuadraticForm (ZMod p) U} {c : ZMod p} {a b : U} (ha : Q a = c) (hb : Q b = c)
    (haniso : ∀ u, polar Q a u = 0 → Q u = 0 → u = 0) :
    orderOf (reflect Q a * reflect Q b) ≤ 3 := by
  by_cases hc : c = 0
  · subst hc
    subst hp5
    have ha0 : a = 0 := haniso a (polar_self_eq_zero ha) ha
    subst ha0
    rw [reflect_of_map_eq_zero (QuadraticMap.map_zero Q), one_mul]
    exact le_trans (orderOf_le_of_pow_eq_one (n := 2) (by norm_num)
      (by rw [pow_two]; exact reflect_mul_self Q b)) (by norm_num)
  · exact ocg_order_aniso_ne_zero hp5 ha hb haniso hc
end CFSG.StandardType.ZS
