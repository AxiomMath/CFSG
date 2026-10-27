module

public import CFSG.Monster.Visible.SignCompat.Triality
import Mathlib.Tactic.ReduceModChar

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess Matrix

namespace SignCompat

variable (e : Parker)

theorem cyc_diag (i : Fin 24) :
    tauB (theta (signLiftPair e) (tbasis (.inl i))) =
      theta (signLiftPair e) (rhoEquiv (XQ e) (tauB (tbasis (.inl i)))) := by
  rw [theta_sign_diag, tauB_diag, rho_diag, theta_sign_diag]

theorem cyc_pair (p : LtPair) (k : Fin 3) :
    tauB (theta (signLiftPair e) (tbasis (.inr (.inl (p, k))))) =
      theta (signLiftPair e) (rhoEquiv (XQ e) (tauB (tbasis (.inr (.inl (p, k)))))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [theta_sign_pair_zero, map_smul, tauB_pair, show (0 : Fin 3) + 1 = 1 from rfl,
      rho_pair_one, map_smul, theta_sign_pair_one]
  · rw [theta_sign_pair_one, tauB_pair, show (1 : Fin 3) + 1 = 2 from rfl, rho_pair_two,
      map_smul, theta_sign_pair_two, smul_smul, sgn_mul_self, one_smul]
  · rw [theta_sign_pair_two, map_smul, tauB_pair, show (2 : Fin 3) + 1 = 0 from rfl,
      rho_pair_zero, theta_sign_pair_zero]

theorem cyc_odd (hP : P (e.code : Fin 24 → ZMod 2) = 0) (c : C₀) (i : Fin 24) (k : Fin 3) :
    tauB (theta (signLiftPair e) (tbasis (.inr (.inr (.inl (c, i, k)))))) =
      theta (signLiftPair e) (rhoEquiv (XQ e) (tauB (tbasis (.inr (.inr (.inl (c, i, k))))))) := by
  have hK := θ_add_θ_swap e.code (c : C)
  have hc := coe_shift_apply e.code c i
  have hPs := P_coe_shift e.code c
  have hKs : K (e.code : Fin 24 → ZMod 2) ((shift e.code c : C) : Fin 24 → ZMod 2) =
      K (e.code : Fin 24 → ZMod 2) ((c : C) : Fin 24 → ZMod 2) := by
    rw [K_shift_right, K_self e.code.2, A_self_mid e.code.2 (c : C).2, add_zero, add_zero]
  have hθs : θ (shift e.code c : C) e.code = θ (c : C) e.code + P (e.code : Fin 24 → ZMod 2) := by
    rw [θ_shift_left, θ_self, A_self_right (c : C).2 e.code.2, add_zero]
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [theta_sign_odd_zero, map_smul, tauB_odd, tauB_odd, show (0 : Fin 3) + 1 = 1 from rfl,
      rho_odd_one, map_smul, theta_sign_odd_one, smul_smul, ← sgn_add]
    refine congrArg (fun t => sgn t • tbasis (.inr (.inr (.inl (shift e.code c, i, 1))))) ?_
    linear_combination (norm := (ring_nf; try reduce_mod_char)) hK - hc - hKs - hP
  · rw [theta_sign_odd_one, map_smul, tauB_odd, show (1 : Fin 3) + 1 = 2 from rfl,
      rho_odd_two, map_smul, theta_sign_odd_two, shift_shift, smul_smul, ← sgn_add]
    refine congrArg (fun t => sgn t • tbasis (.inr (.inr (.inl (c, i, 2))))) ?_
    linear_combination (norm := (ring_nf; try reduce_mod_char)) -hK + hθs
  · rw [theta_sign_odd_two, map_smul, tauB_odd, tauB_odd, show (2 : Fin 3) + 1 = 0 from rfl,
      rho_odd_zero, map_smul, theta_sign_odd_zero, smul_smul, ← sgn_add]
    refine congrArg (fun t => sgn t • tbasis (.inr (.inr (.inl (shift e.code c, i, 0))))) ?_
    rw [K_comm] at hPs
    linear_combination (norm := (ring_nf; try reduce_mod_char)) hPs - hP

theorem octHD_cyc (d : OctadWord) (v w a' : Octad.EvenQuot (octSupp d)) :
    sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v a') * octHD d (v + a') w =
      octHD d v (w + a') * sgn (Octad.quadForm (octSupp d) a' +
        QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) (w + a') a') *
        sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) (w + a') a') := by
  set Q := Octad.quadForm (octSupp d)
  have hq : Q (w + a') = Q w + Q a' + QuadraticMap.polarBilin Q w a' := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    ring
  have hself : QuadraticMap.polarBilin Q a' a' = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    exact ZModModule.add_self _
  have hb1 : QuadraticMap.polarBilin Q v (w + a') =
      QuadraticMap.polarBilin Q v w + QuadraticMap.polarBilin Q v a' := map_add _ _ _
  have hb2 : QuadraticMap.polarBilin Q (w + a') a' =
      QuadraticMap.polarBilin Q w a' + QuadraticMap.polarBilin Q a' a' :=
    LinearMap.map_add₂ _ _ _ _
  have hb3 : QuadraticMap.polarBilin Q (v + a') w =
      QuadraticMap.polarBilin Q v w + QuadraticMap.polarBilin Q a' w :=
    LinearMap.map_add₂ _ _ _ _
  have hsym : QuadraticMap.polarBilin Q a' w = QuadraticMap.polarBilin Q w a' := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply,
      QuadraticMap.polar_comm]
  rw [octHD_apply', octHD_apply', hb1, hb3, hsym, hq, hb2, hself, add_zero]
  have h1 := sgn_mul_self (Q a')
  have h2 := sgn_mul_self (QuadraticMap.polarBilin Q w a')
  simp only [sgn_add]
  linear_combination (-(((2 : ℚ) ^ 3)⁻¹ * sgn (QuadraticMap.polarBilin Q v w) *
    sgn (QuadraticMap.polarBilin Q v a') * sgn (Q w) * sgn (QuadraticMap.polarBilin Q w a'))) *
      (h1 + sgn (Q a') * sgn (Q a') * h2)

theorem cyc_oct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tauB (theta (signLiftPair e) (tbasis (.inr (.inr (.inr ⟨d, v⟩))))) =
      theta (signLiftPair e) (rhoEquiv (XQ e) (tauB (tbasis (.inr (.inr (.inr ⟨d, v⟩)))))) := by
  rw [theta_sign_oct, map_smul, tauB_oct, tauB_oct, Finset.smul_sum, map_sum, map_sum]
  simp only [map_smul, rho_oct, theta_sign_oct, smul_smul]
  have hshift : ∀ w : Octad.EvenQuot (octSupp d), w + octCls e.code d + octCls e.code d = w :=
    fun w => by rw [add_assoc, ZModModule.add_self, add_zero]
  refine Fintype.sum_equiv (Equiv.addRight (octCls e.code d)) _ _ fun w => ?_
  rw [Equiv.coe_addRight, hshift, octHD_cyc]

theorem cyc_tbasis (hP : P (e.code : Fin 24 → ZMod 2) = 0) (x : TIdx) :
    tauB (theta (signLiftPair e) (tbasis x)) =
      theta (signLiftPair e) (rhoEquiv (XQ e) (tauB (tbasis x))) := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | ⟨d, v⟩
  · exact cyc_diag e i
  · exact cyc_pair e p k
  · exact cyc_odd e hP c i k
  · exact cyc_oct e d v

end SignCompat

open SignCompat

theorem tauB_mul_thetaEquiv_signLiftPair (e : Parker) (hP : P (e.code : Fin 24 → ZMod 2) = 0) :
    tauB * thetaEquiv (signLiftPair e) = thetaEquiv (signLiftPair e) * rhoEquiv (XQ e) * tauB :=
  tbasis.ext' fun x => cyc_tbasis e hP x

theorem tauB_conj_thetaEquiv_signLiftPair (e : Parker) (hP : P (e.code : Fin 24 → ZMod 2) = 0) :
    tauB * thetaEquiv (signLiftPair e) * tauB⁻¹ =
      thetaEquiv (signLiftPair e) * rhoEquiv (XQ e) := by
  rw [tauB_mul_thetaEquiv_signLiftPair e hP, mul_inv_cancel_right]

theorem coe_rhoPair_XQ_mul_signLiftPair (e : Parker) :
    ((rhoPair (XQ e) * signLiftPair e : Pvis) : GL SpinIdx ℚ × latticeO) =
      (XU e * YU e, gO e.code) :=
  Prod.ext rfl (one_mul _)

theorem tauB_conj_thetaEquiv_signLiftPair_eq (e : Parker)
    (hP : P (e.code : Fin 24 → ZMod 2) = 0) :
    tauB * thetaEquiv (signLiftPair e) * tauB⁻¹ = thetaEquiv (rhoPair (XQ e) * signLiftPair e) := by
  rw [thetaEquiv_mul, tauB_conj_thetaEquiv_signLiftPair e hP]
  rfl

theorem tauB_sq_conj_rhoEquiv_XQ (e : Parker) (hP : P (e.code : Fin 24 → ZMod 2) = 0) :
    tauB * tauB * rhoEquiv (XQ e) * tauB⁻¹ * tauB⁻¹ =
      thetaEquiv (signLiftPair e) * rhoEquiv (XQ e) := by
  rw [← tauB_conj_thetaEquiv_signLiftPair e hP, thetaEquiv_signLiftPair]
  simp only [mul_assoc]

end CFSG.Monster.Visible
