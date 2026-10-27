module

public import CFSG.Monster.Visible.SignCompat.Labels
import Mathlib.Tactic.ReduceModChar
public import CFSG.Monster.Griess.TrialityMatrix
public import CFSG.Monster.Visible.Action

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Visible

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess Matrix
open scoped symmDiff

namespace SignCompat

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem two_eq_zero' : (2 : ZMod 2) = 0 := rfl

private theorem sgn_one' : sgn 1 = -1 := rfl

theorem mk_zero_zero_smul' (s : ℚ) (N : SpaceW) :
    ((0 : symMat), (0 : SpaceX), s • N) = s • ((0 : symMat), (0 : SpaceX), N) := by
  rw [Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem mk_zero_X_smul (s : ℚ) (x : SpaceX) :
    ((0 : symMat), s • x, (0 : SpaceW)) = s • ((0 : symMat), x, (0 : SpaceW)) := by
  rw [Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem mk_zero_X_neg (x : SpaceX) :
    ((0 : symMat), -x, (0 : SpaceW)) = -((0 : symMat), x, (0 : SpaceW)) := by
  rw [Prod.neg_mk, Prod.neg_mk, neg_zero, neg_zero]

theorem mk_A_smul (s : ℚ) (A : symMat) :
    (s • A, (0 : SpaceX), (0 : SpaceW)) = s • (A, (0 : SpaceX), (0 : SpaceW)) := by
  rw [Prod.smul_mk, Prod.smul_mk, smul_zero, smul_zero]

theorem tensor_smul_smul (x y : ℚ) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    tensor (x • q) (y • v) = (x * y) • tensor q v := by
  rw [tensor, tensor, smul_vecMulVec, vecMulVec_smul, smul_smul]

theorem tensor_smul_left (x : ℚ) (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    tensor (x • q) v = x • tensor q v := by
  rw [tensor, tensor, smul_vecMulVec]

theorem thetaA_gmat_basisA (a : C) (i j : Fin 24) :
    thetaA (gmat a) (basisA s(i, j)) =
      sgn ((a : Fin 24 → ZMod 2) i + (a : Fin 24 → ZMod 2) j) • basisA s(i, j) := by
  refine Subtype.ext ?_
  rw [coe_thetaA, Submodule.coe_smul, gmat_transpose]
  ext k l
  rw [gmat, mul_diagonal, diagonal_mul, Matrix.smul_apply, basisA_apply, smul_eq_mul]
  by_cases h : s(k, l) = s(i, j)
  · rw [ite_eq_left h, mul_one, mul_one, sgn_add]
    rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact mul_comm _ _
  · rw [ite_eq_right h, mul_zero, zero_mul, mul_zero]

variable (e : Parker)

theorem theta_sign_A (A : symMat) :
    theta (signLiftPair e) (A, 0, 0) = (thetaA (gmat e.code) A, 0, 0) :=
  theta_symMat _ A

theorem theta_sign_X (r : Q) :
    theta (signLiftPair e) ((0 : symMat), Xlift r, (0 : SpaceW)) =
      ((0 : symMat), Xlift (conjYQ e r), (0 : SpaceW)) :=
  theta_Xlift _ r

theorem theta_sign_W (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    theta (signLiftPair e) ((0 : symMat), (0 : SpaceX), tensor q v) =
      ((0 : symMat), (0 : SpaceX), tensor (q ᵥ* Ymat e) (v ᵥ* gmat e.code)) :=
  theta_tensor _ q v

theorem rho_X (r : Q) :
    rhoEquiv (XQ e) ((0 : symMat), Xlift r, (0 : SpaceW)) =
      sgn (θ e.code (spinEquiv.symm r).a + pair e.code (spinEquiv.symm r).δ) •
        ((0 : symMat), Xlift r, (0 : SpaceW)) := by
  rw [rhoEquiv_Xlift, Xlift_XQ_conj, mk_zero_X_smul]

theorem rho_W (q : SpinIdx → ℚ) (v : Fin 24 → ℚ) :
    rhoEquiv (XQ e) ((0 : symMat), (0 : SpaceX), tensor q v) =
      ((0 : symMat), (0 : SpaceX), tensor (q ᵥ* Xmat e) v) :=
  rhoEquiv_tensor (XQ e) q v

theorem theta_sign_diag (i : Fin 24) :
    theta (signLiftPair e) (tbasis (.inl i)) = tbasis (.inl i) := by
  rw [tbasis_diag, theta_sign_A, thetaA_gmat_basisA, sgn_add, sgn_mul_self, one_smul]

theorem rho_diag (i : Fin 24) : rhoEquiv (XQ e) (tbasis (.inl i)) = tbasis (.inl i) := by
  rw [tbasis_diag]
  exact rhoEquiv_symMat _ _

theorem case_diag (i : Fin 24) :
    theta (signLiftPair e) (tauB (tbasis (.inl i))) = tauB (rhoEquiv (XQ e) (tbasis (.inl i))) := by
  rw [tauB_diag, theta_sign_diag, rho_diag, tauB_diag]

theorem tbasis_pair_one_eq (p : LtPair) :
    tbasis (.inr (.inl (p, 1))) =
      ((0 : symMat), Xlift (rMinus p.1.1 p.1.2), (0 : SpaceW)) -
        ((0 : symMat), Xlift (rPlus p.1.1 p.1.2), (0 : SpaceW)) := by
  rw [tbasis_pair_one, Prod.mk_sub_mk, Prod.mk_sub_mk, sub_zero, sub_zero]

theorem tbasis_pair_two_eq (p : LtPair) :
    tbasis (.inr (.inl (p, 2))) =
      ((0 : symMat), Xlift (rMinus p.1.1 p.1.2), (0 : SpaceW)) +
        ((0 : symMat), Xlift (rPlus p.1.1 p.1.2), (0 : SpaceW)) := by
  rw [tbasis_pair_two, Prod.mk_add_mk, Prod.mk_add_mk, add_zero, add_zero]

theorem rho_rMinus (i j : Fin 24) :
    rhoEquiv (XQ e) ((0 : symMat), Xlift (rMinus i j), (0 : SpaceW)) =
      sgn (pair e.code (deltaPair i j)) • ((0 : symMat), Xlift (rMinus i j), (0 : SpaceW)) := by
  rw [rho_X, symm_rMinus]
  simp only [θ_zero_right, zero_add]

theorem rho_rPlus (i j : Fin 24) :
    rhoEquiv (XQ e) ((0 : symMat), Xlift (rPlus i j), (0 : SpaceW)) =
      sgn (pair e.code (deltaPair i j)) • ((0 : symMat), Xlift (rPlus i j), (0 : SpaceW)) := by
  rw [rho_X, symm_rPlus]
  simp only [θ_ΩC_right, zero_add]

theorem theta_sign_pair_zero (p : LtPair) :
    theta (signLiftPair e) (tbasis (.inr (.inl (p, 0)))) =
      sgn (pair e.code (deltaPair p.1.1 p.1.2)) • tbasis (.inr (.inl (p, 0))) := by
  rw [tbasis_pair_zero, theta_sign_A, thetaA_gmat_basisA, pair_deltaPair, mk_A_smul]

theorem theta_sign_pair_one (p : LtPair) :
    theta (signLiftPair e) (tbasis (.inr (.inl (p, 1)))) = tbasis (.inr (.inl (p, 1))) := by
  rw [tbasis_pair_one_eq, map_sub, theta_sign_X, theta_sign_X]
  rcases zmod2_cases (pair e.code (deltaPair p.1.1 p.1.2)) with h | h
  · rw [Xlift_conjYQ_rMinus_of_zero e h, Xlift_conjYQ_rPlus_of_zero e h]
  · rw [Xlift_conjYQ_rMinus_of_one e h, Xlift_conjYQ_rPlus_of_one e h, mk_zero_X_neg,
      mk_zero_X_neg, neg_sub_neg]

theorem theta_sign_pair_two (p : LtPair) :
    theta (signLiftPair e) (tbasis (.inr (.inl (p, 2)))) =
      sgn (pair e.code (deltaPair p.1.1 p.1.2)) • tbasis (.inr (.inl (p, 2))) := by
  rw [tbasis_pair_two_eq, map_add, theta_sign_X, theta_sign_X]
  rcases zmod2_cases (pair e.code (deltaPair p.1.1 p.1.2)) with h | h
  · rw [Xlift_conjYQ_rMinus_of_zero e h, Xlift_conjYQ_rPlus_of_zero e h, h, sgn_zero, one_smul]
  · rw [Xlift_conjYQ_rMinus_of_one e h, Xlift_conjYQ_rPlus_of_one e h, mk_zero_X_neg,
      mk_zero_X_neg, h, sgn_one']
    exact (neg_add_rev _ _).symm.trans (neg_one_smul ℚ _).symm

theorem rho_pair_zero (p : LtPair) :
    rhoEquiv (XQ e) (tbasis (.inr (.inl (p, 0)))) = tbasis (.inr (.inl (p, 0))) := by
  rw [tbasis_pair_zero]
  exact rhoEquiv_symMat _ _

theorem rho_pair_one (p : LtPair) :
    rhoEquiv (XQ e) (tbasis (.inr (.inl (p, 1)))) =
      sgn (pair e.code (deltaPair p.1.1 p.1.2)) • tbasis (.inr (.inl (p, 1))) := by
  rw [tbasis_pair_one_eq, map_sub, rho_rMinus, rho_rPlus, smul_sub]

theorem rho_pair_two (p : LtPair) :
    rhoEquiv (XQ e) (tbasis (.inr (.inl (p, 2)))) =
      sgn (pair e.code (deltaPair p.1.1 p.1.2)) • tbasis (.inr (.inl (p, 2))) := by
  rw [tbasis_pair_two_eq, map_add, rho_rMinus, rho_rPlus, smul_add]

theorem case_pair (p : LtPair) (k : Fin 3) :
    theta (signLiftPair e) (tauB (tbasis (.inr (.inl (p, k))))) =
      tauB (rhoEquiv (XQ e) (tbasis (.inr (.inl (p, k))))) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [tauB_pair, rho_pair_zero, tauB_pair, show (0 : Fin 3) + 1 = 1 from rfl,
      theta_sign_pair_one]
  · rw [tauB_pair, rho_pair_one, map_smul, tauB_pair, show (1 : Fin 3) + 1 = 2 from rfl,
      theta_sign_pair_two]
  · rw [tauB_pair, rho_pair_two, map_smul, tauB_pair, show (2 : Fin 3) + 1 = 0 from rfl,
      theta_sign_pair_zero]

theorem theta_sign_odd_zero (c : C₀) (i : Fin 24) :
    theta (signLiftPair e) (tbasis (.inr (.inr (.inl (c, i, 0))))) =
      sgn (e.sign + θ (c : C) e.code) • tbasis (.inr (.inr (.inl (shift e.code c, i, 0)))) := by
  rw [tbasis_odd_zero, theta_sign_X, Xlift_conjYQ_rOdd, mk_zero_X_smul, tbasis_odd_zero]

theorem theta_sign_odd_one (c : C₀) (i : Fin 24) :
    theta (signLiftPair e) (tbasis (.inr (.inr (.inl (c, i, 1))))) =
      sgn (K (e.code : Fin 24 → ZMod 2) ((c : C) : Fin 24 → ZMod 2) +
        (e.code : Fin 24 → ZMod 2) i) • tbasis (.inr (.inr (.inl (c, i, 1)))) := by
  rw [tbasis_odd_one, mk_zero_zero_smul', map_smul, theta_sign_W, E_one_vecMul_Ymat,
    single_vecMul_gmat, tensor_smul_smul, mk_zero_zero_smul', smul_smul, smul_smul]
  congr 1
  rw [sgn_add]
  ring

theorem theta_sign_odd_two (c : C₀) (i : Fin 24) :
    theta (signLiftPair e) (tbasis (.inr (.inr (.inl (c, i, 2))))) =
      sgn (P ((c : C) : Fin 24 → ZMod 2) + e.sign + θ (c : C) e.code +
        (e.code : Fin 24 → ZMod 2) i + P ((shift e.code c : C) : Fin 24 → ZMod 2)) •
        tbasis (.inr (.inr (.inl (shift e.code c, i, 2)))) := by
  rw [tbasis_odd_two, mk_zero_zero_smul', map_smul, theta_sign_W, E_zero_vecMul_Ymat,
    single_vecMul_gmat, tensor_smul_smul, mk_zero_zero_smul', smul_smul, tbasis_odd_two,
    mk_zero_zero_smul', smul_smul]
  congr 1
  have h := sgn_mul_self (P ((shift e.code c : C) : Fin 24 → ZMod 2))
  simp only [sgn_add]
  linear_combination (-(sgn (P ((c : C) : Fin 24 → ZMod 2)) * sgn e.sign *
    sgn (θ (c : C) e.code) * sgn ((e.code : Fin 24 → ZMod 2) i))) * h

theorem rho_odd_zero (c : C₀) (i : Fin 24) :
    rhoEquiv (XQ e) (tbasis (.inr (.inr (.inl (c, i, 0))))) =
      sgn (K (e.code : Fin 24 → ZMod 2) ((c : C) : Fin 24 → ZMod 2) +
        (e.code : Fin 24 → ZMod 2) i) • tbasis (.inr (.inr (.inl (c, i, 0)))) := by
  rw [tbasis_odd_zero, rho_X, symm_rOdd]
  simp only [map_add, pair_thetaD, pair_single, θ_aOdd_left, θ_aOdd_right]
  rw [← add_assoc, θ_add_θ_swap]

theorem rho_odd_one (c : C₀) (i : Fin 24) :
    rhoEquiv (XQ e) (tbasis (.inr (.inr (.inl (c, i, 1))))) =
      sgn (((c : C) : Fin 24 → ZMod 2) i + (e.sign + P (e.code : Fin 24 → ZMod 2) +
        θ e.code (c : C) + μ₀ e.code) + ((shift e.code c : C) : Fin 24 → ZMod 2) i) •
        tbasis (.inr (.inr (.inl (shift e.code c, i, 1)))) := by
  rw [tbasis_odd_one, mk_zero_zero_smul', map_smul, rho_W, E_vecMul_Xmat, tensor_smul_left,
    mk_zero_zero_smul', smul_smul, tbasis_odd_one, mk_zero_zero_smul', smul_smul]
  congr 1
  have h := sgn_mul_self (((shift e.code c : C) : Fin 24 → ZMod 2) i)
  simp only [sgn_add, one_mul]
  linear_combination (-(sgn (((c : C) : Fin 24 → ZMod 2) i) * (sgn e.sign *
    sgn (P (e.code : Fin 24 → ZMod 2)) * sgn (θ e.code (c : C)) * sgn (μ₀ e.code)))) * h

theorem rho_odd_two (c : C₀) (i : Fin 24) :
    rhoEquiv (XQ e) (tbasis (.inr (.inr (.inl (c, i, 2))))) =
      sgn (P ((c : C) : Fin 24 → ZMod 2) + (e.sign + P (e.code : Fin 24 → ZMod 2) +
        θ e.code (c : C)) + P ((shift e.code c : C) : Fin 24 → ZMod 2)) •
        tbasis (.inr (.inr (.inl (shift e.code c, i, 2)))) := by
  rw [tbasis_odd_two, mk_zero_zero_smul', map_smul, rho_W, E_vecMul_Xmat, tensor_smul_left,
    mk_zero_zero_smul', smul_smul, tbasis_odd_two, mk_zero_zero_smul', smul_smul]
  congr 1
  have h := sgn_mul_self (P ((shift e.code c : C) : Fin 24 → ZMod 2))
  simp only [sgn_add, zero_mul, add_zero]
  linear_combination (-(sgn (P ((c : C) : Fin 24 → ZMod 2)) * (sgn e.sign *
    sgn (P (e.code : Fin 24 → ZMod 2)) * sgn (θ e.code (c : C))))) * h

theorem case_odd (c : C₀) (i : Fin 24) (k : Fin 3) :
    theta (signLiftPair e) (tauB (tbasis (.inr (.inr (.inl (c, i, k)))))) =
      tauB (rhoEquiv (XQ e) (tbasis (.inr (.inr (.inl (c, i, k)))))) := by
  have hK := θ_add_θ_swap e.code (c : C)
  have hP := P_coe_shift e.code c
  have hc := coe_shift_apply e.code c i
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by fin_cases k <;> simp
  · rw [tauB_odd, rho_odd_zero, map_smul, tauB_odd, show (0 : Fin 3) + 1 = 1 from rfl,
      theta_sign_odd_one]
  · rw [tauB_odd, rho_odd_one, map_smul, tauB_odd, show (1 : Fin 3) + 1 = 2 from rfl,
      theta_sign_odd_two]
    refine congrArg (fun t => sgn t • tbasis (.inr (.inr (.inl (shift e.code c, i, 2))))) ?_
    rw [K_comm] at hP
    linear_combination (norm := (ring_nf; try reduce_mod_char)) hP + hc - hK
  · rw [tauB_odd, rho_odd_two, map_smul, tauB_odd, show (2 : Fin 3) + 1 = 0 from rfl,
      theta_sign_odd_zero]
    refine congrArg (fun t => sgn t • tbasis (.inr (.inr (.inl (shift e.code c, i, 0))))) ?_
    rw [K_comm] at hP
    linear_combination (norm := (ring_nf; try reduce_mod_char)) hP - hK

@[expose] def octCls (a : C) (d : OctadWord) : Octad.EvenQuot (octSupp d) :=
  Octad.cls (octSupp d) (octMeet a d)

theorem quadForm_octCls (a : C) (d : OctadWord) :
    Octad.quadForm (octSupp d) (octCls a d) =
      K (a : Fin 24 → ZMod 2) ((d : C) : Fin 24 → ZMod 2) := by
  rw [octCls, Octad.quadForm_cls (four_dvd_card_octSupp d) (octMeet_subset a d)
    (even_card_octMeet a d), K_eq_card_octMeet]

theorem polar_octCls (a : C) (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v (octCls a d) =
      (a : Fin 24 → ZMod 2) ⬝ᵥ Octad.ind (octRep d v) := by
  obtain ⟨h1, h2, h3⟩ := octRep_spec d v
  conv_lhs => rw [← h3]
  rw [octCls, Octad.polarBilin_quadForm_cls (four_dvd_card_octSupp d) h1 h2 (octMeet_subset a d)
    (even_card_octMeet a d), dotProduct_ind a d h1]

theorem tbasis_oct' (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tbasis (.inr (.inr (.inr ⟨d, v⟩))) =
      ((0 : symMat), Xlift (rOct d (octRep d v)), (0 : SpaceW)) :=
  tbasis_oct ⟨d, v⟩

theorem theta_sign_oct (d : OctadWord) (w : Octad.EvenQuot (octSupp d)) :
    theta (signLiftPair e) (tbasis (.inr (.inr (.inr ⟨d, w⟩)))) =
      sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) w (octCls e.code d)) •
        tbasis (.inr (.inr (.inr ⟨d, w + octCls e.code d⟩))) := by
  obtain ⟨h1, h2, h3⟩ := octRep_spec d w
  have hm := octMeet_subset e.code d
  have hme := even_card_octMeet e.code d
  have hcls : Octad.cls (octSupp d) (octRep d w ∆ octMeet e.code d) = w + octCls e.code d := by
    rw [cls_symmDiff h1 h2 hm hme, h3, octCls]
  have hr : rOct d (octRep d w ∆ octMeet e.code d) = rOctQ d (w + octCls e.code d) := by
    rw [← hcls, rOctQ_cls (symmDiff_subset h1 hm) (even_card_symmDiff h1 h2 hm hme)]
  rw [tbasis_oct', theta_sign_X, Xlift_conjYQ_rOct e d h1 h2, mk_zero_X_smul, hr, polar_octCls,
    tbasis_oct ⟨d, w + octCls e.code d⟩]

theorem rho_oct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    rhoEquiv (XQ e) (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      sgn (Octad.quadForm (octSupp d) (octCls e.code d) +
        QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v (octCls e.code d)) •
        tbasis (.inr (.inr (.inr ⟨d, v⟩))) := by
  rw [tbasis_oct', rho_X, symm_rOct, quadForm_octCls, polar_octCls]
  simp only [map_add, pair_thetaD, pair_mk]
  rw [← add_assoc, θ_add_θ_swap, aOct, K_add_smul_ΩC_right]

theorem octHD_apply' (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    octHD d v w = ((2 : ℚ) ^ 3)⁻¹ *
      sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v w) *
        sgn (Octad.quadForm (octSupp d) w) := by
  rw [octHD, octD, signMatrix, mul_diagonal, octH, fourierMatrix]

theorem octHD_shift (d : OctadWord) (v u a' : Octad.EvenQuot (octSupp d)) :
    octHD d v (u + a') * sgn (QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) (u + a') a') =
      sgn (Octad.quadForm (octSupp d) a' +
        QuadraticMap.polarBilin (Octad.quadForm (octSupp d)) v a') * octHD d v u := by
  set Q := Octad.quadForm (octSupp d)
  have hq : Q (u + a') = Q u + Q a' + QuadraticMap.polarBilin Q u a' := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar]
    ring
  have hself : QuadraticMap.polarBilin Q a' a' = 0 := by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polar_self, two_smul]
    exact ZModModule.add_self _
  have hb1 : QuadraticMap.polarBilin Q v (u + a') =
      QuadraticMap.polarBilin Q v u + QuadraticMap.polarBilin Q v a' := map_add _ _ _
  have hb2 : QuadraticMap.polarBilin Q (u + a') a' =
      QuadraticMap.polarBilin Q u a' + QuadraticMap.polarBilin Q a' a' :=
    LinearMap.map_add₂ _ _ _ _
  rw [octHD_apply', octHD_apply', hb1, hq, hb2, hself, add_zero]
  have h := sgn_mul_self (QuadraticMap.polarBilin Q u a')
  simp only [sgn_add]
  linear_combination (((2 : ℚ) ^ 3)⁻¹ * sgn (QuadraticMap.polarBilin Q v u) *
    sgn (QuadraticMap.polarBilin Q v a') * sgn (Q u) * sgn (Q a')) * h

theorem case_oct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    theta (signLiftPair e) (tauB (tbasis (.inr (.inr (.inr ⟨d, v⟩))))) =
      tauB (rhoEquiv (XQ e) (tbasis (.inr (.inr (.inr ⟨d, v⟩))))) := by
  rw [tauB_oct, map_sum, rho_oct, map_smul, tauB_oct, Finset.smul_sum]
  simp only [map_smul, theta_sign_oct, smul_smul]
  have hshift : ∀ w : Octad.EvenQuot (octSupp d), w + octCls e.code d + octCls e.code d = w :=
    fun w => by rw [add_assoc, ZModModule.add_self, add_zero]
  refine Fintype.sum_equiv (Equiv.addRight (octCls e.code d)) _ _ fun w => ?_
  rw [Equiv.coe_addRight]
  have h := octHD_shift d v (w + octCls e.code d) (octCls e.code d)
  rw [hshift] at h
  rw [h]

theorem theta_signLiftPair_tauB_tbasis (x : TIdx) :
    theta (signLiftPair e) (tauB (tbasis x)) = tauB (rhoEquiv (XQ e) (tbasis x)) := by
  rcases x with i | ⟨p, k⟩ | ⟨c, i, k⟩ | ⟨d, v⟩
  · exact case_diag e i
  · exact case_pair e p k
  · exact case_odd e c i k
  · exact case_oct e d v

end SignCompat

open SignCompat

theorem thetaEquiv_signLiftPair_mul_tauB (e : Parker) :
    thetaEquiv (signLiftPair e) * tauB = tauB * rhoEquiv (XQ e) :=
  tbasis.ext' fun x => theta_signLiftPair_tauB_tbasis e x

theorem thetaEquiv_signLiftPair (e : Parker) :
    thetaEquiv (signLiftPair e) = tauB * rhoEquiv (XQ e) * tauB⁻¹ := by
  rw [← thetaEquiv_signLiftPair_mul_tauB, mul_inv_cancel_right]

end CFSG.Monster.Visible
