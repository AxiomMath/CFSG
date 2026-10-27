module

public import CFSG.Monster.Visible.Action
public import CFSG.Monster.B.Short.InvolutionCentralizer
public import CFSG.Monster.Griess.AxisSpectrum

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Short

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.ScalarKernel CFSG.Monster.Visible Matrix Subgroup
open scoped commutatorElement

theorem griess_ratVec_eq (v : Fin 24 → ℤ) : Griess.ratVec v = ScalarKernel.ratVec v := rfl

theorem transpose_mul_smul_vecMulVec_mul (g : Matrix (Fin 24) (Fin 24) ℚ) (a : Fin 24 → ℚ) :
    gᵀ * ((32 : ℚ)⁻¹ • vecMulVec a a) * g = (32 : ℚ)⁻¹ • vecMulVec (a ᵥ* g) (a ᵥ* g) := by
  rw [Matrix.mul_smul, Matrix.smul_mul, mul_vecMulVec, vecMulVec_mul, mulVec_transpose]

theorem transpose_mul_projMat_mul (g : latticeO) {u : Fin 24 → ℤ} (hu : u ∈ codeLattice C) :
    (mat g)ᵀ * projMat u * mat g = projMat (latVec (mat g) u) := by
  have h : ScalarKernel.ratVec (latVec (mat g) u) = ScalarKernel.ratVec u ᵥ* mat g :=
    (latVec_spec g hu).2
  have e1 : projMat u = (32 : ℚ)⁻¹ • vecMulVec (ScalarKernel.ratVec u) (ScalarKernel.ratVec u) :=
    rfl
  have e2 : projMat (latVec (mat g) u) = (32 : ℚ)⁻¹ • vecMulVec
      (ScalarKernel.ratVec (latVec (mat g) u)) (ScalarKernel.ratVec (latVec (mat g) u)) := rfl
  rw [e1, e2, h]
  exact transpose_mul_smul_vecMulVec_mul (mat g) (ScalarKernel.ratVec u)

theorem axisE_conjQ (p : Pvis) {r : Q} (hr : IsShortCoord (coordOf r)) :
    (axisE (conjQ p r) : Matrix (Fin 24) (Fin 24) ℚ) =
      (mat p.1.2)ᵀ * (axisE r : Matrix (Fin 24) (Fin 24) ℚ) * mat p.1.2 := by
  obtain ⟨hu, hcl, -⟩ := uvec_spec ⟨coordOf r, hr⟩
  have hcl' : classOf (latVec (mat p.1.2) (uvec ⟨coordOf r, hr⟩)) = phi0 (coordOf (conjQ p r)) :=
    (classOf_latVec p.1.2 hu.1).trans ((congrArg (modTwoEnd p.1.2) hcl).trans
      (((congrArg (modTwoEnd p.1.2) (toAdd_phi_mk r).symm).trans (phi_conjQ p r).symm).trans
        (toAdd_phi_mk (conjQ p r))))
  exact (axisE_eq_projMat (isShortCoord_conjQ p hr) (latVec_mem_minVecs p.1.2 hu) hcl').trans
    ((transpose_mul_projMat_mul p.1.2 hu.1).symm.trans
      (congrArg (fun M => (mat p.1.2)ᵀ * M * mat p.1.2) (coe_axisE hr).symm))

theorem theta_axis (p : Pvis) {r : Q} (hr : IsShortCoord (coordOf r)) :
    theta p (axis r) = axis (conjQ p r) := by
  have hA : thetaA (mat p.1.2) (axisE r) = axisE (conjQ p r) :=
    Subtype.ext ((coe_thetaA _ _).trans (axisE_conjQ p hr).symm)
  calc theta p (axis r)
      = theta p ((2 : ℚ) • ((axisE r, 0, 0) : SpaceB) - (2 : ℚ) • ((0, Xlift r, 0) : SpaceB)) := rfl
    _ = (2 : ℚ) • theta p ((axisE r, 0, 0) : SpaceB) -
        (2 : ℚ) • theta p ((0, Xlift r, 0) : SpaceB) := by rw [map_sub, map_smul, map_smul]
    _ = (2 : ℚ) • ((thetaA (mat p.1.2) (axisE r), 0, 0) : SpaceB) -
        (2 : ℚ) • ((0, Xlift (conjQ p r), 0) : SpaceB) := by rw [theta_symMat, theta_Xlift]
    _ = (2 : ℚ) • ((axisE (conjQ p r), 0, 0) : SpaceB) -
        (2 : ℚ) • ((0, Xlift (conjQ p r), 0) : SpaceB) := by rw [hA]
    _ = axis (conjQ p r) := rfl

theorem thetaEquiv_axis (p : Pvis) {r : Q} (hr : IsShortCoord (coordOf r)) :
    thetaEquiv p (axis r) = axis (conjQ p r) :=
  theta_axis p hr

theorem inv_mul_rhoPair_mul (p : Pvis) (r : Q) : p⁻¹ * rhoPair r * p = rhoPair (conjQ p r) := by
  apply Subtype.ext
  refine Prod.ext rfl ?_
  show p.1.2⁻¹ * 1 * p.1.2 = 1
  rw [mul_one, inv_mul_cancel]

theorem thetaEquiv_conj_rhoEquiv (p : Pvis) (r : Q) :
    thetaEquiv p * rhoEquiv r * (thetaEquiv p)⁻¹ = rhoEquiv (conjQ p r) := by
  calc thetaEquiv p * rhoEquiv r * (thetaEquiv p)⁻¹
      = thetaEquiv p * (thetaEquiv (rhoPair r) * thetaEquiv p⁻¹) := by
        rw [thetaEquiv_inv, mul_assoc]; rfl
    _ = thetaEquiv (p⁻¹ * rhoPair r * p) := by rw [thetaEquiv_mul, thetaEquiv_mul]
    _ = rhoEquiv (conjQ p r) := by rw [inv_mul_rhoPair_mul]; rfl

section Generic

variable {G : Type*} [Group G]

theorem conj_eq_mul_of_commutatorElement {z s q : G} (hz : z ∈ center G) (hc : ⁅s, q⁆ = z) :
    q⁻¹ * s * q = z * s := by
  have h1 : s * q = z * (q * s) := by rw [← hc]; group
  have h2 : q⁻¹ * z * q = z := by
    rw [mul_assoc, ← (mem_center_iff.1 hz q), inv_mul_cancel_left]
  calc q⁻¹ * s * q = q⁻¹ * (s * q) := mul_assoc _ _ _
    _ = q⁻¹ * z * q * s := by rw [h1]; group
    _ = z * s := by rw [h2]

theorem conj_mul_eq_of_conj {z s q : G} (hz : z ∈ center G) (hzz : z * z = 1)
    (hq : q⁻¹ * s * q = z * s) : q⁻¹ * (z * s) * q = s := by
  calc q⁻¹ * (z * s) * q = (q⁻¹ * z * q) * (q⁻¹ * s * q) := by group
    _ = z * (z * s) := by rw [mul_assoc q⁻¹ z q, ← (mem_center_iff.1 hz q), inv_mul_cancel_left, hq]
    _ = s := by rw [← mul_assoc, hzz, one_mul]

theorem eq_or_eq_mul_of_mul_inv_eq {z r s : G} (h : r * s⁻¹ = 1 ∨ r * s⁻¹ = z) :
    r = s ∨ r = z * s := by
  rcases h with h | h
  · exact .inl (mul_inv_eq_one.1 h)
  · right
    rw [← h, inv_mul_cancel_right]

end Generic

theorem projQ_eq_ofAdd_coordOf (r : Q) : projQ r = Multiplicative.ofAdd (coordOf r) :=
  (congrArg projQ (spinEquiv.apply_symm_apply r).symm).trans (projQ_spinEquiv (spinEquiv.symm r))

theorem zQ_mem_center : zQ ∈ center Q := center_Q ▸ mem_zpowers zQ

theorem not_mem_center_of_isShortCoord {s : Q} (hs : IsShortCoord (coordOf s)) :
    s ∉ center Q := by
  intro hc
  have h1 : projQ s = 1 := MonoidHom.mem_ker.1 (ker_projQ.ge hc)
  have h2 : coordOf s = 0 := ofAdd_eq_one.1 ((projQ_eq_ofAdd_coordOf s).symm.trans h1)
  obtain ⟨u, hu, hcl⟩ := hs
  exact classOf_ne_zero_of_mem_minVecs hu (hcl.trans ((congrArg phi0 h2).trans (map_zero phi0)))

theorem exists_conj_eq_zQ_mul {s : Q} (hs : s ∉ center Q) : ∃ q : Q, q⁻¹ * s * q = zQ * s := by
  have hrange := range_commHom_eq_top isExtraspecialPGroup_Q hs
  have hmem : (⟨zQ, zQ_mem_center⟩ : center Q) ∈
      (commHom isExtraspecialPGroup_Q.commutator_eq.le s).range := by
    rw [hrange]
    exact mem_top _
  obtain ⟨q, hq⟩ := hmem
  exact ⟨q, conj_eq_mul_of_commutatorElement zQ_mem_center (congrArg Subtype.val hq)⟩

theorem zQ_mul_zQ : zQ * zQ = 1 := by
  have h := pow_orderOf_eq_one zQ
  rw [orderOf_zQ, pow_two] at h
  exact h

theorem eq_or_eq_zQ_mul_of_coordOf_eq {r s : Q} (h : coordOf r = coordOf s) :
    r = s ∨ r = zQ * s := by
  have h1 : projQ (r * s⁻¹) = 1 := by
    rw [map_mul, map_inv, projQ_eq_ofAdd_coordOf r, projQ_eq_ofAdd_coordOf s, h, mul_inv_cancel]
  have hk : r * s⁻¹ ∈ zpowers zQ := center_Q.le (ker_projQ.le (MonoidHom.mem_ker.2 h1))
  exact eq_or_eq_mul_of_mul_inv_eq ((mem_zpowers_iff_of_orderOf_eq_two orderOf_zQ).1 hk)

theorem exists_conjQ_eq {r s : Q} (hs : IsShortCoord (coordOf s)) (p : Pvis)
    (h : modTwoEnd p.1.2 (phi0 (coordOf r)) = phi0 (coordOf s)) :
    ∃ p' : Pvis, conjQ p' r = s ∧ p'.1.2 = p.1.2 := by
  have hcl : phi0 (coordOf (conjQ p r)) = phi0 (coordOf s) :=
    (toAdd_phi_mk (conjQ p r)).symm.trans ((phi_conjQ p r).trans
      ((congrArg (modTwoEnd p.1.2) (toAdd_phi_mk r)).trans h))
  rcases eq_or_eq_zQ_mul_of_coordOf_eq (phi0_injective hcl) with h1 | h1
  · exact ⟨p, h1, rfl⟩
  · obtain ⟨q, hq⟩ := exists_conj_eq_zQ_mul (not_mem_center_of_isShortCoord hs)
    have hzc : zQ ∈ center Q := zQ_mem_center
    refine ⟨p * rhoPair q, ?_, ?_⟩
    · exact (conjQ_mul p (rhoPair q) r).trans ((congrArg (conjQ (rhoPair q)) h1).trans
        ((conjQ_rhoPair q (zQ * s)).trans (conj_mul_eq_of_conj hzc zQ_mul_zQ hq)))
    · show p.1.2 * 1 = p.1.2
      rw [mul_one]

theorem exists_Gvis_conj_rho_axis {r s : Q} (hr : IsShortCoord (coordOf r))
    (hs : IsShortCoord (coordOf s)) (p : Pvis)
    (h : modTwoEnd p.1.2 (phi0 (coordOf r)) = phi0 (coordOf s)) :
    ∃ f ∈ Gvis, f * rhoEquiv r * f⁻¹ = rhoEquiv s ∧ f (axis r) = axis s := by
  obtain ⟨p', hp', -⟩ := exists_conjQ_eq hs p h
  refine ⟨thetaEquiv p', thetaEquiv_mem_Gvis p', ?_, ?_⟩
  · rw [thetaEquiv_conj_rhoEquiv, hp']
  · rw [thetaEquiv_axis p' hr, hp']

end CFSG.Monster.B.Short
