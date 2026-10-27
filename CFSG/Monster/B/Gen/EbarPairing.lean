
module

public import CFSG.Monster.B.Gen.GenerationBase

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot
open scoped commutatorElement

theorem Q_mul_eq_mul_mul_zQ_pow (q q' : Q) :
    q * q' = q' * q *
      zQ ^ (QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q'))).val := by
  have hc : ⁅q, q'⁆ ∈ commutator Q :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top q) (Subgroup.mem_top q')
  rw [Spin.commutator_Q] at hc
  obtain ⟨f, hf⟩ : ∃ f : ZMod 2, ⁅q, q'⁆ = zQ ^ f.val := by
    rcases (mem_zpowers_iff_of_orderOf_eq_two Spin.orderOf_zQ).1 hc with h | h
    · exact ⟨0, by rw [h, ZMod.val_zero, pow_zero]⟩
    · exact ⟨1, by rw [h]; exact (pow_one zQ).symm⟩
  have hb : QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q')) = f :=
    (congrArg₂ (fun x y => QuadraticMap.polarBilin qL x y) (toAdd_phi_mk q)
      (toAdd_phi_mk q')).symm.trans (bL_phi_of_commutator hf)
  have hcomm : q * q' = ⁅q, q'⁆ * (q' * q) := by
    rw [commutatorElement_def]
    group
  calc q * q' = ⁅q, q'⁆ * (q' * q) := hcomm
    _ = zQ ^ f.val * (q' * q) := congrArg (· * (q' * q)) hf
    _ = q' * q * zQ ^ f.val :=
        (Subgroup.mem_center_iff.1 (Subgroup.pow_mem _ Short.zQ_mem_center _) (q' * q)).symm
    _ = q' * q * zQ ^ (QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q'))).val :=
        congrArg (fun t : ZMod 2 => q' * q * zQ ^ t.val) hb.symm

@[expose] noncomputable def krHom : Subgroup.centralizer ({rStar} : Set Q) →* Cbar :=
  kappa.comp ((rhoHom.comp (Subgroup.centralizer ({rStar} : Set Q)).subtype).codRestrict Cgen
    fun x => by
      rw [MonoidHom.comp_apply, rhoHom_apply]
      exact rhoEquiv_mem_Cgen (Subgroup.inv_mem _ x.2))

theorem krHom_inv_eq {q : Q} (hq : q ∈ Subgroup.centralizer {rStar}) :
    krHom ⟨q⁻¹, Subgroup.inv_mem _ hq⟩ = kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ := by
  unfold krHom
  rw [MonoidHom.comp_apply]
  refine congrArg kappa (Subtype.ext ?_)
  show rhoHom q⁻¹ = rhoEquiv q
  rw [rhoHom_apply, inv_inv]

theorem krHom_zQ : krHom ⟨zQ, zQ_mem_centralizer_rStar⟩ = xbar := by
  unfold krHom
  rw [MonoidHom.comp_apply]
  show kappa _ = kappa xC
  refine congrArg kappa (Subtype.ext ?_)
  show rhoHom zQ = xmat
  exact rhoHom_zQ

theorem xbar_comm_of_mem_Ebar {y : Cbar} (hy : y ∈ Ebar) : y * xbar = xbar * y :=
  congrArg Subtype.val (xbarE_comm ⟨y, hy⟩)

theorem qL_phi0_coordOf_rStar : qL (phi0 (coordOf rStar)) = 0 :=
  (mul_self_eq_one_iff_qL rStar).1 rStar_mul_self

noncomputable abbrev bW : LinearMap.BilinForm (ZMod 2) (Wv (phi0 (coordOf rStar))) :=
  QuadraticMap.polarBilin (qW _ qL_phi0_coordOf_rStar)

theorem kappa_rho_mul_eq {q q' : Q} (hq : q ∈ Subgroup.centralizer {rStar})
    (hq' : q' ∈ Subgroup.centralizer {rStar}) :
    kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * kappa ⟨rhoEquiv q', rhoEquiv_mem_Cgen hq'⟩ =
      kappa ⟨rhoEquiv q', rhoEquiv_mem_Cgen hq'⟩ * kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ *
        xbar ^ (QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q'))).val := by
  have hQ : (⟨q⁻¹, Subgroup.inv_mem _ hq⟩ * ⟨q'⁻¹, Subgroup.inv_mem _ hq'⟩ :
      Subgroup.centralizer ({rStar} : Set Q)) =
      ⟨q'⁻¹, Subgroup.inv_mem _ hq'⟩ * ⟨q⁻¹, Subgroup.inv_mem _ hq⟩ *
        ⟨zQ, zQ_mem_centralizer_rStar⟩ ^
          (QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q'))).val := by
    apply Subtype.ext
    have h := Q_mul_eq_mul_mul_zQ_pow q⁻¹ q'⁻¹
    rw [phi0_coordOf_inv, phi0_coordOf_inv] at h
    exact h
  calc kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ * kappa ⟨rhoEquiv q', rhoEquiv_mem_Cgen hq'⟩
      = krHom ⟨q⁻¹, Subgroup.inv_mem _ hq⟩ * krHom ⟨q'⁻¹, Subgroup.inv_mem _ hq'⟩ :=
        congrArg₂ (· * ·) (krHom_inv_eq hq).symm (krHom_inv_eq hq').symm
    _ = krHom (⟨q⁻¹, Subgroup.inv_mem _ hq⟩ * ⟨q'⁻¹, Subgroup.inv_mem _ hq'⟩) :=
        (map_mul krHom _ _).symm
    _ = krHom (⟨q'⁻¹, Subgroup.inv_mem _ hq'⟩ * ⟨q⁻¹, Subgroup.inv_mem _ hq⟩ *
          ⟨zQ, zQ_mem_centralizer_rStar⟩ ^
            (QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q'))).val) :=
        congrArg krHom hQ
    _ = krHom ⟨q'⁻¹, Subgroup.inv_mem _ hq'⟩ * krHom ⟨q⁻¹, Subgroup.inv_mem _ hq⟩ *
          krHom ⟨zQ, zQ_mem_centralizer_rStar⟩ ^
            (QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q'))).val :=
        (map_mul krHom _ _).trans (congrArg₂ (· * ·) (map_mul krHom _ _) (map_pow krHom _ _))
    _ = _ := congrArg₂ (· * ·) (congrArg₂ (· * ·) (krHom_inv_eq hq') (krHom_inv_eq hq))
          (congrArg (· ^ _) krHom_zQ)

theorem Ebar_mul_eq_mul_xbar_pow (e e' : Ebar) :
    (e : Cbar) * e' = e' * e *
      xbar ^ (bW (Multiplicative.toAdd (psiBar e)) (Multiplicative.toAdd (psiBar e'))).val := by
  obtain ⟨q, hq, rfl⟩ := exists_rep_Ebar e
  obtain ⟨q', hq', rfl⟩ := exists_rep_Ebar e'
  have hpsi : bW (Multiplicative.toAdd (psiBar ⟨kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩,
        kappa_rho_mem_Ebar hq⟩)) (Multiplicative.toAdd (psiBar ⟨kappa ⟨rhoEquiv q',
        rhoEquiv_mem_Cgen hq'⟩, kappa_rho_mem_Ebar hq'⟩)) =
      QuadraticMap.polarBilin qL (phi0 (coordOf q)) (phi0 (coordOf q')) :=
    (congrArg₂ (fun x y => bW (Multiplicative.toAdd x) (Multiplicative.toAdd y))
      (psiBar_kappa_rho hq) (psiBar_kappa_rho hq')).trans (polarBilin_qW_mk _ _ _ _)
  exact (kappa_rho_mul_eq hq hq').trans (congrArg (fun t : ZMod 2 =>
    kappa ⟨rhoEquiv q', rhoEquiv_mem_Cgen hq'⟩ * kappa ⟨rhoEquiv q, rhoEquiv_mem_Cgen hq⟩ *
      xbar ^ t.val) hpsi.symm)

theorem eq_of_xbar_pow_val_eq {a b : ZMod 2} (h : xbar ^ a.val = xbar ^ b.val) : a = b := by
  apply ZMod.val_injective
  by_contra hne
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  have hcases : (a.val = 0 ∧ b.val = 1) ∨ (a.val = 1 ∧ b.val = 0) := by omega
  rcases hcases with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, pow_zero, pow_one] at h
    exact xbar_ne_one h.symm
  · rw [h1, h2, pow_zero, pow_one] at h
    exact xbar_ne_one h

theorem gram_rel_of_lt {e : Fin 22 → Cbar}
    (G : Matrix (Fin 22) (Fin 22) (ZMod 2)) (hsymm : ∀ i j, G i j = G j i)
    (hdiag : ∀ i, G i i = 0)
    (hG : ∀ i j, i < j → e i * e j = e j * e i * xbar ^ (G i j).val) :
    ∀ i j, e i * e j = e j * e i * xbar ^ (G i j).val := by
  intro i j
  rcases lt_trichotomy i j with h | rfl | h
  · exact hG i j h
  · rw [hdiag, ZMod.val_zero, pow_zero, mul_one]
  · have h1 := hG j i h
    rw [hsymm j i] at h1
    have hx2 : xbar ^ (G i j).val * xbar ^ (G i j).val = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, show xbar ^ 2 = 1 by rw [pow_two]; exact xbar_mul_self,
        one_pow]
    calc e i * e j = e i * e j * xbar ^ (G i j).val * xbar ^ (G i j).val := by
          rw [mul_assoc (e i * e j), hx2, mul_one]
      _ = e j * e i * xbar ^ (G i j).val := by rw [← h1]

theorem linearIndependent_psi_of_gram (e : Fin 22 → Cbar) (he : ∀ i, e i ∈ Ebar)
    (G H : Matrix (Fin 22) (Fin 22) (ZMod 2)) (hGH : G * H = 1)
    (hG : ∀ i j, e i * e j = e j * e i * xbar ^ (G i j).val) :
    LinearIndependent (ZMod 2) fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩) := by
  set w : Fin 22 → Wv (phi0 (coordOf rStar)) := fun i => Multiplicative.toAdd (psiBar ⟨e i, he i⟩)
  have hBG : ∀ i j, bW (w i) (w j) = G i j := by
    intro i j
    have h1 : e i * e j = e j * e i * xbar ^ (bW (w i) (w j)).val :=
      Ebar_mul_eq_mul_xbar_pow ⟨e i, he i⟩ ⟨e j, he j⟩
    rw [hG i j] at h1
    exact (eq_of_xbar_pow_val_eq (mul_left_cancel h1)).symm
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hk : Matrix.vecMul c G = 0 := by
    funext k
    have h := congrArg (fun x => bW x (w k)) hc
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_zero, LinearMap.zero_apply, hBG] at h
    exact h
  have hc' : c = Matrix.vecMul (Matrix.vecMul c G) H := by
    rw [Matrix.vecMul_vecMul, hGH, Matrix.vecMul_one]
  intro i
  rw [hc', hk, Matrix.zero_vecMul]
  rfl

end CFSG.Monster.B
