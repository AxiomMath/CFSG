
module


public import CFSG.Sporadic.ThSchreier.Perfect
public import CFSG.Sporadic.ThSchreier.Max3ActionBase

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped commutatorElement

@[expose] noncomputable def conjQ
    (m : ↥M) : Q →* Q where
  toFun g := ⟨m * g * (m : J)⁻¹, AltQuot.conj_mem_Q_of_mem_M m.2 g.2⟩
  map_one' := by
    apply Subtype.ext
    show (m : J) * 1 * (m : J)⁻¹ = 1
    group
  map_mul' g h := by
    apply Subtype.ext
    show (m : J) * ((g : J) * h) * (m : J)⁻¹ =
      (m : J) * g * (m : J)⁻¹ * ((m : J) * h * (m : J)⁻¹)
    group

theorem conjQ_apply
    (m : ↥M) (g : Q) : (conjQ m g : J) = m * g * (m : J)⁻¹ := rfl

theorem conjQ_mul
    (m n : ↥M) : conjQ (m * n) = (conjQ m).comp (conjQ n) := by
  refine MonoidHom.ext fun g => Subtype.ext ?_
  show ((m * n : ↥M) : J) * g * ((m * n : ↥M) : J)⁻¹ =
    (m : J) * ((n : J) * g * (n : J)⁻¹) * (m : J)⁻¹
  simp only [Subgroup.coe_mul]
  group

theorem conjQ_center_le (m : ↥M) :
    Subgroup.center Q ≤ (Subgroup.center Q).comap (conjQ m) := by
  rintro ⟨g, hgQ⟩ hg
  rw [Subgroup.mem_comap]
  have hg' := hg
  rw [center_Q, Subgroup.mem_subgroupOf] at hg'
  have hc : conjQ m ⟨g, hgQ⟩ = ⟨g, hgQ⟩ := by
    apply Subtype.ext
    show (m : J) * g * (m : J)⁻¹ = g
    exact AltQuot.conj_zpowers m.2 hg'
  rw [hc]
  exact hg

@[expose] noncomputable def rhoBar
    (m : ↥M) : Q ⧸ Subgroup.center Q →* Q ⧸ Subgroup.center Q :=
  QuotientGroup.map _ _ (conjQ m) (conjQ_center_le m)

theorem rhoBar_mk (m : ↥M) (g : Q) :
    rhoBar m (QuotientGroup.mk g) = QuotientGroup.mk (conjQ m g) := rfl

@[expose] noncomputable def rhoM
    (m : ↥M) :
    Multiplicative (Fin 8 → ZMod 2) →* Multiplicative (Fin 8 → ZMod 2) :=
  theta.symm.toMonoidHom.comp ((rhoBar m).comp theta.toMonoidHom)

theorem rhoM_piQ
    (m : ↥M) (g : Q) : rhoM m (piQ g) = piQ (conjQ m g) := by
  simp only [rhoM, piQ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply, QuotientGroup.mk'_apply]
  rfl

theorem piQ_surjective :
    Function.Surjective piQ := by
  intro v
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (theta v)
  refine ⟨g, ?_⟩
  simp only [piQ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
  rw [hg, MulEquiv.symm_apply_apply]

theorem rhoM_mul
    (m n : ↥M) : rhoM (m * n) = (rhoM m).comp (rhoM n) := by
  refine MonoidHom.ext fun v => ?_
  obtain ⟨g, rfl⟩ := piQ_surjective v
  simp only [MonoidHom.comp_apply, rhoM_piQ, conjQ_mul]

theorem conjQ_one
    (g : Q) : conjQ 1 g = g := by
  apply Subtype.ext
  show ((1 : ↥M) : J) * g * ((1 : ↥M) : J)⁻¹ = g
  simp

theorem rhoM_one :
    rhoM 1 = MonoidHom.id _ := by
  refine MonoidHom.ext fun v => ?_
  obtain ⟨g, rfl⟩ := piQ_surjective v
  exact (rhoM_piQ 1 g).trans (congrArg piQ (conjQ_one g))

@[expose] noncomputable def rhoLin
    (m : ↥M) : (Fin 8 → ZMod 2) →ₗ[ZMod 2] (Fin 8 → ZMod 2) where
  toFun v := Multiplicative.toAdd (rhoM m (Multiplicative.ofAdd v))
  map_add' v w := by
    show Multiplicative.toAdd (rhoM m (Multiplicative.ofAdd v * Multiplicative.ofAdd w)) = _
    rw [map_mul]
    rfl
  map_smul' c v := by
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases c with rfl | rfl
    · rw [zero_smul, RingHom.id_apply, zero_smul]
      show Multiplicative.toAdd (rhoM m 1) = 0
      rw [map_one]
      rfl
    · rw [one_smul, RingHom.id_apply, one_smul]

theorem rhoLin_apply
    (m : ↥M) (v : Fin 8 → ZMod 2) :
    rhoLin m v = Multiplicative.toAdd (rhoM m (Multiplicative.ofAdd v)) := rfl

@[expose] noncomputable def rhoMat
    (m : ↥M) : Matrix (Fin 8) (Fin 8) (ZMod 2) :=
  LinearMap.toMatrix' (rhoLin m)

theorem rhoMat_mulVec
    (m : ↥M) (v : Fin 8 → ZMod 2) :
    (rhoMat m).mulVec v = Multiplicative.toAdd (rhoM m (Multiplicative.ofAdd v)) := by
  rw [rhoMat, LinearMap.toMatrix'_mulVec, rhoLin_apply]

theorem rhoMat_mul
    (m n : ↥M) : rhoMat (m * n) = rhoMat m * rhoMat n := by
  apply matrix_ext_mulVec
  intro v
  rw [← Matrix.mulVec_mulVec, rhoMat_mulVec, rhoMat_mulVec, rhoMat_mulVec, rhoM_mul]
  simp

theorem rhoMat_one :
    rhoMat 1 = 1 := by
  apply matrix_ext_mulVec
  intro v
  rw [rhoMat_mulVec, rhoM_one, Matrix.one_mulVec]
  rfl

@[expose] noncomputable def rhoHom :
    ↥M →* Matrix (Fin 8) (Fin 8) (ZMod 2) where
  toFun := rhoMat
  map_one' := rhoMat_one
  map_mul' := rhoMat_mul

theorem rhoHom_apply
    (m : ↥M) : rhoHom m = rhoMat m := rfl

theorem rhoMat_xM :
    rhoMat xM = B1 := by
  apply matrix_ext_mulVec
  intro v
  rw [rhoMat_mulVec]
  have h := rhoM_piQ xM ⟨nf 0 v, nf_mem_Q 0 v⟩
  rw [piQ_nf] at h
  rw [h]
  have e : conjQ xM ⟨nf 0 v, nf_mem_Q 0 v⟩ = ⟨x * nf 0 v * x⁻¹, x_conj_mem_Q (nf_mem_Q 0 v)⟩ :=
    rfl
  rw [e, piQ_conj_x]
  rfl

theorem rhoMat_yM :
    rhoMat yM = B2 := by
  apply matrix_ext_mulVec
  intro v
  rw [rhoMat_mulVec]
  have h := rhoM_piQ yM ⟨nf 0 v, nf_mem_Q 0 v⟩
  rw [piQ_nf] at h
  rw [h]
  have e : conjQ yM ⟨nf 0 v, nf_mem_Q 0 v⟩ = ⟨y * nf 0 v * y⁻¹, y_conj_mem_Q (nf_mem_Q 0 v)⟩ :=
    rfl
  rw [e, piQ_conj_y]
  rfl

theorem rhoMat_eq_one_iff
    (m : ↥M) : rhoMat m = 1 ↔ (m : J) ∈ Q := by
  rw [mem_Q_iff_comm_mem_zpowers m.2]
  constructor
  · intro h g hg
    have h1 : rhoM m (piQ ⟨g, hg⟩) = piQ ⟨g, hg⟩ := by
      have := rhoMat_mulVec m (Multiplicative.toAdd (piQ ⟨g, hg⟩))
      simp only [h, Matrix.one_mulVec] at this
      simpa using this.symm
    simp only [rhoM_piQ] at h1
    have h2 : piQ ((conjQ m ⟨g, hg⟩) * (⟨g, hg⟩ : Q)⁻¹) = 1 := by
      rw [map_mul, map_inv, h1]
      exact mul_inv_cancel _
    rw [piQ_eq_one_iff, center_Q, Subgroup.mem_subgroupOf] at h2
    have e : (((conjQ m ⟨g, hg⟩) * (⟨g, hg⟩ : Q)⁻¹ : Q) : J) = ⁅(m : J), g⁆ := by
      simp only [commutatorElement_def]
      rfl
    exact e ▸ h2
  · intro h
    apply matrix_ext_mulVec
    intro v
    obtain ⟨g, hg⟩ := piQ_surjective (Multiplicative.ofAdd v)
    have hc := h g g.2
    have e : (((conjQ m g) * g⁻¹ : Q) : J) = ⁅(m : J), (g : J)⁆ := by
      simp only [commutatorElement_def]
      rfl
    have hk : (conjQ m g) * g⁻¹ ∈ Subgroup.center Q := by
      rw [center_Q, Subgroup.mem_subgroupOf]
      exact e ▸ hc
    have hk' : piQ (conjQ m g) = piQ g := by
      have h1 := (piQ_eq_one_iff _).2 hk
      rw [map_mul, map_inv] at h1
      exact mul_inv_eq_one.1 h1
    calc (rhoMat m).mulVec v = Multiplicative.toAdd (rhoM m (Multiplicative.ofAdd v)) :=
          rhoMat_mulVec m v
      _ = Multiplicative.toAdd (rhoM m (piQ g)) :=
          congrArg (fun w => Multiplicative.toAdd (rhoM m w)) hg.symm
      _ = Multiplicative.toAdd (piQ (conjQ m g)) :=
          congrArg Multiplicative.toAdd (rhoM_piQ m g)
      _ = Multiplicative.toAdd (piQ g) := congrArg Multiplicative.toAdd hk'
      _ = v := congrArg Multiplicative.toAdd hg
      _ = (1 : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec v := (Matrix.one_mulVec v).symm

theorem rhoMat_posWord
    (w : List ℕ) : rhoMat (posWord xM yM w) = posWord B1 B2 w := by
  rw [← rhoHom_apply, map_posWord, rhoHom_apply, rhoHom_apply, rhoMat_xM, rhoMat_yM]

end CFSG.Sporadic.ThSchreier
