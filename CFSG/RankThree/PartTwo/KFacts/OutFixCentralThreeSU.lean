module

public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThreeSL
public import CFSG.RankThree.PartTwo.KFacts.AutPSU
import CFSG.RankThree.PartTwo.Sec4.Item413AutU3

public section

namespace CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut map_bar_comm)

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def normOneUnits : Subgroup Kˣ where
  carrier := {x | h.norm (x : K) = 1}
  mul_mem' {a b} ha hb := by
    change h.norm ((a * b : Kˣ) : K) = 1
    rw [Units.val_mul, norm_mul_eq h, ha, hb, one_mul]
  one_mem' := by
    change h.norm ((1 : Kˣ) : K) = 1
    rw [Units.val_one, UnitaryFieldData.norm, map_one, one_mul]
  inv_mem' {a} ha := by
    change h.norm ((a⁻¹ : Kˣ) : K) = 1
    rw [Units.val_inv_eq_inv_val, norm_inv_eq h, ha, inv_one]

variable {h}

theorem mem_normOneUnits {x : Kˣ} : x ∈ normOneUnits h ↔ h.norm (x : K) = 1 :=
  Iff.rfl

theorem map_mem_normOneUnits (ρ : K ≃+* K) {x : Kˣ} (hx : x ∈ normOneUnits h) :
    Units.map (ρ : K →* K) x ∈ normOneUnits h := by
  rw [mem_normOneUnits] at hx ⊢
  rw [Units.coe_map, UnitaryFieldData.norm, MonoidHom.coe_ofClass, ← map_bar_comm h ρ, ← map_mul]
  change ρ (h.norm (x : K)) = 1
  rw [hx, map_one]

variable (h) in
@[expose] noncomputable def normOneMap (ρ : K ≃+* K) : normOneUnits h →* normOneUnits h where
  toFun x := ⟨Units.map (ρ : K →* K) x, map_mem_normOneUnits ρ x.2⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' x y := Subtype.ext (map_mul _ (x : Kˣ) y)

theorem det_mem_normOneUnits {A : GL (Fin 3) K} (hA : A ∈ unitaryIsom3 h) :
    GeneralLinearGroup.det A ∈ normOneUnits h := by
  rw [mem_normOneUnits, GeneralLinearGroup.val_det_apply, UnitaryFieldData.norm]
  have hdet := congrArg Matrix.det (mem_unitaryIsom3.mp hA)
  rw [Matrix.det_mul, Matrix.det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    Matrix.det_one] at hdet
  rw [mul_comm]
  exact hdet

theorem psuConj_mem_range_conj_of_det (C : unitaryIsom3 h) {y : Kˣ}
    (hy : y ∈ normOneUnits h) (hC : GeneralLinearGroup.det (C : GL (Fin 3) K) = y ^ 3) :
    psuConj h C ∈ (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  have hyI : ∀ w : Kˣ, w ∈ normOneUnits h →
      GeneralLinearGroup.scalar (Fin 3) w ∈ unitaryIsom3 h := by
    intro w hw
    rw [mem_unitaryIsom3, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [mul_comm]
    exact hw
  obtain ⟨Y, hY⟩ : ∃ Y : unitaryIsom3 h, (Y : GL (Fin 3) K) = GeneralLinearGroup.scalar (Fin 3) y :=
    ⟨⟨_, hyI y hy⟩, rfl⟩
  obtain ⟨C', hC'⟩ : ∃ C' : unitaryIsom3 h, C' = Y⁻¹ * C := ⟨_, rfl⟩
  have hdet : ((C' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [← GeneralLinearGroup.val_det_apply, hC', Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_inv, hY, GeneralLinearGroup.det_scalar, Fintype.card_fin, hC, inv_mul_cancel,
      Units.val_one]
  have hC'SU : (C' : GL (Fin 3) K) ∈ unitarySU p f K 3 :=
    (mem_unitarySU_iff h).mpr ⟨hdet, C'.2⟩
  have hY1 : psuConj h Y = 1 :=
    (CFSG.RankThree.PartTwo.Sec4.psuConj_eq_one_iff Y).mpr ⟨y, hY.symm⟩
  have hCY : C = Y * C' := by rw [hC', mul_inv_cancel_left]
  refine ⟨((⟨C', hC'SU⟩ : unitarySU p f K 3) : unitaryPSU h 3), ?_⟩
  calc MulAut.conj ((⟨C', hC'SU⟩ : unitarySU p f K 3) : unitaryPSU h 3) = psuConj h C' := by
        rw [conj_mk_eq_psuConj]
    _ = psuConj h C := by rw [hCY, map_mul, hY1, one_mul]

theorem psuConj_commutator_mem (A B : unitaryIsom3 h) :
    psuConj h A * psuConj h B * (psuConj h A)⁻¹ * (psuConj h B)⁻¹ ∈
      (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
  refine psuConj_mem_range_conj_of_det _ (one_mem _) ?_
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inv,
    map_mul, map_mul, map_mul, map_inv, map_inv, one_pow, ← commutatorElement_def,
    commutatorElement_eq_one_iff_mul_comm]
  exact mul_comm _ _

theorem psuField_commutator_mem [Finite K] (ρ : K ≃+* K) {c : Kˣ} (hcN : c ∈ normOneUnits h)
    (hc : orderOf c = 3) (hfix : Units.map (ρ : K →* K) c = c) (B : unitaryIsom3 h) :
    psuField h ρ * psuConj h B * (psuField h ρ)⁻¹ * (psuConj h B)⁻¹ ∈
      (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range := by
  rw [psuField_mul_psuConj_mul_inv, ← map_inv, ← map_mul]
  set c' : normOneUnits h := ⟨c, hcN⟩
  have hc' : orderOf c' = 3 := by rw [← Subgroup.orderOf_coe]; exact hc
  have hfix' : normOneMap h ρ c' = c' := Subtype.ext hfix
  set b : normOneUnits h := ⟨GeneralLinearGroup.det (B : GL (Fin 3) K), det_mem_normOneUnits B.2⟩
  obtain ⟨y, hy⟩ := exists_eq_pow_three_of_map_eq (normOneMap h ρ) hc' hfix' b
  refine psuConj_mem_range_conj_of_det _ y.2 ?_
  have hy' := congrArg Subtype.val hy
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] at hy'
  rw [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, mul_comm, ← hy']
  congr 1
  apply Units.ext
  rw [GeneralLinearGroup.val_det_apply, coe_glAut, ← RingEquiv.mapMatrix_apply,
    ← RingEquiv.map_det, ← GeneralLinearGroup.val_det_apply]
  rfl

theorem congr_centerDescend_suConj (hq : 2 < p ^ f) (A : unitaryIsom3 h) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (suConj h A)) = psuConj h A := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem congr_centerDescend_suField (hq : 2 < p ^ f) (ρ : K ≃+* K) :
    MulAut.congr (suCenterEquiv h hq) (centerDescend _ (suField h ρ)) = psuField h ρ := by
  ext x
  induction x using QuotientGroup.induction_on with
  | H g => rfl

theorem exists_suConj_mul_suField (hq : 2 < p ^ f) (σ : MulAut (unitarySU p f K 3)) :
    ∃ (A : unitaryIsom3 h) (ρ : K ≃+* K), σ = suConj h A * suField h ρ := by
  have := isPerfect_unitarySU_three h hq
  obtain ⟨A, ρ, hα⟩ := exists_psuConj_mul_psuField hq
    (MulAut.congr (suCenterEquiv h hq) (centerDescend _ σ))
  refine ⟨A, ρ, ?_⟩
  set σ' := suConj h A * suField h ρ with hσ'
  have heq : MulAut.congr (suCenterEquiv h hq) (centerDescend _ σ) =
      MulAut.congr (suCenterEquiv h hq) (centerDescend _ σ') := by
    rw [hα, hσ', map_mul, map_mul, congr_centerDescend_suConj, congr_centerDescend_suField]
  have h1 : centerDescend _ (σ'⁻¹ * σ) = 1 := by
    rw [map_mul, map_inv, (MulAut.congr (suCenterEquiv h hq)).injective heq, inv_mul_cancel]
  have h2 := eq_one_of_quotientAut_eq_one (N := Subgroup.center (unitarySU p f K 3)) le_rfl
    (fun τ => Subgroup.map_center_eq τ) (ρ := σ'⁻¹ * σ) h1
  exact (inv_mul_eq_one.mp h2).symm

variable (h) in
include h in
theorem fixCommInner_unitarySU (hq : 2 < p ^ f) {z : unitarySU p f K 3}
    (hz : z ∈ Subgroup.center (unitarySU p f K 3)) (hz3 : orderOf z = 3) :
    FixCommInner (unitarySU p f K 3) z := by
  have := h.finite
  rw [center_unitarySU_three (h := h) hq] at hz
  obtain ⟨c, hcN, hc3, hzc⟩ := hz
  have hc : orderOf c = 3 := by
    refine orderOf_eq_prime hc3 fun h1 => ?_
    have hz1 : z = 1 := Subtype.ext (by rw [hzc, h1, map_one, Subgroup.coe_one])
    rw [hz1, orderOf_one] at hz3
    norm_num at hz3
  have hfix : ∀ (A : unitaryIsom3 h) (ρ : K ≃+* K), (suConj h A * suField h ρ) z = z →
      Units.map (ρ : K →* K) c = c := by
    intro A ρ hσ
    have key : ((((suConj h A * suField h ρ) z : unitarySU p f K 3) : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = scalar (Fin 3) (ρ (c : K)) := by
      rw [MulAut.mul_apply, coe_suConj, coe_suField, Units.val_mul, Units.val_mul, coe_glAut, hzc,
        GeneralLinearGroup.coe_scalar, map_scalar_eq]
      exact conj_scalar_eq _ _
    have hm := congrArg (fun g : unitarySU p f K 3 =>
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) hσ
    rw [key, hzc, GeneralLinearGroup.coe_scalar] at hm
    have hm0 := congrFun (congrFun hm 0) 0
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq] at hm0
    exact Units.ext hm0
  intro σ τ hσ hτ
  have : (MulAut.conj : unitaryPSU h 3 →* MulAut (unitaryPSU h 3)).range.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_normal _
  obtain ⟨A, ρ, rfl⟩ := exists_suConj_mul_suField (h := h) hq σ
  obtain ⟨B, ρ', rfl⟩ := exists_suConj_mul_suField (h := h) hq τ
  have hrs : psuField h ρ * psuField h ρ' = psuField h ρ' * psuField h ρ := by
    rw [← map_mul, ← map_mul, ringAut_mul_comm K ρ ρ']
  have hmem := commutator_mem_of_parts hrs (psuConj_commutator_mem A B)
    (psuField_commutator_mem ρ hcN hc (hfix A ρ hσ) B)
    (psuField_commutator_mem ρ' hcN hc (hfix B ρ' hτ) A)
  rw [← congr_centerDescend_suConj hq, ← congr_centerDescend_suConj hq,
    ← congr_centerDescend_suField hq, ← congr_centerDescend_suField hq, ← map_mul, ← map_mul,
    ← map_mul, ← map_mul, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_inv,
    ← map_inv, ← map_mul, ← map_mul, ← map_mul] at hmem
  exact (isInnerAut_congr_centerDescend_iff h hq).mp hmem

end CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree
