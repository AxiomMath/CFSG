module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4FusL3MxDefs
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3
public import CFSG.LieType.Steinberg.CentralExt.SUTwo

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.GLS.IVK.Proofs2 CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3 CFSG.RankThree.SubgroupLists
open scoped Matrix MatrixGroups

section SL2U

variable {F : Type} [Field F] [Finite F]

private theorem mem_sl2Of_l3U {Bl : Subgroup (GL (Fin 2) F)} {A : GL (Fin 2) F} :
    A ∈ sl2Of Bl ↔ A ∈ Bl ∧ Matrix.GeneralLinearGroup.det A = 1 := by
  rw [sl2Of, Subgroup.mem_inf, MonoidHom.mem_ker]

private theorem det_eq_one_iff_l3U (A : GL (Fin 2) F) :
    Matrix.GeneralLinearGroup.det A = 1 ↔ (A : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  rw [Units.ext_iff, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]

private theorem mem_statedSU_two_l3U {p : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ 1) ^ 2) (A : GL (Fin 2) F) :
    A ∈ StatedSU 2 (p ^ 1) F ↔ (A : Matrix (Fin 2) (Fin 2) F).det = 1 ∧
      ((A : Matrix (Fin 2) (Fin 2) F).map (· ^ p ^ 1))ᵀ * (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have hfun : ((CFSG.LieType.BorelTits.unitaryInvolution F p 1 : F ≃+* F) : F → F) =
      (· ^ p ^ 1) := by
    funext c
    rw [CFSG.LieType.BorelTits.unitaryInvolution_apply]
  rw [← CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 2,
    CFSG.LieType.Universal.Unitary.mem_SUid]
  simp only [CFSG.LieType.Universal.Unitary.conjTr, hfun]

private theorem mem_GU2_l3U {p : ℕ} (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F)
    (A : GL (Fin 2) F) :
    A ∈ GU2Stated (p ^ 1) F ↔
      ((A : Matrix (Fin 2) (Fin 2) F).map (· ^ p ^ 1))ᵀ * (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [Lemma41aU3.mem_GU2Stated_iff h, Lemma41aU3.bar_eq_pow h]

private theorem sl2Of_GU2_eq_l3U {p : ℕ} (hp : p.Prime) (hF : Nat.card F = (p ^ 1) ^ 2) :
    sl2Of (GU2Stated (p ^ 1) F) = StatedSU 2 (p ^ 1) F := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F :=
    ⟨hp, le_rfl, by rw [hF]; ring⟩
  haveI : CharP F p := h.charP
  ext A
  rw [mem_sl2Of_l3U, mem_GU2_l3U h, mem_statedSU_two_l3U hF, det_eq_one_iff_l3U]
  exact and_comm

private theorem nonempty_sl2_statedSU_l3U {p : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ 1) ^ 2) :
    Nonempty (SL(2, CFSG.LieType.Steinberg.fixedSubfield F p 1) ≃* StatedSU 2 (p ^ 1) F) := by
  obtain ⟨ζ, hζ0, hζ⟩ := CFSG.LieType.BorelTits.exists_unitaryInvolution_eq_neg hF
  obtain ⟨P, hP⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF 2
  exact ⟨((CFSG.LieType.Steinberg.hypEquiv hζ0 hζ).trans
    (CFSG.LieType.Universal.Unitary.conjEquiv P hP)).trans
    (MulEquiv.subgroupCongr (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF 2))⟩

private theorem isPerfect_sl2_fixedSubfield_l3U {p : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ 1) ^ 2) (hp5 : 5 ≤ p) :
    Group.IsPerfect (SL(2, CFSG.LieType.Steinberg.fixedSubfield F p 1)) := by
  refine CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card _ ?_
  rw [CFSG.LieType.Steinberg.card_fixedSubfield hF, pow_one]
  omega

private theorem jL3U_mul_l3U :
    (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, -1; 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private theorem jL3U_mul_l3U' :
    (!![0, -1; 1, 0] : Matrix (Fin 2) (Fin 2) F) * !![0, 1; -1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

private def jL3U : GL (Fin 2) F :=
  ⟨!![0, 1; -1, 0], !![0, -1; 1, 0], jL3U_mul_l3U, jL3U_mul_l3U'⟩

private theorem coe_jL3U :
    ((jL3U : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, 1; -1, 0] := rfl

private theorem dL3U_mul_l3U (a : F) (ha : a ≠ 0) :
    Matrix.diagonal ![a, a⁻¹] * Matrix.diagonal ![a⁻¹, a] = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, ha]

private theorem dL3U_mul_l3U' (a : F) (ha : a ≠ 0) :
    Matrix.diagonal ![a⁻¹, a] * Matrix.diagonal ![a, a⁻¹] = 1 := by
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal_apply, ha]

private def dL3U (a : F) (ha : a ≠ 0) : GL (Fin 2) F :=
  ⟨Matrix.diagonal ![a, a⁻¹], Matrix.diagonal ![a⁻¹, a], dL3U_mul_l3U a ha, dL3U_mul_l3U' a ha⟩

private theorem coe_dL3U (a : F) (ha : a ≠ 0) :
    (dL3U a ha : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![a, a⁻¹] := rfl

private theorem jL3U_matrix_l3U {q : ℕ} (hq0 : q ≠ 0) (hodd : Odd q) :
    ((!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F).map (· ^ q))ᵀ *
      (!![0, 1; -1, 0] : Matrix (Fin 2) (Fin 2) F) = 1 := by
  have h0 : (0 : F) ^ q = 0 := zero_pow hq0
  have h2 : (-1 : F) ^ q = -1 := hodd.neg_one_pow
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h0, h2]

private theorem dL3U_matrix_l3U {q : ℕ} (hq0 : q ≠ 0) (a : F) (ha : a ≠ 0)
    (hq : a ^ q * a = 1) :
    ((Matrix.diagonal ![a, a⁻¹] : Matrix (Fin 2) (Fin 2) F).map (· ^ q))ᵀ *
      Matrix.diagonal ![a, a⁻¹] = 1 := by
  have h0 : (0 : F) ^ q = 0 := zero_pow hq0
  have hq' : (a ^ q)⁻¹ * a⁻¹ = 1 := by rw [← mul_inv, hq, inv_one]
  have hq'' : a⁻¹ ^ q * a⁻¹ = 1 := by rw [inv_pow, hq']
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, h0, hq, hq', hq'', ha]

private theorem jL3U_mem_statedSU {p : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ 1) ^ 2) (hp : p.Prime) (hp5 : 5 ≤ p) :
    jL3U ∈ StatedSU 2 (p ^ 1) F := by
  rw [mem_statedSU_two_l3U hF, coe_jL3U]
  refine ⟨?_, jL3U_matrix_l3U (pow_ne_zero 1 hp.ne_zero) (hp.odd_of_ne_two (by omega)).pow⟩
  rw [Matrix.det_fin_two_of]
  norm_num

private theorem dL3U_mem_statedSU {p : ℕ} [Fact p.Prime] [CharP F p]
    (hF : Nat.card F = (p ^ 1) ^ 2) (hp : p.Prime) (a : F) (ha : a ≠ 0)
    (hq : a ^ (p ^ 1) * a = 1) :
    dL3U a ha ∈ StatedSU 2 (p ^ 1) F := by
  rw [mem_statedSU_two_l3U hF, coe_dL3U]
  refine ⟨?_, dL3U_matrix_l3U (pow_ne_zero 1 hp.ne_zero) a ha hq⟩
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  simp [ha]

private theorem blk_scalar_neg_one_l3U :
    blk (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ)) = negDiag3 F := by
  have hd : (Matrix.scalar (Fin 2) (-1 : F)).det = 1 := by
    simp [Matrix.det_fin_two, Matrix.scalar_apply, Matrix.diagonal_apply]
  apply Units.ext
  rw [coe_blk, coe_negDiag3, Matrix.GeneralLinearGroup.coe_scalar, Units.val_neg, Units.val_one,
    hd, inv_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blkMat, Matrix.scalar_apply, Matrix.diagonal_apply]

private theorem l3U_scalar_of_JD {B : GL (Fin 2) F} {a : F} (ha : a ≠ 0) (haa : a * a ≠ 1)
    (hJ : B * jL3U = jL3U * B) (hD : B * dL3U a ha = dL3U a ha * B) :
    ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
  have hdetB := det_ne_zero_gl B
  have hJm := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hJ
  have hDm := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hD
  simp only [Units.val_mul, coe_jL3U, coe_dL3U] at hJm hDm
  have hinv : a⁻¹ - a ≠ 0 := by
    intro h
    apply haa
    have h2 : a⁻¹ = a := sub_eq_zero.mp h
    calc a * a = a * a⁻¹ := by rw [h2]
      _ = 1 := mul_inv_cancel₀ ha
  have hinv' : a - a⁻¹ ≠ 0 := fun h => hinv (by linear_combination -h)
  set M : Matrix (Fin 2) (Fin 2) F := (B : Matrix (Fin 2) (Fin 2) F) with hM
  have hJ00 : M 0 0 = M 1 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using congrFun (congrFun hJm 0) 1
  have hm01 : M 0 1 = 0 := by
    have h : M 0 1 * a⁻¹ = a * M 0 1 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] using
        congrFun (congrFun hDm 0) 1
    have h' : M 0 1 * (a⁻¹ - a) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_right hinv
  have hm10 : M 1 0 = 0 := by
    have h : M 1 0 * a = a⁻¹ * M 1 0 := by
      simpa [Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply] using
        congrFun (congrFun hDm 1) 0
    have h' : M 1 0 * (a - a⁻¹) = 0 := by linear_combination h
    exact (mul_eq_zero.mp h').resolve_right hinv'
  have hm00 : M 0 0 ≠ 0 := by
    intro h0
    apply hdetB
    simp [Matrix.det_fin_two, hm01, hm10, ← hJ00, h0]
  refine ⟨Units.mk0 (M 0 0) hm00, ?_⟩
  apply Units.ext
  rw [← hM, Matrix.GeneralLinearGroup.coe_scalar, Units.val_mk0]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, hm01, hm10, hJ00]

end SL2U

theorem l3ShapeU_sl2 {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hF : Nat.card F = (p ^ 1) ^ 2) :
    ⁅GU2Stated (p ^ 1) F, GU2Stated (p ^ 1) F⁆ = sl2Of (GU2Stated (p ^ 1) F) ∧
    Group.IsPerfect ↥(sl2Of (GU2Stated (p ^ 1) F)) ∧
    (∀ B : ↥(sl2Of (GU2Stated (p ^ 1) F)),
      B ∈ Subgroup.center ↥(sl2Of (GU2Stated (p ^ 1) F)) ↔
        (blk (B : GL (Fin 2) F) = 1 ∨ blk (B : GL (Fin 2) F) = negDiag3 F)) ∧
    (∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ∧
      Nonempty (↥(sl2Of (GU2Stated (p ^ 1) F)) ⧸ Subgroup.center ↥(sl2Of (GU2Stated (p ^ 1) F)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀)) ∧
    (∀ B ∈ GU2Stated (p ^ 1) F, (∀ B' ∈ sl2Of (GU2Stated (p ^ 1) F), B * B' = B' * B) →
      ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 2) c) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData p 1 F :=
    ⟨hp, le_rfl, by rw [hF]; ring⟩
  haveI : CharP F p := h.charP
  have hSU : sl2Of (GU2Stated (p ^ 1) F) = StatedSU 2 (p ^ 1) F := sl2Of_GU2_eq_l3U hp hF
  obtain ⟨e₀⟩ := nonempty_sl2_statedSU_l3U hF
  have e₁ : SL(2, CFSG.LieType.Steinberg.fixedSubfield F p 1) ≃*
      ↥(sl2Of (GU2Stated (p ^ 1) F)) :=
    e₀.trans (MulEquiv.subgroupCongr hSU.symm)
  haveI := isPerfect_sl2_fixedSubfield_l3U hF hp5
  have hperf : Group.IsPerfect ↥(sl2Of (GU2Stated (p ^ 1) F)) :=
    Group.IsPerfect.ofSurjective (f := e₁.toMonoidHom) e₁.surjective
  obtain ⟨l, hl1, hl2⟩ := CFSG.LieType.Steinberg.exists_norm_one_orderOf_eq hF
  rw [CFSG.LieType.BorelTits.unitaryInvolution_apply] at hl1
  have ha : (l : F) ≠ 0 := l.ne_zero
  have haa : (l : F) * (l : F) ≠ 1 := by
    intro hsq
    have h2 : l ^ 2 = 1 :=
      Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one, sq]; exact hsq)
    have hd := orderOf_dvd_of_pow_eq_one h2
    rw [hl2, pow_one] at hd
    have := Nat.le_of_dvd (by norm_num) hd
    omega
  have hJS : jL3U ∈ sl2Of (GU2Stated (p ^ 1) F) := by
    rw [hSU]
    exact jL3U_mem_statedSU hF hp hp5
  have hDS : dL3U (l : F) ha ∈ sl2Of (GU2Stated (p ^ 1) F) := by
    rw [hSU]
    exact dL3U_mem_statedSU hF hp (l : F) ha hl1
  have hderived : ⁅GU2Stated (p ^ 1) F, GU2Stated (p ^ 1) F⁆ = sl2Of (GU2Stated (p ^ 1) F) := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [mem_sl2Of_l3U]
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        exact (GU2Stated (p ^ 1) F).mul_mem ((GU2Stated (p ^ 1) F).mul_mem
          ((GU2Stated (p ^ 1) F).mul_mem hx hy) ((GU2Stated (p ^ 1) F).inv_mem hx))
          ((GU2Stated (p ^ 1) F).inv_mem hy)
      · rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    · have hle : sl2Of (GU2Stated (p ^ 1) F) ≤ GU2Stated (p ^ 1) F :=
        fun x hx => (mem_sl2Of_l3U.mp hx).1
      haveI := hperf
      calc sl2Of (GU2Stated (p ^ 1) F)
          = ⁅sl2Of (GU2Stated (p ^ 1) F), sl2Of (GU2Stated (p ^ 1) F)⁆ :=
            Subgroup.commutator_eq_self.symm
        _ ≤ ⁅GU2Stated (p ^ 1) F, GU2Stated (p ^ 1) F⁆ := Subgroup.commutator_mono hle hle
  have hcenter : ∀ B : ↥(sl2Of (GU2Stated (p ^ 1) F)),
      B ∈ Subgroup.center ↥(sl2Of (GU2Stated (p ^ 1) F)) ↔
        (blk (B : GL (Fin 2) F) = 1 ∨ blk (B : GL (Fin 2) F) = negDiag3 F) := by
    intro B
    constructor
    · intro hB
      have hJc : (B : GL (Fin 2) F) * jL3U = jL3U * (B : GL (Fin 2) F) :=
        (congrArg (fun x : ↥(sl2Of (GU2Stated (p ^ 1) F)) => (x : GL (Fin 2) F))
          (Subgroup.mem_center_iff.mp hB ⟨jL3U, hJS⟩)).symm
      have hDc : (B : GL (Fin 2) F) * dL3U (l : F) ha = dL3U (l : F) ha * (B : GL (Fin 2) F) :=
        (congrArg (fun x : ↥(sl2Of (GU2Stated (p ^ 1) F)) => (x : GL (Fin 2) F))
          (Subgroup.mem_center_iff.mp hB ⟨dL3U (l : F) ha, hDS⟩)).symm
      obtain ⟨c, hc⟩ := l3U_scalar_of_JD ha haa hJc hDc
      have hdet : ((B : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 :=
        (det_eq_one_iff_l3U _).mp (mem_sl2Of_l3U.mp B.2).2
      have hcc : (c : F) * (c : F) = 1 := by
        have h2 := hdet
        rw [hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Matrix.det_diagonal,
          Fin.prod_univ_two] at h2
        exact h2
      rcases mul_self_eq_one_iff.mp hcc with h1 | h1
      · left
        have hc1 : c = 1 := Units.ext (by rw [h1, Units.val_one])
        rw [hc, hc1, map_one, map_one]
      · right
        have hc1 : c = -1 := Units.ext (by rw [h1, Units.val_neg, Units.val_one])
        rw [hc, hc1, blk_scalar_neg_one_l3U]
    · intro hB
      rcases hB with hB | hB
      · have h1 : (B : GL (Fin 2) F) = 1 := blk_injective (by rw [hB, map_one])
        have hB1 : B = 1 := Subtype.ext h1
        rw [hB1]
        exact Subgroup.one_mem _
      · have h1 : (B : GL (Fin 2) F) = Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) :=
          blk_injective (by rw [hB, blk_scalar_neg_one_l3U])
        have hz : (Matrix.GeneralLinearGroup.scalar (Fin 2) (-1 : Fˣ) : GL (Fin 2) F) ∈
            Subgroup.center (GL (Fin 2) F) := by
          rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact ⟨-1, rfl⟩
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        show (g : GL (Fin 2) F) * (B : GL (Fin 2) F) = (B : GL (Fin 2) F) * g
        rw [h1]
        exact Subgroup.mem_center_iff.mp hz (g : GL (Fin 2) F)
  have hpsl : ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Nat.card F₀ = p ∧
      Nonempty (↥(sl2Of (GU2Stated (p ^ 1) F)) ⧸ Subgroup.center ↥(sl2Of (GU2Stated (p ^ 1) F)) ≃*
        Matrix.ProjectiveSpecialLinearGroup (Fin 2) F₀) := by
    refine ⟨↥(CFSG.LieType.Steinberg.fixedSubfield F p 1), inferInstance, inferInstance, ?_, ?_⟩
    · rw [CFSG.LieType.Steinberg.card_fixedSubfield hF, pow_one]
    · exact ⟨(QuotientGroup.congr
        (Subgroup.center SL(2, ↥(CFSG.LieType.Steinberg.fixedSubfield F p 1)))
        (Subgroup.center ↥(sl2Of (GU2Stated (p ^ 1) F))) e₁
        (Subgroup.map_center_eq e₁)).symm⟩
  have hscalar : ∀ B ∈ GU2Stated (p ^ 1) F,
      (∀ B' ∈ sl2Of (GU2Stated (p ^ 1) F), B * B' = B' * B) →
        ∃ c : Fˣ, B = Matrix.GeneralLinearGroup.scalar (Fin 2) c := by
    intro B _ hcomm
    exact l3U_scalar_of_JD ha haa (hcomm _ hJS) (hcomm _ hDS)
  exact ⟨hderived, hperf, hcenter, hpsl, hscalar⟩

end CFSG.Quasithin.H13
