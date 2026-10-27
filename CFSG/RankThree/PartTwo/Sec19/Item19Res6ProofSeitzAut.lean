module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryGen
public import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
public import CFSG.RankThree.PartTwo.KFacts.AutKindsCentral

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

section Descend

theorem eq_of_descend_eq (hq : 2 < p ^ f) {φ ψ : MulAut (unitarySU p f K 3)}
    (h1 : MulAut.congr (suCenterEquiv h hq) (centerDescend _ φ) =
      MulAut.congr (suCenterEquiv h hq) (centerDescend _ ψ)) : φ = ψ := by
  have : Group.IsPerfect (unitarySU p f K 3) := isPerfect_unitarySU_three h hq
  have h2 : centerDescend _ φ = centerDescend _ ψ := (MulAut.congr _).injective h1
  apply Sec4.mulAut_eq_of_inv_mul_mem_center
  intro g
  have h3 := congrArg (fun τ : MulAut (unitarySU p f K 3 ⧸ Subgroup.center _) =>
    τ (g : unitarySU p f K 3 ⧸ Subgroup.center _)) h2
  simp only [centerDescend_mk] at h3
  exact QuotientGroup.eq.mp h3.symm

theorem eq_conj_suField_of_not_mem (hq : 2 < p ^ f) {φ : MulAut (unitarySU p f K 3)}
    (hφ3 : φ ^ 3 = 1) (hφ : φ ∉ (suConj h).range) :
    ∃ σ : K ≃+* K, orderOf σ = 3 ∧ ∃ H : unitaryIsom3 h,
      φ = suConj h H * suField h σ * (suConj h H)⁻¹ := by
  set φ' := MulAut.congr (suCenterEquiv h hq) (centerDescend _ φ) with hφ'
  have hφ'3 : φ' ^ 3 = 1 := by rw [hφ', ← map_pow, ← map_pow, hφ3, map_one, map_one]
  have hD : φ' ∉ (psuConj h).range := by
    rintro ⟨A, hA⟩
    apply hφ
    refine ⟨A, eq_of_descend_eq (h := h) hq ?_⟩
    rw [Sec4.congr_centerDescend_suConj h hq, hA]
  obtain ⟨σ, hσ, H, hH⟩ := unitary_order_three_field_descent hq φ' hφ'3 hD
  refine ⟨σ, hσ, H, eq_of_descend_eq (h := h) hq ?_⟩
  rw [← hφ', hH, map_mul, map_mul, map_inv, map_mul, map_mul, map_inv,
    Sec4.congr_centerDescend_suConj h hq, Sec4.congr_centerDescend_suField h hq]

theorem conj_eq_suConj (s : unitarySU p f K 3) :
    MulAut.conj s = suConj h ⟨s, unitarySU_le_unitaryIsom3 s.2⟩ := by
  ext g
  rfl

theorem conj_suField_fix (H : unitaryIsom3 h) (σ : K ≃+* K) (g : unitarySU p f K 3)
    (hg : ∀ i j, σ (((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
      ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) :
    (suConj h H * suField h σ * (suConj h H)⁻¹) (suConj h H g) = suConj h H g := by
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
  congr 1
  apply Subtype.ext
  rw [coe_suField]
  apply Units.ext
  rw [coe_glAut]
  ext i j
  exact hg i j

end Descend

section Center

theorem apply_eq_of_mem_center (h : UnitaryFieldData p f K) (hq : 2 < p ^ f)
    {e : MulAut (unitarySU p f K 3)}
    (he3 : e ^ 3 = 1) {s : unitarySU p f K 3} (hs : s ∈ Subgroup.center (unitarySU p f K 3)) :
    e s = s := by
  have hes : e s ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff] at hs ⊢
    intro y
    have h1 := hs (e.symm y)
    have h2 := congrArg e h1
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  rw [center_unitarySU_three (h := h) hq] at hs hes
  obtain ⟨c, -, hc3, hsc⟩ := hs
  obtain ⟨c', -, hc'3, hesc⟩ := hes
  have hs3 : s ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hsc, ← map_pow, hc3, map_one, Subgroup.coe_one]
  have he3s : e (e (e s)) = s := by
    have := congrArg (fun τ : MulAut (unitarySU p f K 3) => τ s) he3
    simpa [pow_succ] using this
  by_cases hc1 : c = 1
  · have hs1 : s = 1 := Subtype.ext (by rw [hsc, hc1, map_one, Subgroup.coe_one])
    rw [hs1, map_one]
  have hcK : ((c : Kˣ) : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hc'K : ((c' : Kˣ) : K) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc'3, Units.val_one]
  have hc1K : ((c : Kˣ) : K) ≠ 1 := fun h1 => hc1 (Units.ext h1)
  have hcc : ((c : Kˣ) : K) ^ 2 + (c : K) + 1 = 0 := by
    have h1 : ((c : K) - 1) * ((c : K) ^ 2 + c + 1) = 0 := by linear_combination hcK
    exact (mul_eq_zero.1 h1).resolve_left (sub_ne_zero.2 hc1K)
  have hfac : ((c' : K) - 1) * ((c' : K) - c) * ((c' : K) - (c : K) ^ 2) = 0 := by
    linear_combination hc'K + ((c' : K) - (c' : K) ^ 2) * hcc + ((c' : K) - 1) * hcK
  rcases mul_eq_zero.1 hfac with h12 | h3
  · rcases mul_eq_zero.1 h12 with h1 | h2
    ·
      have hes1 : e s = 1 := Subtype.ext (by
        rw [hesc, Subgroup.coe_one]
        have : c' = 1 := Units.ext (by rw [Units.val_one]; exact sub_eq_zero.1 h1)
        rw [this, map_one])
      have : s = 1 := by
        have := congrArg e.symm hes1
        rwa [MulEquiv.symm_apply_apply, map_one] at this
      rw [this, map_one]
    ·
      apply Subtype.ext
      rw [hesc, hsc]
      congr 1
      exact Units.ext (sub_eq_zero.1 h2)
  ·
    have hes2 : e s = s ^ 2 := by
      apply Subtype.ext
      rw [hesc, Subgroup.coe_pow, hsc, ← map_pow]
      congr 1
      apply Units.ext
      rw [Units.val_pow_eq_pow_val]
      exact sub_eq_zero.1 h3
    have hpow : ∀ n : ℕ, e (s ^ n) = s ^ (2 * n) := fun n => by
      rw [map_pow, hes2, ← pow_mul]
    have h4 : e (e (e s)) = s ^ 2 := by
      rw [hes2, hpow, hpow]
      calc s ^ (2 * (2 * 2)) = (s ^ 3) ^ 2 * s ^ 2 := by group
        _ = s ^ 2 := by rw [hs3, one_pow, one_mul]
    have h5 : s = s ^ 2 := he3s.symm.trans h4
    have hs1 : s = 1 := by
      have : s * s = s * 1 := by rw [mul_one, ← sq, ← h5]
      exact mul_left_cancel this
    rw [hs1, map_one]

end Center

section Scalar

variable {F : Type} [Field F]

@[expose] def swapMat' (F : Type) [Field F] : Matrix (Fin 3) (Fin 3) F :=
  !![-1, 0, 0; 0, 0, 1; 0, 1, 0]

theorem swapMat'_mul_self (F : Type) [Field F] : swapMat' F * swapMat' F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMat', Matrix.mul_apply, Fin.sum_univ_three]

@[expose] def swapGL' (F : Type) [Field F] : GL (Fin 3) F :=
  ⟨swapMat' F, swapMat' F, swapMat'_mul_self F, swapMat'_mul_self F⟩

theorem swapGL_mem_unitarySU {e : ℕ} (h₀ : UnitaryFieldData p e F) :
    swapGL F ∈ unitarySU p e F 3 := by
  refine (mem_unitarySU_iff h₀).mpr ⟨?_, ?_⟩
  · change (swapMat F).det = 1
    simp [swapMat, Matrix.det_fin_three]
  · change ((swapMat F).map h₀.bar)ᵀ * swapMat F = 1
    have hmap : (swapMat F).map h₀.bar = swapMat F := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapMat]
    rw [hmap]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem swapGL'_mem_unitarySU {e : ℕ} (h₀ : UnitaryFieldData p e F) :
    swapGL' F ∈ unitarySU p e F 3 := by
  refine (mem_unitarySU_iff h₀).mpr ⟨?_, ?_⟩
  · change (swapMat' F).det = 1
    simp [swapMat', Matrix.det_fin_three]
  · change ((swapMat' F).map h₀.bar)ᵀ * swapMat' F = 1
    have hmap : (swapMat' F).map h₀.bar = swapMat' F := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [swapMat']
    rw [hmap]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [swapMat', Matrix.mul_apply, Fin.sum_univ_three]

theorem eq_smul_one_of_commute (M : Matrix (Fin 3) (Fin 3) F) {ω : F} (hω : IsPrimitiveRoot ω 3)
    (h1 : M * diagonal ![ω, ω ^ 2, 1] = diagonal ![ω, ω ^ 2, 1] * M)
    (h2 : M * swapMat F = swapMat F * M) (h3 : M * swapMat' F = swapMat' F * M) :
    M = M 0 0 • 1 := by
  have hω3 : ω ^ 3 = 1 := hω.pow_eq_one
  have hω1 : ω ≠ 1 := hω.ne_one (by norm_num)
  have hω2 : ω ^ 2 ≠ 1 := fun h => by
    have := hω.pow_eq_one_iff_dvd 2
    rw [this] at h
    omega
  have hω21 : ω ^ 2 ≠ ω := fun h => by
    apply hω1
    have h0 : ω ≠ 0 := by rintro rfl; norm_num at hω3
    have : ω * ω = ω * 1 := by rw [mul_one, ← sq, h]
    exact mul_left_cancel₀ h0 this
  have hentry : ∀ i j, M i j * (![ω, ω ^ 2, 1] j - ![ω, ω ^ 2, 1] i) = 0 := by
    intro i j
    have := congrFun (congrFun h1 i) j
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    linear_combination this
  have hoff : ∀ i j, i ≠ j → M i j = 0 := by
    intro i j hij
    refine (mul_eq_zero.1 (hentry i j)).resolve_right ?_
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
    · exact sub_ne_zero.2 hω21
    · exact sub_ne_zero.2 (Ne.symm hω1)
    · exact sub_ne_zero.2 (Ne.symm hω21)
    · exact sub_ne_zero.2 (Ne.symm hω2)
    · exact sub_ne_zero.2 hω1
    · exact sub_ne_zero.2 hω2
  have e01 := congrFun (congrFun h2 0) 1
  have e12 := congrFun (congrFun h3 1) 2
  simp [Matrix.mul_apply, Fin.sum_univ_three, swapMat, swapMat'] at e01 e12
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hoff 0 1 (by decide), hoff 0 2 (by decide),
    hoff 1 0 (by decide), hoff 1 2 (by decide), hoff 2 0 (by decide), hoff 2 1 (by decide)]
  · exact e01.symm
  · rw [← e12, e01]

end Scalar

end CFSG.RankThree.PartTwo.Sec19.Item19Res6Proof
