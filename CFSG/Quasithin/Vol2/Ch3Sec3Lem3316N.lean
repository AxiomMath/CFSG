module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316F
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4Even
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4

public section

namespace CFSG.Quasithin.H13.L3316.Sp4Aut

open Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.QuasithinUnique.Lin2.Five (tauSp coe_tauSp tauAut tauAut_proj projEquiv tauMat
  tauMat_apply tauPair)

variable {F : Type} [Field F]

theorem spMat_conjSp_fieldSp (A : gsp 2 F) (σ : F ≃+* F) (h : StatedSp 2 F) :
    spMat (conjSp 2 F A (fieldSp 2 F σ h)) =
      ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
        (spMat h).map σ *
        (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) := by
  show (((conjSp 2 F A (fieldSp 2 F σ h) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = _
  rw [coe_conjSp, Units.val_mul, Units.val_mul, coe_fieldSp]

theorem trace_conjSp_fieldSp (A : gsp 2 F) (σ : F ≃+* F) (h : StatedSp 2 F) :
    (spMat (conjSp 2 F A (fieldSp 2 F σ h))).trace = σ (spMat h).trace := by
  rw [spMat_conjSp_fieldSp, Matrix.trace_mul_cycle, ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Matrix.one_mul]
  simp only [Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]

theorem det_one_add_conjSp_fieldSp (A : gsp 2 F) (σ : F ≃+* F) (h : StatedSp 2 F) :
    (1 + spMat (conjSp 2 F A (fieldSp 2 F σ h))).det = σ (1 + spMat h).det := by
  have hab : ((A : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *
      (((A : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [spMat_conjSp_fieldSp]
  have h1 : ∀ a b M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, a * b = 1 →
      1 + a * M * b = a * (1 + M) * b := by
    intro a b M hab
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hab]
  have h2 : 1 + (spMat h).map σ = (1 + spMat h).map σ := by
    rw [Matrix.map_add _ (map_add σ), Matrix.map_one _ (map_zero σ) (map_one σ)]
  rw [h1 _ _ _ hab, Matrix.det_mul, Matrix.det_mul, mul_comm (Matrix.det _) (Matrix.det (1 + _)),
    mul_assoc, ← Matrix.det_mul, hab, Matrix.det_one, mul_one, h2]
  exact (RingHom.map_det σ.toRingHom (1 + spMat h)).symm

omit [Field F] in
theorem two_eq_zero' {F : Type} [Field F] [CharP F 2] : (2 : F) = 0 := CharTwo.two_eq_zero

theorem entries_of_blocks {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hs : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0)
    (hz : ∀ i k : Fin 2, M (Sum.inr i) (Sum.inl k) = 0)
    (hdet : M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 1) (Sum.inl 1) -
      M (Sum.inl 0) (Sum.inl 1) * M (Sum.inl 1) (Sum.inl 0) = 1) :
    M (Sum.inr 0) (Sum.inr 0) = M (Sum.inl 1) (Sum.inl 1) ∧
      M (Sum.inr 1) (Sum.inr 1) = M (Sum.inl 0) (Sum.inl 0) ∧
      M (Sum.inr 0) (Sum.inr 1) = -M (Sum.inl 1) (Sum.inl 0) ∧
      M (Sum.inr 1) (Sum.inr 0) = -M (Sum.inl 0) (Sum.inl 1) := by
  have e00 := congrFun₂ hs (Sum.inl 0) (Sum.inr 0)
  have e01 := congrFun₂ hs (Sum.inl 0) (Sum.inr 1)
  have e10 := congrFun₂ hs (Sum.inl 1) (Sum.inr 0)
  have e11 := congrFun₂ hs (Sum.inl 1) (Sum.inr 1)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, hz] at e00 e01 e10 e11
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination (-M (Sum.inr 0) (Sum.inr 0)) * hdet + M (Sum.inl 1) (Sum.inl 1) * e00 -
      M (Sum.inl 1) (Sum.inl 0) * e10
  · linear_combination (-M (Sum.inr 1) (Sum.inr 1)) * hdet + M (Sum.inl 0) (Sum.inl 0) * e11 -
      M (Sum.inl 0) (Sum.inl 1) * e01
  · linear_combination (-M (Sum.inr 0) (Sum.inr 1)) * hdet + M (Sum.inl 1) (Sum.inl 1) * e01 -
      M (Sum.inl 1) (Sum.inl 0) * e11
  · linear_combination (-M (Sum.inr 1) (Sum.inr 0)) * hdet - M (Sum.inl 0) (Sum.inl 1) * e00 +
      M (Sum.inl 0) (Sum.inl 0) * e10

theorem trace_of_blocks [CharP F 2] {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hs : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0)
    (hz : ∀ i k : Fin 2, M (Sum.inr i) (Sum.inl k) = 0)
    (hdet : M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 1) (Sum.inl 1) -
      M (Sum.inl 0) (Sum.inl 1) * M (Sum.inl 1) (Sum.inl 0) = 1) :
    M.trace = 0 := by
  obtain ⟨h1, h2, -, -⟩ := entries_of_blocks hs hz hdet
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Fin.sum_univ_two]
  rw [h1, h2]
  linear_combination (M (Sum.inl 0) (Sum.inl 0) + M (Sum.inl 1) (Sum.inl 1)) *
    (two_eq_zero' : (2 : F) = 0)

theorem det_one_add_of_blocks [CharP F 2] {M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F}
    (hs : Mᵀ * fromBlocks 0 1 (-1) 0 * M = fromBlocks 0 1 (-1) 0)
    (hz : ∀ i k : Fin 2, M (Sum.inr i) (Sum.inl k) = 0)
    (hdet : M (Sum.inl 0) (Sum.inl 0) * M (Sum.inl 1) (Sum.inl 1) -
      M (Sum.inl 0) (Sum.inl 1) * M (Sum.inl 1) (Sum.inl 0) = 1) :
    (1 + M).det = (M (Sum.inl 0) (Sum.inl 0) + M (Sum.inl 1) (Sum.inl 1)) ^ 2 := by
  obtain ⟨h1, h2, h3, h4⟩ := entries_of_blocks hs hz hdet
  have hM : 1 + M = fromBlocks (1 + M.toBlocks₁₁) M.toBlocks₁₂ 0 (1 + M.toBlocks₂₂) := by
    ext (i | i) (k | k)
    · simp [Matrix.one_apply, Matrix.toBlocks₁₁]
    · simp [Matrix.toBlocks₁₂]
    · simp [hz i k]
    · simp [Matrix.one_apply, Matrix.toBlocks₂₂]
  rw [hM, det_fromBlocks_zero₂₁, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.toBlocks₁₁, Matrix.toBlocks₂₂, Matrix.of_apply]
  simp only [Matrix.one_apply_eq, Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1),
    Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0), zero_add]
  rw [h1, h2, h3, h4]
  linear_combination
    (((1 + M (Sum.inl 0) (Sum.inl 0)) * (1 + M (Sum.inl 1) (Sum.inl 1)) -
      M (Sum.inl 0) (Sum.inl 1) * M (Sum.inl 1) (Sum.inl 0)) + M (Sum.inl 0) (Sum.inl 0) +
      M (Sum.inl 1) (Sum.inl 1)) * hdet +
    (((1 + M (Sum.inl 0) (Sum.inl 0)) * (1 + M (Sum.inl 1) (Sum.inl 1)) -
      M (Sum.inl 0) (Sum.inl 1) * M (Sum.inl 1) (Sum.inl 0)) + M (Sum.inl 0) (Sum.inl 0) +
      M (Sum.inl 1) (Sum.inl 1)) * (two_eq_zero' : (2 : F) = 0)

theorem sigma2_zero : sigma2 0 = ![(Sum.inl 1 : Fin 2 ⊕ Fin 2), Sum.inr 1] := rfl

theorem sigma2_one : sigma2 1 = ![(Sum.inl 0 : Fin 2 ⊕ Fin 2), Sum.inl 1] := rfl

variable [Finite F]

theorem trace_of_mem_zero [CharP F 2] {x : StatedSp 2 F} (hx : x ∈ perfectCore (Q2 F 0)) :
    (spMat x).trace =
      ((blkN 0 ⟨x, hx⟩ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace := by
  have hxQ : x ∈ Q2 F 0 := perfectCore_le _ hx
  have h1 := spMat_inl_zero_eq_one_of_perfectCore hx
  have h2 := spMat_key_of_mem_Q2_zero hxQ (Sum.inr 0)
  rw [h1, one_mul] at h2
  simp only [fromBlocks_apply₁₂, Matrix.one_apply_eq] at h2
  rw [blkN_coe, sigma2_zero]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_sum_type, Fin.sum_univ_two, blkIdx,
    Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h1, h2]
  linear_combination (two_eq_zero' : (2 : F) = 0)

theorem blocks_of_mem_one {x : StatedSp 2 F} (hx : x ∈ perfectCore (Q2 F 1)) :
    (spMat x)ᵀ * fromBlocks 0 1 (-1) 0 * spMat x = fromBlocks 0 1 (-1) 0 ∧
      (∀ i k : Fin 2, spMat x (Sum.inr i) (Sum.inl k) = 0) ∧
      spMat x (Sum.inl 0) (Sum.inl 0) * spMat x (Sum.inl 1) (Sum.inl 1) -
        spMat x (Sum.inl 0) (Sum.inl 1) * spMat x (Sum.inl 1) (Sum.inl 0) = 1 ∧
      ((blkN 1 ⟨x, hx⟩ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
        spMat x (Sum.inl 0) (Sum.inl 0) + spMat x (Sum.inl 1) (Sum.inl 1) := by
  have hxQ : x ∈ Q2 F 1 := perfectCore_le _ hx
  have hdet := (blkN 1 ⟨x, hx⟩).2
  rw [blkN_coe, sigma2_one, Matrix.det_fin_two] at hdet
  simp only [blkIdx, Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hdet
  refine ⟨SymplecticTorusWeyl.mem_statedSp_iff.mp x.2, spMat_inr_inl_of_mem_Q2_one hxQ, hdet, ?_⟩
  rw [blkN_coe, sigma2_one, Matrix.trace_fin_two]
  simp only [blkIdx, Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem trace_of_mem_one [CharP F 2] {x : StatedSp 2 F} (hx : x ∈ perfectCore (Q2 F 1)) :
    (spMat x).trace = 0 := by
  obtain ⟨hs, hz, hdet, -⟩ := blocks_of_mem_one hx
  exact trace_of_blocks hs hz hdet

theorem det_one_add_of_mem_one [CharP F 2] {x : StatedSp 2 F} (hx : x ∈ perfectCore (Q2 F 1)) :
    (1 + spMat x).det =
      ((blkN 1 ⟨x, hx⟩ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace ^ 2 := by
  obtain ⟨hs, hz, hdet, htr⟩ := blocks_of_mem_one hx
  rw [htr]
  exact det_one_add_of_blocks hs hz hdet

omit [Finite F] in
theorem trace_tauSp_spLevi_zero [CharP F 2] (B : SpecialLinearGroup (Fin 2) F) :
    (spMat (tauSp (spLevi 0 B))).trace = 0 := by
  rw [show spMat (tauSp (spLevi 0 B)) = tauMat (spMat (spLevi 0 B)) from coe_tauSp _, spMat_lam]
  simp [Matrix.trace, Fintype.sum_sum_type, tauMat_apply, tauPair, SymplecticTorusWeyl.pairMat]
  linear_combination ((B : Matrix (Fin 2) (Fin 2) F) 0 0 + (B : Matrix (Fin 2) (Fin 2) F) 1 1) *
    (two_eq_zero' : (2 : F) = 0)

omit [Finite F] in
theorem trace_tauSp_spLevi_one [CharP F 2] (B : SpecialLinearGroup (Fin 2) F) :
    (spMat (tauSp (spLevi 1 B))).trace = ((B : Matrix (Fin 2) (Fin 2) F).trace) ^ 2 := by
  rw [show spMat (tauSp (spLevi 1 B)) = tauMat (spMat (spLevi 1 B)) from coe_tauSp _,
    spMat_leviSp_one, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp [Matrix.trace, Fintype.sum_sum_type, tauMat_apply, tauPair, Fin.sum_univ_two]
  linear_combination
    (-((B : Matrix (Fin 2) (Fin 2) F) 0 1 * (B : Matrix (Fin 2) (Fin 2) F) 1 0)) *
      (two_eq_zero' : (2 : F) = 0)

theorem exists_form [CharP F 2] (φ : MulAut (StatedSp 2 F)) :
    ∃ (A : gsp 2 F) (σ : F ≃+* F), (∀ g, φ g = conjSp 2 F A (fieldSp 2 F σ g)) ∨
      ∀ g, φ g = conjSp 2 F A (fieldSp 2 F σ (tauSp g)) := by
  set α : MulAut (StatedProj (StatedSp 2 F)) := ((projEquiv F).symm.trans φ).trans (projEquiv F)
    with hα
  have hαp : ∀ g, α (proj 2 F g) = proj 2 F (φ g) := by
    intro g
    show projEquiv F (φ ((projEquiv F).symm (projEquiv F g))) = proj 2 F (φ g)
    rw [MulEquiv.symm_apply_apply]
    rfl
  obtain ⟨A, σ, ε, hε, hαe⟩ :=
    CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
  refine ⟨A, σ, ?_⟩
  rcases (by omega : ε = 0 ∨ ε = 1) with rfl | rfl
  · left
    intro g
    apply proj_injective_charTwo
    rw [← hαp, hαe, pow_zero, mul_one, MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  · right
    intro g
    apply proj_injective_charTwo
    rw [← hαp, hαe, pow_one, MulAut.mul_apply, MulAut.mul_apply, tauAut_proj, fieldAut_proj,
      conjAut_proj]

theorem inner_of_levi [CharP F 2] (hF4 : ∃ s : Finset F, s.card = 4)
    (φ : MulAut (StatedSp 2 F)) (j : Fin 2) (hQ : (Q2 F j).map φ.toMonoidHom = Q2 F j)
    (c : SpecialLinearGroup (Fin 2) F)
    (hc : ∀ (x : ↥(perfectCore (Q2 F j))) (hx : φ x ∈ perfectCore (Q2 F j)),
      blkN j ⟨φ x, hx⟩ = c * blkN j x * c⁻¹) :
    ∃ g : StatedSp 2 F, ∀ y, φ y = g * y * g⁻¹ := by
  classical
  have hN : ∀ x ∈ perfectCore (Q2 F j), φ x ∈ perfectCore (Q2 F j) := by
    intro x hx
    have h1 : (perfectCore (Q2 F j)).map φ.toMonoidHom = perfectCore (Q2 F j) := by
      rw [map_perfectCore, hQ]
    rw [← h1]
    exact ⟨x, hx, rfl⟩
  have hlevi : ∀ B : SpecialLinearGroup (Fin 2) F,
      ((blkN j ⟨φ (spLevi j B), hN _ (spLevi_mem_perfectCore hF4 j B)⟩ :
        SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace =
        (B : Matrix (Fin 2) (Fin 2) F).trace := by
    intro B
    rw [hc ⟨spLevi j B, spLevi_mem_perfectCore hF4 j B⟩, blkN_spLevi hF4 j B,
      SL3Aut.trace_conj_sl2]
  let Bt : F → SpecialLinearGroup (Fin 2) F := fun t =>
    ⟨!![t, 1; -1, 0], by simp [Matrix.det_fin_two]⟩
  have hBt : ∀ t, ((Bt t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).trace = t := by
    intro t
    simp [Bt, Matrix.trace_fin_two]
  obtain ⟨A, σ, hform | hform⟩ := exists_form φ
  · have hσ : ∀ t : F, σ t = t := by
      intro t
      rcases fin_two_cases j with rfl | rfl
      · have h1 := trace_of_mem_zero (hN _ (spLevi_mem_perfectCore hF4 0 (Bt t)))
        rw [hlevi, hBt, hform, trace_conjSp_fieldSp,
          trace_of_mem_zero (spLevi_mem_perfectCore hF4 0 (Bt t)), blkN_spLevi hF4, hBt] at h1
        exact h1
      · have h1 := det_one_add_of_mem_one (hN _ (spLevi_mem_perfectCore hF4 1 (Bt t)))
        rw [hlevi, hBt, hform, det_one_add_conjSp_fieldSp,
          det_one_add_of_mem_one (spLevi_mem_perfectCore hF4 1 (Bt t)), blkN_spLevi hF4, hBt,
          map_pow] at h1
        exact CharTwo.sq_injective h1
    have hσ1 : σ = 1 := RingEquiv.ext hσ
    obtain ⟨y, hy⟩ := CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A
    obtain ⟨g₀, rfl⟩ := proj_surjective y
    refine ⟨g₀, fun g => ?_⟩
    rw [hform, hσ1, map_one, MulAut.one_apply]
    apply proj_injective_charTwo
    rw [← conjAut_proj, ← hy, MulAut.conj_apply, map_mul, map_mul, map_inv]
  · exfalso
    rcases fin_two_cases j with rfl | rfl
    · have h1 := trace_of_mem_zero (hN _ (spLevi_mem_perfectCore hF4 0 (Bt 1)))
      rw [hlevi, hBt, hform, trace_conjSp_fieldSp, trace_tauSp_spLevi_zero, map_zero] at h1
      exact one_ne_zero h1.symm
    · have h1 := trace_of_mem_one (hN _ (spLevi_mem_perfectCore hF4 1 (Bt 1)))
      rw [hform, trace_conjSp_fieldSp, trace_tauSp_spLevi_one, hBt, one_pow, map_one] at h1
      exact one_ne_zero h1

end CFSG.Quasithin.H13.L3316.Sp4Aut
