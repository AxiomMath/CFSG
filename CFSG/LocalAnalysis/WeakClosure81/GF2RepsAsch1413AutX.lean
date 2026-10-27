module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TypeOne
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk413AutSp
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4TwoComp

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch1413

open CFSG.ComponentClassification.CatFactsSp4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial SymplecticHigher SymplecticFlag Subgroup
open CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Final CFSG.GH74.GLS.Stage2.Final.ModelBlock
  CFSG.GH74.GLS.Stage2.Final.ModelSp CFSG.GH74.L5U5 CFSG.GH74.Ivk413
  CFSG.RankThree.PartTwo.KFacts Matrix
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {K : Type} [Field K]

private theorem a1413AutX_exists_toGL_of_mem_H2 {a : GL (Fin 2) K}
    (ha : a ∈ (ModelData.sp K).H2) :
    ∃ A : Matrix.SpecialLinearGroup (Fin 2) K, Matrix.SpecialLinearGroup.toGL A = a :=
  ⟨⟨(a : Matrix (Fin 2) (Fin 2) K), ((ModelData.sp K).mem_H2 a).1 ha |>.2⟩, Units.ext rfl⟩

private theorem a1413AutX_reindex_sigma_blk (g h : Matrix (Fin 2) (Fin 2) K) :
    Matrix.reindex sigma sigma (blk g h) = blk4 g h := by
  rw [blk4_eq_reindex, Matrix.coe_reindexAlgEquiv]
  have e0 : e4.symm (0 : Fin 4) = Sum.inl (0 : Fin 2) := by decide
  have e1 : e4.symm (1 : Fin 4) = Sum.inl (1 : Fin 2) := by decide
  have e2 : e4.symm (2 : Fin 4) = Sum.inr (0 : Fin 2) := by decide
  have e3 : e4.symm (3 : Fin 4) = Sum.inr (1 : Fin 2) := by decide
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk, diag2, Matrix.reindex_apply, Matrix.submatrix_apply, sigma, e4, e0, e1, e2, e3]

private theorem a1413AutX_glSigma_blkSL (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    glSigma K ((blkSL K (g, h) : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) =
      diagGL (Matrix.SpecialLinearGroup.toGL g) (Matrix.SpecialLinearGroup.toGL h) := by
  apply Units.ext
  rw [coe_glSigma, coe_blkSL, coe_diagGL]
  exact a1413AutX_reindex_sigma_blk (g : Matrix (Fin 2) (Fin 2) K)
    (h : Matrix (Fin 2) (Fin 2) K)

private theorem a1413AutX_spMulEquiv_blkSL (g h : Matrix.SpecialLinearGroup (Fin 2) K) :
    ((spMulEquiv (blkSL K (g, h)) : ↥(ModelData.sp K).K4) : GL (Fin 4) K) =
      diagGL (Matrix.SpecialLinearGroup.toGL g) (Matrix.SpecialLinearGroup.toGL h) := by
  rw [coe_spMulEquiv]
  exact a1413AutX_glSigma_blkSL g h

private theorem a1413AutX_K1_le_image_E1 :
    K1 (ModelData.sp K) ≤ (spEquiv K) '' E1 K := by
  rintro y ⟨a, rfl⟩
  obtain ⟨A, hA⟩ := a1413AutX_exists_toGL_of_mem_H2 a.2
  refine ⟨proj 2 K (blkSL K (A, 1)), mem_E1.mpr ⟨A, rfl⟩, ?_⟩
  have hK4 : spMulEquiv (blkSL K (A, 1)) =
      (⟨blkL K (a : GL (Fin 2) K), (ModelData.sp K).blkL_mem_K4 a.2⟩ :
        ↥(ModelData.sp K).K4) := by
    apply Subtype.ext
    show (spMulEquiv (blkSL K (A, 1)) : GL (Fin 4) K) = blkL K (a : GL (Fin 2) K)
    rw [a1413AutX_spMulEquiv_blkSL, blkL_apply, ← hA]
    simp
  change spEquiv K (QuotientGroup.mk (blkSL K (A, 1))) = iota1 (ModelData.sp K) a
  rw [spEquiv_mk, iota1_apply, hK4]
  rfl

private theorem a1413AutX_K2_le_image_E2 :
    K2 (ModelData.sp K) ≤ (spEquiv K) '' E2 K := by
  rintro y ⟨a, rfl⟩
  obtain ⟨A, hA⟩ := a1413AutX_exists_toGL_of_mem_H2 a.2
  refine ⟨proj 2 K (blkSL K (1, A)), mem_E2.mpr ⟨A, rfl⟩, ?_⟩
  have hK4 : spMulEquiv (blkSL K (1, A)) =
      (⟨blkR K (a : GL (Fin 2) K), (ModelData.sp K).blkR_mem_K4 a.2⟩ :
        ↥(ModelData.sp K).K4) := by
    apply Subtype.ext
    show (spMulEquiv (blkSL K (1, A)) : GL (Fin 4) K) = blkR K (a : GL (Fin 2) K)
    rw [a1413AutX_spMulEquiv_blkSL, blkR_apply, ← hA]
    simp
  change spEquiv K (QuotientGroup.mk (blkSL K (1, A))) = iota2 (ModelData.sp K) a
  rw [spEquiv_mk, iota2_apply, hK4]
  rfl

private theorem a1413AutX_E2Equiv_negOneSL (h2 : (2 : K) ≠ 0) :
    E2Equiv h2 negOneSL = ⟨u1 K, u1_mem_E2⟩ := by
  apply Subtype.ext
  change proj 2 K (blkSL K (1, negOneSL)) = u1 K
  exact u1_eq_proj_blkSL.symm

private theorem a1413AutX_autInner [Finite K] (h2 : (2 : K) ≠ 0)
    (hG : GoodModel (ModelData.sp K)) (β : MulAut (PG (ModelData.sp K)))
    (hfix : ∀ g ∈ K1 (ModelData.sp K), β g = g) :
    ∃ k ∈ K2 (ModelData.sp K), β = MulAut.conj k := by
  obtain ⟨A, σ, hrep⟩ := semiRep_sp_aux h2 β
  set B : GL (Fin 4) K := glSigma K (A : GL (Fin 2 ⊕ Fin 2) K) with hB
  have hcomm : ∀ a : ↥(ModelData.sp K).H2,
      B * glAut σ (blkL K (a : GL (Fin 2) K)) * B⁻¹ = blkL K a :=
    semiconj_fixes_blkL hG B σ β hrep hfix
  have hσ1 : ∀ t, σ t = t :=
    phi_fix_sp σ fun a ha => phi_fixes_trace B σ a (hcomm ⟨a, ha⟩)
  have hσ : σ = 1 := RingEquiv.ext hσ1
  have hgl : ∀ g : GL (Fin 4) K, glAut σ g = g := by
    intro g
    rw [hσ, map_one]
    rfl
  have hBc : ∀ a : GL (Fin 2) K, (a : Matrix (Fin 2) (Fin 2) K).det = 1 →
      B * blkL K a = blkL K a * B := by
    intro a ha
    have hH : a ∈ (ModelData.sp K).H2 := by
      rw [(ModelData.sp K).mem_H2]
      exact ⟨mem_U2_sp.2 ha, ha⟩
    have := hcomm ⟨a, hH⟩
    rw [hgl] at this
    exact (mul_inv_eq_iff_eq_mul.1 this)
  obtain ⟨c, b, hBb⟩ := eq_diagGL_scalar_of_comm h2 hBc
  obtain ⟨μ, hμ⟩ := glSigma_sim A
  have hdetb : (b : Matrix (Fin 2) (Fin 2) K).det = (c : K) ^ 2 :=
    det_of_sim (c := c) (b := b) (μ := μ) (by rw [← hBb]; exact hμ)
  let b' : GL (Fin 2) K := sc2 c⁻¹ * b
  have hb' : (b' : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    show ((sc2 c⁻¹ * b : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det = 1
    rw [Units.val_mul, Matrix.det_mul, CFSG.GH74.Ivk413.det_sc2, hdetb, Units.val_inv_eq_inv_val]
    have : (c : K) ≠ 0 := c.ne_zero
    field_simp
  let B' : GL (Fin 4) K := diagGL 1 b'
  have hB'K : B' ∈ (ModelData.sp K).K4 := by
    refine ((ModelData.sp K).diagGL_mem_K4_iff).2 ⟨?_, mem_U2_sp.2 hb', ?_⟩
    · exact mem_U2_sp.2 (by simp)
    · simp [hb']
  have hBeq : B = Matrix.GeneralLinearGroup.scalar (Fin 4) c * B' := by
    rw [hBb, scalar4_eq]
    show diagGL (sc2 c) b = diagGL (sc2 c) (sc2 c) * diagGL 1 (sc2 c⁻¹ * b)
    rw [diagGL_mul, mul_one, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  refine ⟨mkP (ModelData.sp K) ⟨B', hB'K⟩, ?_, ?_⟩
  · change mkP (ModelData.sp K) ⟨B', hB'K⟩ ∈ (iota2 (ModelData.sp K)).range
    refine ⟨⟨b', ((ModelData.sp K).mem_H2 b').2 ⟨mem_U2_sp.2 hb', hb'⟩⟩, ?_⟩
    rw [iota2_apply]
    congr 1
  · apply MulEquiv.ext
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨hg, h1⟩ := hrep g
    have h1' : β (mkP (ModelData.sp K) g) = mkP (ModelData.sp K) ⟨B * (g : GL (Fin 4) K) * B⁻¹, by
        simpa only [hgl] using hg⟩ := by
      rw [h1]
      congr 1
      apply Subtype.ext
      show B * glAut σ (g : GL (Fin 4) K) * B⁻¹ = B * (g : GL (Fin 4) K) * B⁻¹
      rw [hgl]
    show β (mkP (ModelData.sp K) g) = (MulAut.conj (mkP (ModelData.sp K) ⟨B', hB'K⟩))
      (mkP (ModelData.sp K) g)
    rw [h1', MulAut.conj_apply, ← map_inv (mkP (ModelData.sp K)),
      ← map_mul (mkP (ModelData.sp K)), ← map_mul (mkP (ModelData.sp K))]
    congr 1
    apply Subtype.ext
    show B * (g : GL (Fin 4) K) * B⁻¹ = B' * (g : GL (Fin 4) K) * B'⁻¹
    have hcen := Subgroup.mem_center_iff.1 (scalar_mem_center (F := K) c)
    rw [hBeq, _root_.mul_inv_rev]
    calc Matrix.GeneralLinearGroup.scalar (Fin 4) c * B' * (g : GL (Fin 4) K) *
          (B'⁻¹ * (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹)
        = Matrix.GeneralLinearGroup.scalar (Fin 4) c * (B' * (g : GL (Fin 4) K) * B'⁻¹) *
            (Matrix.GeneralLinearGroup.scalar (Fin 4) c)⁻¹ := by group
      _ = B' * (g : GL (Fin 4) K) * B'⁻¹ := by
          rw [← hcen (B' * (g : GL (Fin 4) K) * B'⁻¹)]
          group

theorem psp4_aut_fix_E1 {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (α : MulAut (StatedProj (StatedSp 2 K)))
    (h1 : ∀ x ∈ E1 K, α x = x) : ∃ y ∈ E2 K, α = MulAut.conj y := by
  have h2 : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatFactsSp4.two_ne_zero_of_odd_card hodd
  let β : MulAut (PG (ModelData.sp K)) := MulAut.congr (spEquiv K) α
  have hβ : ∀ g ∈ K1 (ModelData.sp K), β g = g := by
    rintro g ⟨a, rfl⟩
    obtain ⟨x, hx, hxg⟩ := a1413AutX_K1_le_image_E1 ⟨a, rfl⟩
    rw [← hxg]
    change MulAut.congr (spEquiv K) α (spEquiv K x) = spEquiv K x
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, h1 x hx]
  obtain ⟨k, hk, hβk⟩ := a1413AutX_autInner h2 (goodModel_sp h2 h5) β hβ
  obtain ⟨y, hy, hyk⟩ := a1413AutX_K2_le_image_E2 hk
  refine ⟨y, hy, ?_⟩
  apply MulEquiv.ext
  intro z
  rw [MulAut.conj_apply]
  have hβz : β (spEquiv K z) = spEquiv K (α z) := by
    change MulAut.congr (spEquiv K) α (spEquiv K z) = spEquiv K (α z)
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply]
  have h3 : spEquiv K (α z) = k * spEquiv K z * k⁻¹ := by
    rw [← hβz, hβk, MulAut.conj_apply]
  have h4 : α z = (spEquiv K).symm (k * spEquiv K z * k⁻¹) := by
    rw [← h3, MulEquiv.symm_apply_apply]
  rw [← hyk, ← map_mul, ← map_inv, ← map_mul, MulEquiv.symm_apply_apply] at h4
  exact h4

theorem psp4_aut_fix_E1E2 {K : Type} [Field K] [Finite K] (hodd : Odd (Nat.card K))
    (h5 : 5 ≤ Nat.card K) (α : MulAut (StatedProj (StatedSp 2 K)))
    (h1 : ∀ x ∈ E1 K, α x = x) (h2 : ∀ x ∈ E2 K, α x = x) :
    α = 1 ∨ α = MulAut.conj (u1 K) := by
  have h2' : (2 : K) ≠ 0 := CFSG.ComponentClassification.CatFactsSp4.two_ne_zero_of_odd_card hodd
  obtain ⟨y, hy, hα⟩ := psp4_aut_fix_E1 hodd h5 α h1
  have hyc : ∀ z ∈ E2 K, y * z = z * y := by
    intro z hz
    have h := congrArg (fun f : MulAut (StatedProj (StatedSp 2 K)) => f z) hα
    rw [MulAut.conj_apply, h2 z hz] at h
    exact mul_inv_eq_iff_eq_mul.1 h.symm
  have hcenter : (⟨y, hy⟩ : E2 K) ∈ Subgroup.center (E2 K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (hyc z z.2).symm
  set h : Matrix.SpecialLinearGroup (Fin 2) K := (E2Equiv h2').symm ⟨y, hy⟩ with hh
  have hhcenter : h ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply (E2Equiv h2').injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hyc (E2Equiv h2' z) (E2Equiv h2' z).2).symm
  rcases eq_one_or_neg_of_mem_center hhcenter with h1' | h1'
  · left
    have hy1 : y = 1 := by
      have hone : (⟨y, hy⟩ : E2 K) = 1 := by
        rw [← MulEquiv.apply_symm_apply (E2Equiv h2') ⟨y, hy⟩, ← hh,
          show h = 1 from Subtype.ext h1', map_one]
      exact congrArg Subtype.val hone
    rw [hα, hy1, map_one]
  · right
    have hhneg : h = negOneSL := Subtype.ext h1'
    have hyu : y = u1 K := by
      have hone : (⟨y, hy⟩ : E2 K) = ⟨u1 K, u1_mem_E2⟩ := by
        rw [← MulEquiv.apply_symm_apply (E2Equiv h2') ⟨y, hy⟩, ← hh, hhneg]
        exact a1413AutX_E2Equiv_negOneSL h2'
      exact congrArg Subtype.val hone
    rw [hα, hyu]

end CFSG.LocalAnalysis.WeakClosure81.Asch1413

end
