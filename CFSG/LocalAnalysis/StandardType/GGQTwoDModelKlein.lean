module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDModelDefs
public import CFSG.ClassicalInvolution.Phan.PhanDn.KleinWedge

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.PhanDn.QTwo CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.BorelTits CFSG.RankThree.PartOne.K159 CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary Matrix

section Klein

variable {F K : Type} [Field F] [Field K] [Algebra F K] [CharP K 2] {σ : K ≃+* K}
  (E : QuadExt F K σ)

private theorem pmk_alt_row0_zero (σ : K ≃+* K) (x : Fin 3 → K) :
    Klein.alt (Sum.elim x fun t => σ (x t)) 0 0 = 0 := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat]

private theorem pmk_alt_row0_one (σ : K ≃+* K) (x : Fin 3 → K) :
    Klein.alt (Sum.elim x fun t => σ (x t)) 0 1 = x 0 := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat]

private theorem pmk_alt_row0_two (σ : K ≃+* K) (x : Fin 3 → K) :
    Klein.alt (Sum.elim x fun t => σ (x t)) 0 2 = x 1 := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat]

private theorem pmk_alt_row0_three (σ : K ≃+* K) (x : Fin 3 → K) :
    Klein.alt (Sum.elim x fun t => σ (x t)) 0 3 = x 2 := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat]

private theorem pmk_alt_col3_one (σ : K ≃+* K) (x : Fin 3 → K) :
    Klein.alt (Sum.elim x fun t => σ (x t)) 1 3 = σ (x 1) := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat]

private theorem pmk_alt_col3_two (σ : K ≃+* K) (x : Fin 3 → K) :
    Klein.alt (Sum.elim x fun t => σ (x t)) 2 3 = σ (x 0) := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat]

private theorem pmk_alt_col3_three (σ : K ≃+* K) (x : Fin 3 → K) :
    Klein.alt (Sum.elim x fun t => σ (x t)) 3 3 = 0 := by
  simp [Klein.alt, CFSG.LocalAnalysis.antiMat]

private theorem pmk_bm1_row0 (M : Matrix (Fin 3) (Fin 3) K) (b : Fin 4) :
    blockMat 4 1 M 0 b = (1 : Matrix (Fin 4) (Fin 4) K) 0 b :=
  blockMat_apply_of_not_mem_left (F := K) (m := 4) (k := 3) (i := 1) (a := 0) M (by decide) b

private theorem pmk_bm1_succ_zero (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    blockMat 4 1 M i.succ 0 = 0 := by
  rw [blockMat_apply_of_not_mem_right (F := K) (m := 4) (k := 3) (i := 1) (a := i.succ) M
    (by decide), Matrix.one_apply]
  simp [Fin.succ_ne_zero i]

private theorem pmk_bm1_succ_succ (M : Matrix (Fin 3) (Fin 3) K) (i t : Fin 3) :
    blockMat 4 1 M i.succ t.succ = M i t := by
  rw [blockMat_apply, dite_eq_left]
  · exact congrArg₂ M (Fin.ext (by simp [Fin.val_succ])) (Fin.ext (by simp [Fin.val_succ]))
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Fin.val_succ] <;> omega

private theorem pmk_bm1_succ_one (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    blockMat 4 1 M i.succ 1 = M i 0 := pmk_bm1_succ_succ M i 0

private theorem pmk_bm1_succ_two (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    blockMat 4 1 M i.succ 2 = M i 1 := pmk_bm1_succ_succ M i 1

private theorem pmk_bm1_succ_three (M : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    blockMat 4 1 M i.succ 3 = M i 2 := pmk_bm1_succ_succ M i 2

private theorem pmk_bm0_apply_lt (M : Matrix (Fin 3) (Fin 3) K) (a d : Fin 3) :
    blockMat 4 0 M a.castSucc d.castSucc = M a d := by
  rw [blockMat_apply, dite_eq_left]
  · exact congrArg₂ M (Fin.ext (by simp [Fin.val_castSucc])) (Fin.ext (by simp [Fin.val_castSucc]))
  · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> simp only [Fin.val_castSucc] <;> omega

private theorem pmk_bm0_apply_zero (M : Matrix (Fin 3) (Fin 3) K) (a : Fin 3) :
    blockMat 4 0 M a.castSucc 0 = M a 0 := pmk_bm0_apply_lt M a 0

private theorem pmk_bm0_apply_one (M : Matrix (Fin 3) (Fin 3) K) (a : Fin 3) :
    blockMat 4 0 M a.castSucc 1 = M a 1 := pmk_bm0_apply_lt M a 1

private theorem pmk_bm0_apply_two (M : Matrix (Fin 3) (Fin 3) K) (a : Fin 3) :
    blockMat 4 0 M a.castSucc 2 = M a 2 := pmk_bm0_apply_lt M a 2

private theorem pmk_bm0_apply_three (M : Matrix (Fin 3) (Fin 3) K) (a : Fin 3) :
    blockMat 4 0 M a.castSucc 3 = 0 := by
  rw [blockMat_apply_of_not_mem_right (F := K) (m := 4) (k := 3) (i := 0) (a := a.castSucc) M
    (by decide), Matrix.one_apply]
  have hne : (a.castSucc : Fin 4) ≠ 3 := by
    intro hh
    have h2 : a.val = 3 := by simpa [Fin.val_castSucc] using congrArg Fin.val hh
    omega
  simp [hne]

private theorem pmk_entry_one (σ : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K)
    (x : Fin 3 → K) (i : Fin 3) :
    (blockMat 4 1 M * Klein.alt (Sum.elim x fun t => σ (x t)) *
      (blockMat 4 1 M)ᵀ) 0 i.succ = (M *ᵥ x) i := by
  have hrow : ∀ a : Fin 4,
      (blockMat 4 1 M * Klein.alt (Sum.elim x fun t => σ (x t))) 0 a =
        Klein.alt (Sum.elim x fun t => σ (x t)) 0 a := by
    intro a
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    simp [pmk_bm1_row0]
  change ((blockMat 4 1 M * Klein.alt (Sum.elim x fun t => σ (x t))) *
    (blockMat 4 1 M)ᵀ) 0 i.succ = (M *ᵥ x) i
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Finset.sum_congr rfl fun a _ => by rw [hrow a]]
  rw [Fin.sum_univ_four]
  simp only [pmk_alt_row0_zero σ x, pmk_alt_row0_one σ x, pmk_alt_row0_two σ x,
    pmk_alt_row0_three σ x, pmk_bm1_succ_zero, pmk_bm1_succ_one, pmk_bm1_succ_two,
    pmk_bm1_succ_three, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  ring

private theorem pmk_entry_zero_three (σ : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K)
    (x : Fin 3 → K) (a : Fin 3) :
    (blockMat 4 0 M * Klein.alt (Sum.elim x fun t => σ (x t)) * (blockMat 4 0 M)ᵀ)
      a.castSucc 3 = M a 0 * x 2 + M a 1 * σ (x 1) + M a 2 * σ (x 0) := by
  have hrow3 : ∀ b : Fin 4, blockMat 4 0 M 3 b = (1 : Matrix (Fin 4) (Fin 4) K) 3 b :=
    fun b => blockMat_apply_of_not_mem_left (F := K) (m := 4) (k := 3) (i := 0) (a := 3) M
      (by decide) b
  change ((blockMat 4 0 M * Klein.alt (Sum.elim x fun t => σ (x t))) *
    (blockMat 4 0 M)ᵀ) a.castSucc 3 = _
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]
  rw [Fin.sum_univ_four]
  simp [hrow3]
  rw [Matrix.mul_apply, Fin.sum_univ_four]
  simp only [pmk_alt_row0_three σ x, pmk_alt_col3_one σ x, pmk_alt_col3_two σ x,
    pmk_alt_col3_three σ x, pmk_bm0_apply_zero, pmk_bm0_apply_one, pmk_bm0_apply_two,
    pmk_bm0_apply_three]
  ring

private theorem pmk_cong_blockMat_one (σ : K ≃+* K) (M : Matrix (Fin 3) (Fin 3) K)
    (x : Fin 3 → K) (i : Fin 3) :
    Klein.cong (blockMat 4 1 M) (Sum.elim x fun t => σ (x t)) (Sum.inl i) = (M *ᵥ x) i := by
  rw [Klein.cong_apply, Klein.coords]
  fin_cases i
  · simpa using pmk_entry_one σ M x 0
  · simpa using pmk_entry_one σ M x 1
  · simpa using pmk_entry_one σ M x 2

private theorem pmk_swapMat_conj_apply (N : Matrix (Fin 3) (Fin 3) K) (a b : Fin 3) :
    ((swapMat : Matrix (Fin 3) (Fin 3) K) * N * (swapMat : Matrix (Fin 3) (Fin 3) K)) a b =
      N a.rev b.rev := by
  fin_cases a <;> fin_cases b <;>
    simp [swapMat, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_three,
      CharTwo.neg_eq]

@[expose] noncomputable def kleinJ : (Fin 3 → K) →ₗ[F] (Fin 3 ⊕ Fin 3 → K) where
  toFun x := Sum.elim x (fun i => σ (x i))
  map_add' x y := by
    ext (i | i) <;> simp
  map_smul' a x := by
    ext (i | i) <;> simp [Algebra.smul_def, E.fix]

@[expose] noncomputable def kleinP : (Fin 3 ⊕ Fin 3 → K) →ₗ[F] (Fin 3 → K) :=
  LinearMap.funLeft F K Sum.inl

@[expose] noncomputable def kleinPsi (g : Matrix (Fin 4) (Fin 4) K) :
    (Fin 3 → K) →ₗ[F] (Fin 3 → K) :=
  kleinP ∘ₗ (Klein.cong g).restrictScalars F ∘ₗ kleinJ E

theorem kleinPsi_apply (g : Matrix (Fin 4) (Fin 4) K) (x : Fin 3 → K) (i : Fin 3) :
    kleinPsi E g x i = Klein.cong g (Sum.elim x fun t => σ (x t)) (Sum.inl i) :=
  rfl

theorem dFlip_kleinJ (x : Fin 3 → K) : dFlip σ (kleinJ E x) = kleinJ E x := by
  funext s
  rcases s with i | i <;>
    simp [kleinJ, dFlip_apply_inl, dFlip_apply_inr, E.isUnitary.invol]

theorem kleinJ_kleinP_of_flip {w : Fin 3 ⊕ Fin 3 → K} (hw : dFlip σ w = w) :
    kleinJ E (kleinP (F := F) w) = w := by
  ext (i | i)
  · rfl
  · change σ (w (Sum.inl i)) = w (Sum.inr i)
    have h := congrFun hw (Sum.inl i)
    simp only [dFlip_apply_inl] at h
    rw [← h, E.isUnitary.invol]

theorem kleinPsi_one : kleinPsi E (1 : Matrix (Fin 4) (Fin 4) K) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  change kleinP (F := F) (Klein.cong 1 (kleinJ E x)) = x
  rw [Klein.cong_one]
  rfl

theorem kleinPsi_mul {g h : Matrix (Fin 4) (Fin 4) K} (hh : conjTr σ h * h = 1)
    (hd : h.det = 1) : kleinPsi E (g * h) = kleinPsi E g ∘ₗ kleinPsi E h := by
  apply LinearMap.ext
  intro x
  set u := Klein.cong h (kleinJ E x) with hu
  have hfix : dFlip σ u = u := by
    rw [hu, dFlip_cong_of_unitary hh (kleinJ E x), hd, map_one, one_smul, dFlip_kleinJ]
  have hJu : kleinJ E (kleinP (F := F) u) = u := kleinJ_kleinP_of_flip E hfix
  change kleinP (F := F) (Klein.cong (g * h) (kleinJ E x)) =
    kleinP (F := F) (Klein.cong g (kleinJ E (kleinP (F := F) (Klein.cong h (kleinJ E x)))))
  rw [Klein.cong_mul, ← hu, hJu]

end Klein

section KleinSU

variable {F K : Type} [Field F] [Field K] [Finite K] [Algebra F K] [CharP K 2]
  (E : QuadExt F K (unitaryInvolution K 2 1))

@[expose] noncomputable def kleinPsiHom : Su K 2 1 4 →* Module.End F (Fin 3 → K) where
  toFun g := kleinPsi E ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K)
  map_one' := kleinPsi_one E
  map_mul' g h := by
    rw [Subgroup.coe_mul, Units.val_mul, kleinPsi_mul E h.2.2 h.2.1]
    rfl

theorem kleinPsiHom_blockEmb_one (h : Su K 2 1 3) (x : Fin 3 → K) :
    kleinPsiHom E (blockEmb K 2 1 4 3 1 (by norm_num) h) x =
      ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
  set M : Matrix (Fin 3) (Fin 3) K := ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hcoe : (((blockEmb K 2 1 4 3 1 (by norm_num) h : Su K 2 1 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = blockMat 4 1 M := by rw [coe_coe_blockEmb]
  have hpsi : kleinPsiHom E (blockEmb K 2 1 4 3 1 (by norm_num) h) =
      kleinPsi E (blockMat 4 1 M) := by
    rw [show kleinPsiHom E (blockEmb K 2 1 4 3 1 (by norm_num) h) =
        kleinPsi E (((blockEmb K 2 1 4 3 1 (by norm_num) h : Su K 2 1 4) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) from rfl, hcoe]
  rw [hpsi]
  funext i
  rw [kleinPsi_apply]
  exact pmk_cong_blockMat_one (unitaryInvolution K 2 1) M x i

theorem kleinPsiHom_blockEmb_one_eq (h : Su K 2 1 3) :
    kleinPsiHom E (blockEmb K 2 1 4 3 1 (by norm_num) h) =
      (suEndN (F := F) (unitaryInvolution K 2 1) 3 h).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [kleinPsiHom_blockEmb_one]
  change ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
    (suEndN (F := F) (unitaryInvolution K 2 1) 3 h).toLinearMap x
  rw [show (suEndN (F := F) (unitaryInvolution K 2 1) 3 h).toLinearMap x =
      suEndN (F := F) (unitaryInvolution K 2 1) 3 h x from rfl, suEndN_apply]
  rfl

theorem revSU3_coe_apply (h : Su K 2 1 3) (a b : Fin 3) :
    (((revSU3 K 2 1 h : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b =
      unitaryInvolution K 2 1 (((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a.rev b.rev) := by
  set M : Matrix (Fin 3) (Fin 3) K := ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hcoe : (((revSU3 K 2 1 h : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      swapMat * M.map (unitaryInvolution K 2 1) * swapMat := by
    rw [revSU3, MulEquiv.trans_apply, MulAut.conj_apply, swapElt_inv]
    rfl
  rw [hcoe, pmk_swapMat_conj_apply]
  rfl

theorem kleinPsiHom_blockEmb_zero (h : Su K 2 1 3) (x : Fin 3 → K) :
    kleinPsiHom E (blockEmb K 2 1 4 3 0 (by norm_num) h) x =
      tauAt E (2 : Fin 3)
        (((revSU3 K 2 1 h : Su K 2 1 3) : GL (Fin 3) K) *ᵥ tauAt E (2 : Fin 3) x) := by
  set M : Matrix (Fin 3) (Fin 3) K := ((h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  set G : Matrix (Fin 4) (Fin 4) K := blockMat 4 0 M
  set w : Fin 3 ⊕ Fin 3 → K := Sum.elim x fun t => unitaryInvolution K 2 1 (x t)
  set N : Matrix (Fin 3) (Fin 3) K :=
    (((revSU3 K 2 1 h : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
  have hcoe : (((blockEmb K 2 1 4 3 0 (by norm_num) h : Su K 2 1 4) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) = G := by rw [coe_coe_blockEmb]
  have hpsi : kleinPsiHom E (blockEmb K 2 1 4 3 0 (by norm_num) h) = kleinPsi E G := by
    rw [show kleinPsiHom E (blockEmb K 2 1 4 3 0 (by norm_num) h) =
        kleinPsi E (((blockEmb K 2 1 4 3 0 (by norm_num) h : Su K 2 1 4) : GL (Fin 4) K) :
          Matrix (Fin 4) (Fin 4) K) from rfl, hcoe]
  have hunit : conjTr (unitaryInvolution K 2 1) G * G = 1 := by
    have hmem := (blockEmb K 2 1 4 3 0 (by norm_num) h).2.2
    rw [hcoe] at hmem
    exact hmem
  have hdet : G.det = 1 := by
    change (blockMat 4 0 M).det = 1
    rw [det_blockMat (by norm_num), h.2.1]
  have hw : dFlip (unitaryInvolution K 2 1) w = w := by
    funext s
    rcases s with i | i
    · simp only [w, dFlip_apply_inl, Sum.elim_inr, Sum.elim_inl]
      rw [E.isUnitary.invol]
    · simp only [w, dFlip_apply_inr, Sum.elim_inl, Sum.elim_inr]
  have hfix : dFlip (unitaryInvolution K 2 1) (Klein.cong G w) = Klein.cong G w := by
    rw [dFlip_cong_of_unitary hunit w, hdet, map_one, one_smul, hw]
  have hN : ∀ a b : Fin 3, N a b = unitaryInvolution K 2 1 (M a.rev b.rev) := by
    intro a b
    change (((revSU3 K 2 1 h : Su K 2 1 3) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) a b =
      unitaryInvolution K 2 1 (M a.rev b.rev)
    rw [revSU3_coe_apply]
  have hY03 : (G * Klein.alt w * Gᵀ) 0 3 =
      M 0 0 * x 2 + M 0 1 * unitaryInvolution K 2 1 (x 1) +
        M 0 2 * unitaryInvolution K 2 1 (x 0) :=
    pmk_entry_zero_three (unitaryInvolution K 2 1) M x 0
  have hY13 : (G * Klein.alt w * Gᵀ) 1 3 =
      M 1 0 * x 2 + M 1 1 * unitaryInvolution K 2 1 (x 1) +
        M 1 2 * unitaryInvolution K 2 1 (x 0) :=
    pmk_entry_zero_three (unitaryInvolution K 2 1) M x 1
  have hY23 : (G * Klein.alt w * Gᵀ) 2 3 =
      M 2 0 * x 2 + M 2 1 * unitaryInvolution K 2 1 (x 1) +
        M 2 2 * unitaryInvolution K 2 1 (x 0) :=
    pmk_entry_zero_three (unitaryInvolution K 2 1) M x 2
  have hu0 : Klein.cong G w (Sum.inl 0) =
      unitaryInvolution K 2 1 ((G * Klein.alt w * Gᵀ) 2 3) := by
    have hh := congrFun hfix (Sum.inl 0)
    rw [dFlip_apply_inl] at hh
    rw [← hh,
      show Klein.cong G w (Sum.inr 0) = (G * Klein.alt w * Gᵀ) 2 3 by
        rw [Klein.cong_apply, Klein.coords]; simp]
  have hu1 : Klein.cong G w (Sum.inl 1) =
      unitaryInvolution K 2 1 ((G * Klein.alt w * Gᵀ) 1 3) := by
    have hh := congrFun hfix (Sum.inl 1)
    rw [dFlip_apply_inl] at hh
    rw [← hh,
      show Klein.cong G w (Sum.inr 1) = (G * Klein.alt w * Gᵀ) 1 3 by
        rw [Klein.cong_apply, Klein.coords]; simp]
  have hu2 : Klein.cong G w (Sum.inl 2) = (G * Klein.alt w * Gᵀ) 0 3 := by
    rw [Klein.cong_apply, Klein.coords]; simp
  have hL : kleinPsiHom E (blockEmb K 2 1 4 3 0 (by norm_num) h) x =
      ![unitaryInvolution K 2 1 ((G * Klein.alt w * Gᵀ) 2 3),
        unitaryInvolution K 2 1 ((G * Klein.alt w * Gᵀ) 1 3),
        (G * Klein.alt w * Gᵀ) 0 3] := by
    funext i
    fin_cases i
    · rw [hpsi, kleinPsi_apply]
      change Klein.cong G w (Sum.inl 0) = _
      rw [hu0]
      rfl
    · rw [hpsi, kleinPsi_apply]
      change Klein.cong G w (Sum.inl 1) = _
      rw [hu1]
      rfl
    · rw [hpsi, kleinPsi_apply]
      change Klein.cong G w (Sum.inl 2) = _
      rw [hu2]
      rfl
  have hR : tauAt E (2 : Fin 3) (N *ᵥ tauAt E (2 : Fin 3) x) =
      ![unitaryInvolution K 2 1 (M 2 0 * x 2 + M 2 1 * unitaryInvolution K 2 1 (x 1) +
            M 2 2 * unitaryInvolution K 2 1 (x 0)),
        unitaryInvolution K 2 1 (M 1 0 * x 2 + M 1 1 * unitaryInvolution K 2 1 (x 1) +
            M 1 2 * unitaryInvolution K 2 1 (x 0)),
        M 0 0 * x 2 + M 0 1 * unitaryInvolution K 2 1 (x 1) +
            M 0 2 * unitaryInvolution K 2 1 (x 0)] := by
    have hr0 : (0 : Fin 3).rev = 2 := by decide
    have hr1 : (1 : Fin 3).rev = 1 := by decide
    have hr2 : (2 : Fin 3).rev = 0 := by decide
    have hinvol : ∀ c : K, frobenius K 2 (frobenius K 2 c) = c := fun c => E.isUnitary.invol c
    funext i
    fin_cases i <;>
      simp [tauAt_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hN, hr0, hr1, hr2,
        hinvol, map_add, map_mul] <;>
      ring
  rw [hL, hR, hY03, hY13, hY23]

theorem kleinPsiHom_blockEmb_zero_eq (h : Su K 2 1 3) :
    kleinPsiHom E (blockEmb K 2 1 4 3 0 (by norm_num) h) =
      (tauAt E (2 : Fin 3)).toLinearMap *
        (suEndN (F := F) (unitaryInvolution K 2 1) 3 (revSU3 K 2 1 h)).toLinearMap *
        (tauAt E (2 : Fin 3)).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [kleinPsiHom_blockEmb_zero, Module.End.mul_apply, Module.End.mul_apply]
  change tauAt E (2 : Fin 3)
      (((revSU3 K 2 1 h : Su K 2 1 3) : GL (Fin 3) K) *ᵥ tauAt E (2 : Fin 3) x) =
    tauAt E (2 : Fin 3)
      (suEndN (F := F) (unitaryInvolution K 2 1) 3 (revSU3 K 2 1 h) (tauAt E (2 : Fin 3) x))
  rw [suEndN_apply, CFSG.ClassicalGroups.Unitary.smul_def]

end KleinSU

end CFSG.StandardType.QTwo

end
