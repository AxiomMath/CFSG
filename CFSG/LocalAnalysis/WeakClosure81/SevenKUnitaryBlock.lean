module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKUnitary
public import CFSG.LocalAnalysis.WeakClosure81.SU3RankDefs
import CFSG.RankThree.GF2n.Smith81.S81CTransvSU
import CFSG.RankThree.GF2n.Smith81.Sec220DihLin
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix CFSG.Open CFSG.LocalAnalysis.WeakClosure81.SevenK

private lemma wcru_blockMat_sub_one {F : Type*} [Field F] {m k i : ℕ}
    (A : Matrix (Fin k) (Fin k) F) :
    CFSG.ClassicalInvolution.Phan.blockMat m i A - 1 =
      CFSG.ClassicalInvolution.Phan.blockSel F m k i * (A - 1) *
        (CFSG.ClassicalInvolution.Phan.blockSel F m k i)ᵀ := by
  unfold CFSG.ClassicalInvolution.Phan.blockMat
  abel

private lemma wcru_blockSel_mul {F : Type*} [Field F] {m l k : ℕ} (hkl : k ≤ l) :
    CFSG.ClassicalInvolution.Phan.blockSel F m l 0 *
      CFSG.ClassicalInvolution.Phan.blockSel F l k 0 =
        CFSG.ClassicalInvolution.Phan.blockSel F m k 0 := by
  ext a j
  rw [Matrix.mul_apply]
  simp only [CFSG.ClassicalInvolution.Phan.blockSel_apply]
  have hj : j.val < l := lt_of_lt_of_le j.isLt hkl
  rw [Finset.sum_eq_single (⟨j.val, hj⟩ : Fin l)]
  · simp [CFSG.ClassicalInvolution.Phan.blockSel_apply]
  · intro b _ hb
    have hbj : b.val ≠ j.val := fun h => hb (Fin.ext h)
    simp [CFSG.ClassicalInvolution.Phan.blockSel_apply, hbj]
  · simp

private lemma wcru_rank_vecMulVec_eq_one {F : Type*} [Field F] {m : ℕ} {u w : Fin m → F}
    (hu : u ≠ 0) (hw : w ≠ 0) : (Matrix.vecMulVec u w).rank = 1 := by
  apply le_antisymm (Matrix.rank_vecMulVec_le u w)
  obtain ⟨j, hj⟩ := Function.ne_iff.1 hw
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  rw [Matrix.rank_eq_finrank_span_cols, Submodule.finrank_eq_zero] at h0
  have hcol : (Matrix.vecMulVec u w).col j ∈
      Submodule.span F (Set.range (Matrix.vecMulVec u w).col) :=
    Submodule.subset_span ⟨j, rfl⟩
  rw [h0, Submodule.mem_bot] at hcol
  apply hu
  have h1 : w j • u = 0 := by
    rw [← hcol]
    ext i
    simp [Matrix.vecMulVec_apply, mul_comm]
  exact (smul_eq_zero.1 h1).resolve_left hj

theorem rank_blockMat_sub_one {F : Type*} [Field F] {m k i : ℕ} (h : i + k ≤ m)
    (A : Matrix (Fin k) (Fin k) F) :
    (CFSG.ClassicalInvolution.Phan.blockMat m i A - 1).rank = (A - 1).rank := by
  rw [wcru_blockMat_sub_one A]
  set L : Matrix (Fin m) (Fin k) F := CFSG.ClassicalInvolution.Phan.blockSel F m k i with hL
  have hLL : Lᵀ * L = 1 := by
    rw [hL]
    exact CFSG.ClassicalInvolution.Phan.blockSel_transpose_mul_self h
  refine le_antisymm ?_ ?_
  · calc (L * (A - 1) * Lᵀ).rank = ((L * (A - 1)) * Lᵀ).rank := by rw [Matrix.mul_assoc]
      _ ≤ (L * (A - 1)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (A - 1).rank := Matrix.rank_mul_le_right _ _
  · have hY : Lᵀ * (L * (A - 1) * Lᵀ) * L = A - 1 := by
      have key : ∀ B : Matrix (Fin k) (Fin k) F, Lᵀ * (L * B * Lᵀ) * L = B := by
        intro B
        calc Lᵀ * (L * B * Lᵀ) * L = (Lᵀ * L) * B * (Lᵀ * L) := by
              simp only [Matrix.mul_assoc]
          _ = B := by rw [hLL, Matrix.one_mul, Matrix.mul_one]
      exact key (A - 1)
    have hle : (Lᵀ * (L * (A - 1) * Lᵀ) * L).rank ≤ (L * (A - 1) * Lᵀ).rank :=
      le_trans (Matrix.rank_mul_le_left (Lᵀ * (L * (A - 1) * Lᵀ)) L)
        (Matrix.rank_mul_le_right Lᵀ (L * (A - 1) * Lᵀ))
    rwa [hY] at hle

theorem blockMat_blockMat_zero {F : Type*} [Field F] {m l k : ℕ} (hkl : k ≤ l)
    (A : Matrix (Fin k) (Fin k) F) :
    CFSG.ClassicalInvolution.Phan.blockMat m 0 (CFSG.ClassicalInvolution.Phan.blockMat l 0 A) =
      CFSG.ClassicalInvolution.Phan.blockMat m 0 A := by
  have hinner : CFSG.ClassicalInvolution.Phan.blockMat l 0 A - 1 =
      CFSG.ClassicalInvolution.Phan.blockSel F l k 0 * (A - 1) *
        (CFSG.ClassicalInvolution.Phan.blockSel F l k 0)ᵀ :=
    wcru_blockMat_sub_one A
  have key : CFSG.ClassicalInvolution.Phan.blockMat m 0
        (CFSG.ClassicalInvolution.Phan.blockMat l 0 A) - 1 =
      CFSG.ClassicalInvolution.Phan.blockMat m 0 A - 1 := by
    rw [wcru_blockMat_sub_one (m := m) (i := 0)
        (A := CFSG.ClassicalInvolution.Phan.blockMat l 0 A),
      wcru_blockMat_sub_one (m := m) (i := 0) (A := A), hinner]
    generalize (A - 1) = B
    have hre : CFSG.ClassicalInvolution.Phan.blockSel F m l 0 *
          (CFSG.ClassicalInvolution.Phan.blockSel F l k 0 * B *
            (CFSG.ClassicalInvolution.Phan.blockSel F l k 0)ᵀ) *
          (CFSG.ClassicalInvolution.Phan.blockSel F m l 0)ᵀ =
        (CFSG.ClassicalInvolution.Phan.blockSel F m l 0 *
            CFSG.ClassicalInvolution.Phan.blockSel F l k 0) * B *
          ((CFSG.ClassicalInvolution.Phan.blockSel F l k 0)ᵀ *
            (CFSG.ClassicalInvolution.Phan.blockSel F m l 0)ᵀ) := by
      simp only [Matrix.mul_assoc]
    rw [hre, wcru_blockSel_mul hkl, ← Matrix.transpose_mul, wcru_blockSel_mul hkl]
  have := congrArg (fun M : Matrix (Fin m) (Fin m) F => M + 1) key
  simpa using this

theorem rank_permSU_swap_sub_one {n : ℕ} {F₀ : Type} [Field F₀] [CharP F₀ 2] :
    Matrix.rank ((((permSU n F₀ (Equiv.swap 0 1) : ↥(StatedSU 3 (2 ^ n) F₀)) : GL (Fin 3) F₀) :
      Matrix (Fin 3) (Fin 3) F₀) - 1) = 1 := by
  rw [coe_permSU]
  have hM : (((CFSG.RankThree.Classical.permGL (Equiv.swap 0 1) : GL (Fin 3) F₀) :
      Matrix (Fin 3) (Fin 3) F₀) - 1) =
        Matrix.vecMulVec (![1, 1, 0] : Fin 3 → F₀) ![1, 1, 0] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.sub_apply, Matrix.vecMulVec_apply, Matrix.permMatrixHom_apply,
        PEquiv.toMatrix_toPEquiv_apply, Pi.single_apply, Equiv.swap_apply_def,
        CharTwo.neg_eq]
  rw [hM]
  have hu : (![1, 1, 0] : Fin 3 → F₀) ≠ 0 := by
    intro h
    have h0 : (1 : F₀) = 0 := by simpa using congrFun h 0
    exact one_ne_zero h0
  rw [wcru_rank_vecMulVec_eq_one hu hu]

theorem isUnitaryTransvection_not_mem_center_of_two_le {X : Type} [Group X] {m n : ℕ}
    (hm : 2 ≤ m) {x : X} (hx : IsUnitaryTransvection X m n x) : x ∉ Subgroup.center X := by
  classical
  obtain ⟨F, hF, hFfin, hcard, e, g, hge, hgrank⟩ := hx
  intro hxc
  have hx1 : (QuotientGroup.mk x : X ⧸ Subgroup.center X) = 1 :=
    (QuotientGroup.eq_one_iff x).2 hxc
  have hg1 : (QuotientGroup.mk g : StatedProj (StatedSU m (2 ^ n) F)) = 1 := by
    rw [hge, hx1, map_one]
  have hgmem : (g : GL (Fin m) F) ∈ StatedScalars (Fin m) F := by
    have h := (QuotientGroup.eq_one_iff g).1 hg1
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  rw [StatedScalars, MonoidHom.mem_range] at hgmem
  obtain ⟨c, hc⟩ := hgmem
  have hgmat : ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) =
      Matrix.scalar (Fin m) (c : F) := by
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar]
  have hdiag : (((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) - 1 =
      ((c : F) - 1) • (1 : Matrix (Fin m) (Fin m) F) := by
    rw [hgmat, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, sub_smul, one_smul]
  have hrank01 : ((((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) - 1).rank = 0 ∨
      ((((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) - 1).rank = m := by
    rw [hdiag]
    by_cases h : (c : F) - 1 = 0
    · left
      rw [h, zero_smul, Matrix.rank_zero]
    · right
      rw [Matrix.rank_smul_of_mem_nonZeroDivisors (1 : Matrix (Fin m) (Fin m) F)
        (mem_nonZeroDivisors_of_ne_zero h), Matrix.rank_one, Fintype.card_fin]
  rcases hrank01 with h | h <;> rw [h] at hgrank <;> omega

theorem exists_mul_mul_inv_eq_of_rank_sub_one_eq_one {m n : ℕ} {F₀ : Type} [Field F₀]
    [Finite F₀] (hcard : Nat.card F₀ = (2 ^ n) ^ 2) (hm : 3 ≤ m)
    {g g' : ↥(StatedSU m (2 ^ n) F₀)}
    (hg : Matrix.rank (((g : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1) = 1)
    (hg' : Matrix.rank (((g' : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1) = 1) :
    ∃ a : ↥(StatedSU m (2 ^ n) F₀), a * g * a⁻¹ = g' := by
  have hn : 1 ≤ n := by
    by_contra h
    have hn0 : n = 0 := by omega
    have hc := hcard
    rw [hn0, pow_zero, one_pow] at hc
    have := Finite.one_lt_card (α := F₀)
    omega
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 n F₀ :=
    ⟨Nat.prime_two, hn, by rw [hcard, ← pow_mul, mul_comm]⟩
  have hdet : (((g : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀)).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSU g.2
  obtain ⟨p, r, hp, hr, hrp, hMeq⟩ :=
    CFSG.RankThree.GF2n.Smith81.exists_eq_dihTv_of_rank_eq_one (M :=
      ((g : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀)) hg hdet
  have hg2 : (((g : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1) *
      (((g : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1) = 0 := by
    have hsub : ((g : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1 =
        Matrix.vecMulVec p r := by
      rw [hMeq]
      unfold CFSG.RankThree.GF2n.Smith81.dihTv
      abel
    rw [hsub, Matrix.vecMulVec_mul_vecMulVec, hrp, zero_smul, Matrix.vecMulVec_zero]
  obtain ⟨b, hb0, hb, hgeq⟩ :=
    CFSG.RankThree.GF2n.Smith81.S81C.su_transv_form hU g.2 hg2 hg
  have hdet' : (((g' : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀)).det = 1 :=
    CFSG.Open.StatedAPI.det_of_mem_statedSU g'.2
  obtain ⟨p', r', hp', hr', hrp', hMeq'⟩ :=
    CFSG.RankThree.GF2n.Smith81.exists_eq_dihTv_of_rank_eq_one (M :=
      ((g' : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀)) hg' hdet'
  have hg2' : (((g' : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1) *
      (((g' : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1) = 0 := by
    have hsub : ((g' : GL (Fin m) F₀) : Matrix (Fin m) (Fin m) F₀) - 1 =
        Matrix.vecMulVec p' r' := by
      rw [hMeq']
      unfold CFSG.RankThree.GF2n.Smith81.dihTv
      abel
    rw [hsub, Matrix.vecMulVec_mul_vecMulVec, hrp', zero_smul, Matrix.vecMulVec_zero]
  obtain ⟨b', hb0', hb', hgeq'⟩ :=
    CFSG.RankThree.GF2n.Smith81.S81C.su_transv_form hU g'.2 hg2' hg'
  obtain ⟨W, hWmem, hconj⟩ :=
    CFSG.RankThree.GF2n.Smith81.S81C.su_conj_tvMat hU hm hb0 hb hb0' hb' g.2 g'.2 hgeq hgeq'
  exact ⟨⟨W, hWmem⟩, by
    apply Subtype.ext
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using hconj⟩

end CFSG.LocalAnalysis.WeakClosure81

end
