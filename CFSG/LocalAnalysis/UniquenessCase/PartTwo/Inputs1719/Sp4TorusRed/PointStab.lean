module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.PointUnip
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.Weyl
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed.SmithRootFree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQS
open CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {K : Type} [Field K]

local notation "spMat " g =>
  (((g : StatedSp 2 K) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)

def FixesLine (y : StatedSp 2 K) (c : K) : Prop :=
  (spMat y) *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1

def IsPointStab (y : StatedSp 2 K) : Prop := ∃ c, FixesLine y c

theorem fixesLine_one : FixesLine (1 : StatedSp 2 K) 1 := by
  show (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ Pi.single (Sum.inl 0) 1 = _
  rw [Matrix.one_mulVec, one_smul]

theorem col_of_fixesLine {y : StatedSp 2 K} {c : K} (h : FixesLine y c)
    (i : Fin 2 ⊕ Fin 2) :
    (spMat y) i (Sum.inl 0) = if i = Sum.inl 0 then c else 0 := by
  have h' := congrFun h i
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply,
    Pi.single_apply] at h'
  rw [h']
  by_cases hi : i = Sum.inl 0 <;> simp [hi]

variable [CharP K 2]

theorem f0_entry_mul_of_fixesLine {y : StatedSp 2 K} {c : K} (h : FixesLine y c) :
    (spMat y) (Sum.inr 0) (Sum.inr 0) * c = 1 := by
  have hJ := mem_statedSp_iff.mp y.2
  have hentry := congrFun (congrFun hJ (Sum.inr 0)) (Sum.inl 0)
  rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inl 0)] at hentry
  · rw [Matrix.mul_apply, Finset.sum_eq_single (Sum.inr 0)] at hentry
    · simpa [Matrix.transpose_apply, fromBlocks_J_apply, col_of_fixesLine h] using hentry
    · intro a _ ha
      rw [Matrix.transpose_apply, fromBlocks_J_apply]
      simp only [Sum.swap_inl]
      simp [ha]
    · simp
  · intro k _ hk
    rw [col_of_fixesLine h k, if_neg hk, mul_zero]
  · simp

theorem scalar_ne_zero_of_fixesLine {y : StatedSp 2 K} {c : K} (h : FixesLine y c) : c ≠ 0 := by
  intro hc
  have h1 := f0_entry_mul_of_fixesLine h
  rw [hc, mul_zero] at h1
  exact zero_ne_one h1

theorem row_of_fixesLine {y : StatedSp 2 K} {c : K} (h : FixesLine y c)
    (j : Fin 2 ⊕ Fin 2) :
    (spMat y) (Sum.inr 0) j = if j = Sum.inr 0 then c⁻¹ else 0 := by
  have hc : c ≠ 0 := scalar_ne_zero_of_fixesLine h
  set M := spMat y with hM
  set N := spMat y⁻¹ with hN
  have hMN : M * N = 1 := by
    rw [hM, hN, ← TorusQS.spMat_mul, mul_inv_cancel]
    rfl
  have hNM : N * M = 1 := by
    rw [hM, hN, ← TorusQS.spMat_mul, inv_mul_cancel]
    rfl
  have hMe : M *ᵥ (N *ᵥ Pi.single (Sum.inl 0) 1) = Pi.single (Sum.inl 0) 1 := by
    rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec]
  have hNe : N *ᵥ Pi.single (Sum.inl 0) 1 = c⁻¹ • Pi.single (Sum.inl 0) 1 := by
    have hinj : Function.Injective (fun u => M *ᵥ u) := by
      intro u v huv
      have := congrArg (fun w => N *ᵥ w) huv
      simpa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using this
    apply hinj
    change M *ᵥ (N *ᵥ Pi.single (Sum.inl 0) 1) = M *ᵥ (c⁻¹ • Pi.single (Sum.inl 0) 1)
    rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec, Matrix.mulVec_smul]
    rw [show M *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1 from h]
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hkey : ∀ u : Fin 2 ⊕ Fin 2 → K, (M *ᵥ u) (Sum.inr 0) = c⁻¹ * u (Sum.inr 0) := by
    intro u
    have h1 : (M *ᵥ u) (Sum.inr 0) =
        pairedSympForm K 2
          (Pi.single (Sum.inl 0) 1) (M *ᵥ u) := by
      rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.pairedSympForm_single_apply]
      simp [lineSign]
    rw [h1]
    calc pairedSympForm K 2
          (Pi.single (Sum.inl 0) 1) (M *ᵥ u)
        = pairedSympForm K 2
            (M *ᵥ (N *ᵥ Pi.single (Sum.inl 0) 1)) (M *ᵥ u) := by rw [hMe]
      _ = pairedSympForm K 2
            (N *ᵥ Pi.single (Sum.inl 0) 1) u :=
          CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.pairedSympForm_mulVec y _ _
      _ = pairedSympForm K 2
            (c⁻¹ • Pi.single (Sum.inl 0) 1) u := by rw [hNe]
      _ = c⁻¹ * pairedSympForm K 2
            (Pi.single (Sum.inl 0) 1) u := by simp
      _ = c⁻¹ * u (Sum.inr 0) := by
          rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.pairedSympForm_single_apply]
          simp [lineSign]
  have h := hkey (Pi.single j 1)
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h]
  by_cases hj : j = Sum.inr 0
  · simp [hj]
  · simp [hj, Ne.symm hj]

omit [CharP K 2] in
theorem fixesLine_of_col {y : StatedSp 2 K} {c : K}
    (h : ∀ i, (spMat y) i (Sum.inl 0) = if i = Sum.inl 0 then c else 0) : FixesLine y c := by
  show (spMat y) *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1
  ext j
  rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.smul_apply, Pi.single_apply, h j]
  by_cases hj : j = Sum.inl 0 <;> simp [hj]

def HasPointEntries (y : StatedSp 2 K) (c : K) : Prop :=
  (∀ i, (spMat y) i (Sum.inl 0) = if i = Sum.inl 0 then c else 0) ∧
    (∀ j, (spMat y) (Sum.inr 0) j = if j = Sum.inr 0 then c⁻¹ else 0) ∧ c ≠ 0

theorem hasPointEntries_of_fixesLine {y : StatedSp 2 K} {c : K} (h : FixesLine y c) :
    HasPointEntries y c :=
  ⟨col_of_fixesLine h, row_of_fixesLine h, scalar_ne_zero_of_fixesLine h⟩

omit [CharP K 2] in
theorem hasPointEntries_mul {y z : StatedSp 2 K} {c d : K} (hy : HasPointEntries y c)
    (hz : HasPointEntries z d) : HasPointEntries (y * z) (c * d) := by
  have hy0 := hy.1
  have hz0 := hz.1
  have hy1 := hy.2.1
  have hz1 := hz.2.1
  have hc := hy.2.2
  have hd := hz.2.2
  have hmul : (spMat (y * z)) = (spMat y) * (spMat z) := TorusQS.spMat_mul y z
  refine ⟨fun i => ?_, fun j => ?_, mul_ne_zero hc hd⟩
  · rw [hmul, Matrix.mul_apply]
    rw [Finset.sum_eq_single (Sum.inl 0)]
    · rw [hy0 i, hz0 (Sum.inl 0)]
      by_cases hi : i = Sum.inl 0 <;> simp [hi]
    · intro k _ hk
      rw [hz0 k, if_neg hk, mul_zero]
    · simp
  · rw [hmul, Matrix.mul_apply]
    rw [Finset.sum_eq_single (Sum.inr 0)]
    · rw [hy1 (Sum.inr 0), hz1 j]
      by_cases hj : j = Sum.inr 0 <;> simp [hj, mul_inv_rev, mul_comm]
    · intro k _ hk
      rw [hy1 k, if_neg hk, zero_mul]
    · simp

theorem hasPointEntries_inv {y : StatedSp 2 K} {c : K} (h : HasPointEntries y c) :
    HasPointEntries y⁻¹ c⁻¹ := by
  have hc := h.2.2
  refine ⟨fun i => ?_, fun j => ?_, inv_ne_zero hc⟩
  · rw [TorusQS.spMat_inv_apply, Sum.swap_inl]
    rw [h.2.1 i.swap]
    by_cases hi : i = Sum.inl 0
    · simp [hi]
    · rw [if_neg hi, if_neg (fun hh : i.swap = Sum.inr 0 => hi (by
        have := congrArg Sum.swap hh
        simpa using this))]
  · rw [TorusQS.spMat_inv_apply, Sum.swap_inr]
    rw [h.1 j.swap]
    by_cases hj : j = Sum.inr 0
    · simp [hj]
    · rw [if_neg hj, if_neg (fun hh : j.swap = Sum.inl 0 => hj (by
        have := congrArg Sum.swap hh
        simpa using this))]

def pointStab : Subgroup (StatedSp 2 K) where
  carrier := {y | IsPointStab y}
  one_mem' := ⟨1, fixesLine_one⟩
  mul_mem' := by
    rintro y z ⟨c, hc⟩ ⟨d, hd⟩
    exact ⟨c * d, fixesLine_of_col (hasPointEntries_mul
      (hasPointEntries_of_fixesLine hc) (hasPointEntries_of_fixesLine hd)).1⟩
  inv_mem' := by
    rintro y ⟨c, hc⟩
    exact ⟨c⁻¹, fixesLine_of_col (hasPointEntries_inv
      (hasPointEntries_of_fixesLine hc)).1⟩

theorem pointStab_hasPointEntries (y : pointStab (K := K)) :
    HasPointEntries (y : StatedSp 2 K) ((spMat (y : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0)) := by
  obtain ⟨c, hc⟩ := y.2
  have h := hasPointEntries_of_fixesLine hc
  have hc' : (spMat (y : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) = c := by
    simpa using h.1 (Sum.inl 0)
  rw [hc']
  exact h

noncomputable def chi : pointStab (K := K) →* Kˣ where
  toFun y := Units.mk0 ((spMat (y : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0))
    (pointStab_hasPointEntries y).2.2
  map_one' := by
    apply Units.ext
    show (spMat ((1 : pointStab (K := K)) : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) = _
    simp
  map_mul' := by
    intro y z
    apply Units.ext
    have hy := pointStab_hasPointEntries y
    have hz := pointStab_hasPointEntries z
    have h := hasPointEntries_mul hy hz
    have h1 := h.1 (Sum.inl 0)
    change (spMat (((y * z : pointStab (K := K)) : StatedSp 2 K))) (Sum.inl 0) (Sum.inl 0) =
      (spMat (y : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) *
        (spMat (z : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0)
    rw [show ((y * z : pointStab (K := K)) : StatedSp 2 K) =
      (y : StatedSp 2 K) * (z : StatedSp 2 K) from rfl]
    exact h1

@[expose] def planeIdx : Fin 2 → Fin 2 ⊕ Fin 2 := ![Sum.inl 1, Sum.inr 1]

theorem planeIdx_mem (j : Fin 2) :
    planeIdx j ≠ Sum.inl 0 ∧ planeIdx j ≠ Sum.inr 0 := by
  fin_cases j <;> simp [planeIdx]

theorem planeIdx_zero : planeIdx 0 = Sum.inl 1 := rfl

theorem planeIdx_one : planeIdx 1 = Sum.inr 1 := rfl

@[expose] noncomputable def blockMat (y : pointStab (K := K)) : Matrix (Fin 2) (Fin 2) K :=
  Matrix.of fun i j => (spMat (y : StatedSp 2 K)) (planeIdx i) (planeIdx j)

theorem blockMat_apply (y : pointStab (K := K)) (i j : Fin 2) :
    blockMat y i j = (spMat (y : StatedSp 2 K)) (planeIdx i) (planeIdx j) := rfl

theorem row_plane_zero (z : pointStab (K := K)) (j : Fin 2) :
    (spMat (z : StatedSp 2 K)) (Sum.inr 0) (planeIdx j) = 0 := by
  have h := pointStab_hasPointEntries z
  rw [h.2.1 (planeIdx j), if_neg (planeIdx_mem j).2]

theorem blockMat_mul (y z : pointStab (K := K)) :
    blockMat (y * z) = blockMat y * blockMat z := by
  ext i j
  rw [blockMat_apply, Matrix.mul_apply]
  have hmul : (spMat (((y * z : pointStab (K := K)) : StatedSp 2 K))) =
      (spMat (y : StatedSp 2 K)) * (spMat (z : StatedSp 2 K)) := by
    rw [show ((y * z : pointStab (K := K)) : StatedSp 2 K) =
      (y : StatedSp 2 K) * (z : StatedSp 2 K) from rfl]
    exact TorusQS.spMat_mul _ _
  rw [hmul, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [col_of_fixesLine (fixesLine_of_col (pointStab_hasPointEntries y).1) (planeIdx i),
    if_neg (planeIdx_mem i).1, zero_mul,
    row_plane_zero z j, mul_zero]
  simp only [zero_add]
  rw [Fin.sum_univ_two, blockMat_apply, blockMat_apply, blockMat_apply, blockMat_apply]
  simp [planeIdx]

theorem blockMat_det (y : pointStab (K := K)) : (blockMat y).det = 1 := by
  have hJ := mem_statedSp_iff.mp (y : StatedSp 2 K).2
  have hentry := congrFun (congrFun hJ (Sum.inl 1)) (Sum.inr 1)
  have hrow := (pointStab_hasPointEntries y).2.1
  have hcol := (pointStab_hasPointEntries y).1
  rw [Matrix.det_fin_two]
  simp only [blockMat_apply, planeIdx, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hform :
      pairedSympForm K 2 ((spMat (y : StatedSp 2 K)) *ᵥ Pi.single (Sum.inl 1) 1)
        ((spMat (y : StatedSp 2 K)) *ᵥ Pi.single (Sum.inr 1) 1) = 1 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.pairedSympForm_mulVec,
      pairedSympForm_single]
  rw [Matrix.mulVec_single_one, Matrix.mulVec_single_one,
    pairedSympForm_apply] at hform
  have h1 : ((spMat (y : StatedSp 2 K)).col (Sum.inl 1) ∘ Sum.inl) ⬝ᵥ
      ((spMat (y : StatedSp 2 K)).col (Sum.inr 1) ∘ Sum.inr) =
      (spMat (y : StatedSp 2 K)) (Sum.inl 1) (Sum.inl 1) *
        (spMat (y : StatedSp 2 K)) (Sum.inr 1) (Sum.inr 1) := by
    simp [dotProduct, Fin.sum_univ_two, Matrix.col_apply, hrow]
  have h2 : ((spMat (y : StatedSp 2 K)).col (Sum.inl 1) ∘ Sum.inr) ⬝ᵥ
      ((spMat (y : StatedSp 2 K)).col (Sum.inr 1) ∘ Sum.inl) =
      (spMat (y : StatedSp 2 K)) (Sum.inr 1) (Sum.inl 1) *
        (spMat (y : StatedSp 2 K)) (Sum.inl 1) (Sum.inr 1) := by
    simp [dotProduct, Fin.sum_univ_two, Matrix.col_apply, hrow]
  rw [h1, h2] at hform
  rw [mul_comm ((spMat (y : StatedSp 2 K)) (Sum.inl 1) (Sum.inr 1))
    ((spMat (y : StatedSp 2 K)) (Sum.inr 1) (Sum.inl 1))]
  exact hform

theorem planeIdx_injective : Function.Injective planeIdx := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [planeIdx]

theorem blockMat_one : blockMat (1 : pointStab (K := K)) = 1 := by
  ext i j
  rw [blockMat_apply, Matrix.one_apply]
  show (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (planeIdx i) (planeIdx j) = _
  rw [Matrix.one_apply]
  by_cases h : i = j
  · subst h; simp [planeIdx]
  · rw [if_neg h, if_neg (fun hh => h (planeIdx_injective hh))]

@[expose] noncomputable def blockElt :
    pointStab (K := K) →* Matrix.SpecialLinearGroup (Fin 2) K where
  toFun y := ⟨blockMat y, blockMat_det y⟩
  map_one' := by
    apply Subtype.ext
    exact blockMat_one
  map_mul' := by
    intro y z
    apply Subtype.ext
    exact blockMat_mul y z

theorem coe_blockElt (y : pointStab (K := K)) :
    ((blockElt y : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      blockMat y := rfl

theorem isPointUnip_of_chi_eq_one_of_blockElt_eq_one {y : pointStab (K := K)}
    (hχ : chi y = 1) (hℓ : blockElt y = 1) : IsPointUnip (y : StatedSp 2 K) := by
  have h := pointStab_hasPointEntries y
  have hb : blockMat y = 1 := congrArg Subtype.val hℓ
  have hc : (spMat (y : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) = 1 := by
    have h1 : ((chi y : Kˣ) : K) = (spMat (y : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) := rfl
    rw [hχ] at h1
    simpa using h1.symm
  have e00 : (spMat (y : StatedSp 2 K)) (Sum.inl 1) (Sum.inl 1) = 1 := by
    have := congrFun (congrFun hb 0) 0
    simpa [blockMat_apply, planeIdx] using this
  have e01 : (spMat (y : StatedSp 2 K)) (Sum.inl 1) (Sum.inr 1) = 0 := by
    have := congrFun (congrFun hb 0) 1
    simpa [blockMat_apply, planeIdx] using this
  have e10 : (spMat (y : StatedSp 2 K)) (Sum.inr 1) (Sum.inl 1) = 0 := by
    have := congrFun (congrFun hb 1) 0
    simpa [blockMat_apply, planeIdx] using this
  have e11 : (spMat (y : StatedSp 2 K)) (Sum.inr 1) (Sum.inr 1) = 1 := by
    have := congrFun (congrFun hb 1) 1
    simpa [blockMat_apply, planeIdx] using this
  unfold IsPointUnip
  constructor
  · intro i j hj hi
    by_cases hj0 : j = Sum.inl 0
    · subst hj0
      rw [h.1 i]
      by_cases hi0 : i = Sum.inl 0
      · rw [if_pos hi0, if_pos hi0, hc]
      · rw [if_neg hi0, if_neg hi0]
    by_cases hi0 : i = Sum.inr 0
    · subst hi0
      rw [h.2.1 j, if_neg hj, if_neg (Ne.symm hj)]
    rcases i with i | i
    · fin_cases i
      · exact absurd rfl hi
      · rcases j with j | j
        · fin_cases j
          · exact absurd rfl hj0
          · simpa using e00
        · fin_cases j
          · exact absurd rfl hj
          · simpa using e01
    · fin_cases i
      · exact absurd rfl hi0
      · rcases j with j | j
        · fin_cases j
          · exact absurd rfl hj0
          · simpa using e10
        · fin_cases j
          · exact absurd rfl hj
          · simpa using e11
  · rw [h.2.1 (Sum.inr 0)]
    simp [hc]

theorem torus_le_pointStab : torus 2 K ≤ pointStab (K := K) := by
  rintro _ ⟨t, rfl⟩
  refine ⟨(t 0 : K), ?_⟩
  show (spMat (torusHom t : StatedSp 2 K)) *ᵥ Pi.single (Sum.inl 0) 1 = _
  ext j
  rw [coe_torusHom, Matrix.mulVec_single_one, Matrix.col_apply,
    Matrix.diagonal_apply, Pi.smul_apply, Pi.single_apply]
  by_cases hj : j = Sum.inl 0
  · subst hj; simp
  · simp [hj]

@[expose] noncomputable def torusPoint (t : Fin 2 → Kˣ) : pointStab (K := K) :=
  ⟨torusHom t, torus_le_pointStab (torusHom_mem_torus t)⟩

theorem coe_torusPoint (t : Fin 2 → Kˣ) :
    ((torusPoint t : pointStab (K := K)) : StatedSp 2 K) = torusHom t := rfl

theorem chi_torusPoint (t : Fin 2 → Kˣ) : chi (torusPoint t) = t 0 := by
  apply Units.ext
  change (spMat (torusHom t : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) = (t 0 : K)
  rw [coe_torusHom, Matrix.diagonal_apply]
  simp

theorem blockMat_torusPoint (t : Fin 2 → Kˣ) :
    blockMat (torusPoint t) = sl2Diag (t 1) := by
  ext i j
  rw [blockMat_apply, coe_torusPoint, coe_torusHom, coe_sl2Diag, Matrix.diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [planeIdx]

theorem blockElt_torusPoint (t : Fin 2 → Kˣ) :
    blockElt (torusPoint t) = sl2Diag (t 1) := by
  apply Subtype.ext
  exact blockMat_torusPoint t

theorem conj_sl2Up_sl2Diag (s : K) (u : Kˣ) :
    sl2Up K s * sl2Diag u * (sl2Up K s)⁻¹ * (sl2Diag u)⁻¹ =
      sl2Up K (s * (1 + (u : K) ^ 2)) := by
  have hup : ((sl2Up K s)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) = sl2Up K s := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [coe_sl2Up_inv]
    fin_cases i <;> fin_cases j <;> simp [sl2Up, CharTwo.neg_eq]
  have hdinv : ((sl2Diag u)⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) = sl2Diag u⁻¹ :=
    (map_inv (sl2Diag (k := K)) u).symm
  rw [hup, hdinv]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, coe_sl2Diag, coe_sl2Diag]
  fin_cases i <;> fin_cases j <;> simp [sl2Up, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp
  all_goals ring

variable [Finite K]

theorem blockElt_eq_one_of_mem_utri (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {y : pointStab (K := K)} (hyX : (y : StatedSp 2 K) ∈ X)
    (hyU : blockElt y ∈ CFSG.CGT.Timmesfeld75.utri K) : blockElt y = 1 := by
  classical

  have hyU' := CFSG.CGT.Timmesfeld75.mem_utri_entries.mp hyU
  have h10 : blockMat y 1 0 = 0 := hyU'.1
  have h00 : blockMat y 0 0 = 1 := hyU'.2
  have h11 : blockMat y 1 1 = 1 := by
    have hd := blockMat_det y
    rw [Matrix.det_fin_two, h00, h10] at hd
    simpa using hd
  by_cases hs : blockMat y 0 1 = 0
  ·
    apply Subtype.ext
    change blockMat y = (1 : Matrix (Fin 2) (Fin 2) K)
    ext i j
    fin_cases i <;> fin_cases j <;> simp [h00, h10, hs, h11]
  obtain ⟨a, ha0, ha1⟩ : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
    have hord : orderOf ζ = Nat.card K - 1 := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
    have hζ1 : ζ ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hord
      omega
    refine ⟨1 + (ζ : K), ?_, ?_⟩
    · intro h
      apply hζ1
      have h1 : (ζ : K) = -1 := by linear_combination h
      rw [CharTwo.neg_eq] at h1
      exact Units.ext h1
    · intro h
      have h1 : (ζ : K) = 0 := by linear_combination h
      exact ζ.ne_zero h1
  let u : Kˣ := Units.mk0 a ha0
  have hu1 : (u : K) ≠ 1 := by simpa [u] using ha1
  have hone : ∀ {v : K}, v ≠ 1 → v + 1 ≠ 0 := fun {v} hv => by
    have h : v - 1 ≠ 0 := sub_ne_zero.mpr hv
    simpa [sub_eq_add_neg, CharTwo.neg_eq] using h
  have hsq : ∀ {v : K}, v ≠ 1 → 1 + v ^ 2 ≠ 0 := fun {v} hv => by
    have hv2 : v ^ 2 ≠ 1 := by
      intro h
      rcases sq_eq_one_iff.mp h with h1 | h1
      · exact hv h1
      · rw [CharTwo.neg_eq] at h1
        exact hv h1
    have h : v ^ 2 - 1 ≠ 0 := sub_ne_zero.mpr hv2
    simpa [sub_eq_add_neg, CharTwo.neg_eq, add_comm] using h
  let h1 : pointStab (K := K) := torusPoint ![1, u]
  let h2 : pointStab (K := K) := torusPoint ![u, 1]
  have hchi1 : chi h1 = 1 := by simp [h1, chi_torusPoint]
  have hchi2 : chi h2 = u := by simp [h2, chi_torusPoint]
  have hblock1 : blockElt h1 = sl2Diag u := by simp [h1, blockElt_torusPoint]
  have hblock2 : blockElt h2 = 1 := by simp [h2, blockElt_torusPoint]
  have h1X : (h1 : StatedSp 2 K) ∈ X := by
    have : (h1 : StatedSp 2 K) = torusHom ![1, u] := rfl
    rw [this]
    exact hT (torusHom_mem_torus _)
  have h2X : (h2 : StatedSp 2 K) ∈ X := by
    have : (h2 : StatedSp 2 K) = torusHom ![u, 1] := rfl
    rw [this]
    exact hT (torusHom_mem_torus _)
  let z : pointStab (K := K) := y * h1 * y⁻¹ * h1⁻¹
  have hchi_z : chi z = 1 := by
    simp only [z, map_mul, map_inv, hchi1, mul_one, inv_one]
    exact mul_inv_cancel (chi y)
  have hblock_z : blockElt z = sl2Up K ((blockMat y) 0 1 * (1 + (u : K) ^ 2)) := by
    have hB : blockElt y = sl2Up K ((blockMat y) 0 1) := by
      apply Subtype.ext
      rw [coe_blockElt]
      change blockMat y = (sl2Up K ((blockMat y) 0 1) :
        Matrix.SpecialLinearGroup (Fin 2) K)
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sl2Up, h00, h10, h11]
    simp only [z, map_mul, map_inv, hB, hblock1]
    exact conj_sl2Up_sl2Diag _ _
  have hzX : (z : StatedSp 2 K) ∈ X := by
    simp only [z, Subgroup.coe_mul, Subgroup.coe_inv]
    exact X.mul_mem (X.mul_mem (X.mul_mem hyX h1X) (X.inv_mem hyX)) (X.inv_mem h1X)
  let w : pointStab (K := K) := z⁻¹ * h2 * z * h2⁻¹
  have hchi_w : chi w = 1 := by
    simp only [w, map_mul, map_inv, hchi2, hchi_z, mul_one, inv_one]
    group
  have hblock_w : blockElt w = 1 := by
    simp only [w, map_mul, map_inv, hblock2, hblock_z, mul_one, inv_one]
    simp
  have hwQ : IsPointUnip (w : StatedSp 2 K) :=
    isPointUnip_of_chi_eq_one_of_blockElt_eq_one hchi_w hblock_w
  have hwX : (w : StatedSp 2 K) ∈ X := by
    simp only [w, Subgroup.coe_mul, Subgroup.coe_inv]
    exact X.mul_mem (X.mul_mem (X.mul_mem (X.inv_mem hzX) h2X) hzX) (X.inv_mem h2X)
  have hw1 : (w : StatedSp 2 K) = 1 := eq_one_of_isPointUnip hK hT hX hwX hwQ
  have hw_eq : (z : StatedSp 2 K)⁻¹ * (h2 : StatedSp 2 K) * (z : StatedSp 2 K) *
      (h2 : StatedSp 2 K)⁻¹ = 1 := by
    simpa only [w, Subgroup.coe_mul, Subgroup.coe_inv] using hw1
  have hcomm : (z : StatedSp 2 K) * (h2 : StatedSp 2 K) = (h2 : StatedSp 2 K) * z := by
    have h1 : (z : StatedSp 2 K)⁻¹ * (h2 : StatedSp 2 K) * z = h2 := by
      have h := congrArg (fun g : StatedSp 2 K => g * (h2 : StatedSp 2 K)) hw_eq
      simpa [mul_assoc] using h
    calc (z : StatedSp 2 K) * h2 = z * ((z : StatedSp 2 K)⁻¹ * h2 * z) := by rw [h1]
      _ = h2 * z := by group
  have hentry : ∀ i j : Fin 2 ⊕ Fin 2,
      (spMat z) i j * (spMat (h2 : StatedSp 2 K)) j j =
        (spMat (h2 : StatedSp 2 K)) i i * (spMat z) i j := by
    intro i j
    have h := congrFun (congrFun (congrArg (fun g : StatedSp 2 K => spMat g) hcomm) i) j
    rw [TorusQS.spMat_mul, TorusQS.spMat_mul] at h
    have hd : (spMat (h2 : StatedSp 2 K)) =
        Matrix.diagonal (Sum.elim (fun i => ((![u, 1] i : Kˣ) : K))
          fun i => (((![u, 1] i)⁻¹ : Kˣ) : K)) := by
      rw [show (h2 : StatedSp 2 K) = torusHom ![u, 1] from rfl, coe_torusHom]
    rw [hd, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
    rw [hd]
    simpa using h
  have hd0 : (spMat (h2 : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) = (u : K) := by
    rw [show (h2 : StatedSp 2 K) = torusHom ![u, 1] from rfl, coe_torusHom,
      Matrix.diagonal_apply]
    simp
  have hd1 : (spMat (h2 : StatedSp 2 K)) (Sum.inl 1) (Sum.inl 1) = 1 := by
    rw [show (h2 : StatedSp 2 K) = torusHom ![u, 1] from rfl, coe_torusHom,
      Matrix.diagonal_apply]
    simp
  have hd2 : (spMat (h2 : StatedSp 2 K)) (Sum.inr 1) (Sum.inr 1) = 1 := by
    rw [show (h2 : StatedSp 2 K) = torusHom ![u, 1] from rfl, coe_torusHom,
      Matrix.diagonal_apply]
    simp
  have hdf : (spMat (h2 : StatedSp 2 K)) (Sum.inr 0) (Sum.inr 0) = (u : K)⁻¹ := by
    rw [show (h2 : StatedSp 2 K) = torusHom ![u, 1] from rfl, coe_torusHom,
      Matrix.diagonal_apply]
    simp
  have h01 : (spMat z) (Sum.inl 0) (Sum.inl 1) = 0 := by
    have he := hentry (Sum.inl 0) (Sum.inl 1)
    rw [hd0, hd1, mul_one] at he
    have h : ((u : K) + 1) * (spMat z) (Sum.inl 0) (Sum.inl 1) = 0 := by
      calc ((u : K) + 1) * (spMat z) (Sum.inl 0) (Sum.inl 1)
          = (u : K) * (spMat z) (Sum.inl 0) (Sum.inl 1) +
              (spMat z) (Sum.inl 0) (Sum.inl 1) := by rw [add_mul, one_mul]
        _ = 0 := by rw [← he, CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp h).resolve_left (hone hu1)
  have h02 : (spMat z) (Sum.inl 0) (Sum.inr 1) = 0 := by
    have he := hentry (Sum.inl 0) (Sum.inr 1)
    rw [hd0, hd2, mul_one] at he
    have h : ((u : K) + 1) * (spMat z) (Sum.inl 0) (Sum.inr 1) = 0 := by
      calc ((u : K) + 1) * (spMat z) (Sum.inl 0) (Sum.inr 1)
          = (u : K) * (spMat z) (Sum.inl 0) (Sum.inr 1) +
              (spMat z) (Sum.inl 0) (Sum.inr 1) := by rw [add_mul, one_mul]
        _ = 0 := by rw [← he, CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp h).resolve_left (hone hu1)
  have h03 : (spMat z) (Sum.inl 0) (Sum.inr 0) = 0 := by
    have he := hentry (Sum.inl 0) (Sum.inr 0)
    rw [hd0, hdf] at he
    have he' : (spMat z) (Sum.inl 0) (Sum.inr 0) =
        (u : K) ^ 2 * (spMat z) (Sum.inl 0) (Sum.inr 0) := by
      have h := he
      field_simp at h
      simpa [mul_comm] using h
    have h : (1 + (u : K) ^ 2) * (spMat z) (Sum.inl 0) (Sum.inr 0) = 0 := by
      calc (1 + (u : K) ^ 2) * (spMat z) (Sum.inl 0) (Sum.inr 0)
          = (spMat z) (Sum.inl 0) (Sum.inr 0) +
              (u : K) ^ 2 * (spMat z) (Sum.inl 0) (Sum.inr 0) := by rw [add_mul, one_mul]
        _ = 0 := by rw [← he', CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp h).resolve_left (hsq hu1)
  have h13 : (spMat z) (Sum.inl 1) (Sum.inr 0) = 0 := by
    have he := hentry (Sum.inl 1) (Sum.inr 0)
    rw [hd1, hdf] at he
    have he' : (spMat z) (Sum.inl 1) (Sum.inr 0) =
        (u : K) * (spMat z) (Sum.inl 1) (Sum.inr 0) := by
      have h := he
      field_simp at h
      simpa [mul_comm] using h
    have h : ((u : K) + 1) * (spMat z) (Sum.inl 1) (Sum.inr 0) = 0 := by
      calc ((u : K) + 1) * (spMat z) (Sum.inl 1) (Sum.inr 0)
          = (u : K) * (spMat z) (Sum.inl 1) (Sum.inr 0) +
              (spMat z) (Sum.inl 1) (Sum.inr 0) := by rw [add_mul, one_mul]
        _ = 0 := by rw [← he', CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp h).resolve_left (hone hu1)
  have h23 : (spMat z) (Sum.inr 1) (Sum.inr 0) = 0 := by
    have he := hentry (Sum.inr 1) (Sum.inr 0)
    rw [hd2, hdf] at he
    have he' : (spMat z) (Sum.inr 1) (Sum.inr 0) =
        (u : K) * (spMat z) (Sum.inr 1) (Sum.inr 0) := by
      have h := he
      field_simp at h
      simpa [mul_comm] using h
    have h : ((u : K) + 1) * (spMat z) (Sum.inr 1) (Sum.inr 0) = 0 := by
      calc ((u : K) + 1) * (spMat z) (Sum.inr 1) (Sum.inr 0)
          = (u : K) * (spMat z) (Sum.inr 1) (Sum.inr 0) +
              (spMat z) (Sum.inr 1) (Sum.inr 0) := by rw [add_mul, one_mul]
        _ = 0 := by rw [← he', CharTwo.add_self_eq_zero]
    exact (mul_eq_zero.mp h).resolve_left (hone hu1)
  have hc : (spMat z) (Sum.inl 0) (Sum.inl 0) = 1 := by
    have h := (pointStab_hasPointEntries z).1 (Sum.inl 0)
    have hχ : ((chi z : Kˣ) : K) = 1 := by rw [hchi_z]; rfl
    have hval : (spMat (z : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) = ((chi z : Kˣ) : K) := rfl
    rw [hval, hχ]
  have hcol : ∀ i, (spMat z) i (Sum.inl 0) = if i = Sum.inl 0 then 1 else 0 := by
    intro i
    rw [(pointStab_hasPointEntries z).1 i]
    by_cases hi : i = Sum.inl 0
    · subst hi; simp [hc]
    · simp [hi]
  have hrow : ∀ j, (spMat z) (Sum.inr 0) j = if j = Sum.inr 0 then 1 else 0 := by
    intro j
    have h := (pointStab_hasPointEntries z).2.1 j
    have hval : (spMat (z : StatedSp 2 K)) (Sum.inl 0) (Sum.inl 0) = ((chi z : Kˣ) : K) := rfl
    rw [h, hval, hchi_z]
    by_cases hj : j = Sum.inr 0
    · subst hj; simp
    · simp [hj]
  have hze : blockMat z = !![1, (blockMat y) 0 1 * (1 + (u : K) ^ 2); 0, 1] := by
    have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) K =>
      (g : Matrix (Fin 2) (Fin 2) K)) hblock_z
    rw [coe_blockElt] at h
    rw [h]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Up]
  have hz00 : (spMat z) (Sum.inl 1) (Sum.inl 1) = 1 := by
    have h := congrFun (congrFun hze 0) 0
    simpa [blockMat_apply, planeIdx, sl2Up] using h
  have hz01 : (spMat z) (Sum.inl 1) (Sum.inr 1) =
      (blockMat y) 0 1 * (1 + (u : K) ^ 2) := by
    have h := congrFun (congrFun hze 0) 1
    simpa [blockMat_apply, planeIdx, sl2Up] using h
  have hz10 : (spMat z) (Sum.inr 1) (Sum.inl 1) = 0 := by
    have h := congrFun (congrFun hze 1) 0
    simpa [blockMat_apply, planeIdx, sl2Up] using h
  have hz11 : (spMat z) (Sum.inr 1) (Sum.inr 1) = 1 := by
    have h := congrFun (congrFun hze 1) 1
    simpa [blockMat_apply, planeIdx, sl2Up] using h
  have hzroot : (z : StatedSp 2 K) =
      pairRootElt (Sum.inl_ne_inr : (Sum.inl 1 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 1)
        ((blockMat y) 0 1 * (1 + (u : K) ^ 2)) := by
    apply statedSp_ext
    rw [pairRootElt_long, coe_lam]
    change (spMat z) = pairMat (Sum.inl 1) (Sum.inr 1)
      !![1, (blockMat y) 0 1 * (1 + (u : K) ^ 2); 0, 1]
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [hcol, hrow, h01, h02, h03, h13, h23, hz00, hz01, hz10, hz11, pairMat]
  have hzrootX : pairRootElt (Sum.inl_ne_inr : (Sum.inl 1 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 1)
      ((blockMat y) 0 1 * (1 + (u : K) ^ 2)) ∈ X := by
    rw [← hzroot]
    exact hzX
  have ht : (blockMat y) 0 1 * (1 + (u : K) ^ 2) = 0 :=
    hX (Sum.inl 1) (Sum.inr 1) Sum.inl_ne_inr
      ((blockMat y) 0 1 * (1 + (u : K) ^ 2)) hzrootX
  exact absurd ((mul_eq_zero.mp ht).resolve_right (hsq hu1)) hs

noncomputable def pointImage (X : Subgroup (StatedSp 2 K)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) K) :=
  ((X ⊓ pointStab (K := K)).subgroupOf pointStab).map blockElt

omit [Finite K] in
theorem mem_pointImage {X : Subgroup (StatedSp 2 K)} {n : Matrix.SpecialLinearGroup (Fin 2) K} :
    n ∈ pointImage X ↔ ∃ y : pointStab (K := K), (y : StatedSp 2 K) ∈ X ∧ blockElt y = n := by
  rw [pointImage, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, (Subgroup.mem_subgroupOf.mp hy).1, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, Subgroup.mem_subgroupOf.mpr ⟨hy, y.2⟩, rfl⟩

theorem pointImage_inf_utri_eq_bot (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X) :
    pointImage X ⊓ CFSG.CGT.Timmesfeld75.utri K = ⊥ := by
  rw [eq_bot_iff]
  rintro n ⟨hnN, hnU⟩
  obtain ⟨y, hyX, rfl⟩ := mem_pointImage.mp hnN
  exact blockElt_eq_one_of_mem_utri hK hT hX hyX hnU

omit [Finite K] in
theorem pointStab_conj {g n : StatedSp 2 K} (hg : g ∈ pointStab (K := K))
    (hn : (spMat n) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1)
    (hn' : (spMat n⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1) :
    n * g * n⁻¹ ∈ pointStab (K := K) := by
  obtain ⟨c, hc⟩ := hg
  refine ⟨c, ?_⟩
  change (spMat (n * g * n⁻¹)) *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1
  rw [TorusQS.spMat_mul, TorusQS.spMat_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hn', hc, Matrix.mulVec_smul, hn]

omit [Finite K] in
theorem lam_sl2W_fixes_e0 :
    (spMat (lam 1 sl2W : StatedSp 2 K)) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 := by
  rw [Matrix.mulVec_single_one]
  ext j
  rw [Matrix.col_apply,
    show (spMat (lam 1 sl2W : StatedSp 2 K)) =
      pairMat (Sum.inl 1) (Sum.inr 1) (!![0, 1; 1, 0]) from by
      rw [coe_lam, coe_sl2W, CharTwo.neg_eq],
    pairMat_apply_of_ne' (by decide) (by decide), Matrix.one_apply]
  by_cases hj : j = Sum.inl 0
  · subst hj; simp
  · rw [if_neg hj, Pi.single_apply, if_neg hj]

omit [Finite K] in
theorem lam_sl2W_inv_fixes_e0 :
    (spMat (lam 1 sl2W : StatedSp 2 K)⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 := by
  have h : (spMat (lam 1 sl2W : StatedSp 2 K)⁻¹) *ᵥ
      ((spMat (lam 1 sl2W : StatedSp 2 K)) *ᵥ Pi.single (Sum.inl 0) 1) =
      (spMat (lam 1 sl2W : StatedSp 2 K)⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 := by
    rw [lam_sl2W_fixes_e0]
  rw [Matrix.mulVec_mulVec, ← TorusQS.spMat_mul, inv_mul_cancel] at h
  have h1 : (spMat (1 : StatedSp 2 K)) *ᵥ Pi.single (Sum.inl 0) 1 =
      Pi.single (Sum.inl 0) 1 := by
    change (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ _ = _
    rw [Matrix.one_mulVec]
  exact h.symm.trans h1

theorem pointImage_inf_ltri_eq_bot (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X) :
    pointImage X ⊓ CFSG.CGT.Timmesfeld75.ltri K = ⊥ := by
  classical
  rw [eq_bot_iff]
  rintro n ⟨hnN, hnL⟩
  obtain ⟨y, hyX, rfl⟩ := mem_pointImage.mp hnN
  have hyL := CFSG.CGT.Timmesfeld75.mem_ltri_entries.mp hnL
  have hy01 : blockMat y 0 1 = 0 := hyL.1
  have hy00 : blockMat y 0 0 = 1 := hyL.2
  have hy11 : blockMat y 1 1 = 1 := by
    have hd := blockMat_det y
    rw [Matrix.det_fin_two, hy00, hy01] at hd
    simpa using hd
  set n0 : StatedSp 2 K := lam 1 sl2W with hn0
  have hperml : IsLinePerm (Equiv.swap (Sum.inl 1) (Sum.inr 1)) (spMat n0) := by
    rw [hn0]
    exact isLinePerm_of_isPermSp (isPermSp_lam_sl2W 1)
  have hn0norm : n0 ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) :=
    mem_normalizer_torus_of_isLinePerm hperml
  have hn0e : (spMat n0) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
    rw [hn0]
    exact lam_sl2W_fixes_e0
  have hn0ie : (spMat n0⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = Pi.single (Sum.inl 0) 1 := by
    rw [hn0]
    exact lam_sl2W_inv_fixes_e0
  let X' : Subgroup (StatedSp 2 K) := X.map (MulAut.conj n0).toMonoidHom
  have hX' : IsRootFree X' := IsRootFree.map_conj hX hperml
  have hT' : torus 2 K ≤ X' := by
    intro t ht
    change t ∈ X.map (MulAut.conj n0).toMonoidHom
    rw [Subgroup.mem_map]
    refine ⟨n0⁻¹ * t * n0, hT ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn0norm) t).mp ht
    · simp [MulAut.conj_apply, mul_assoc]
  have hy'X : n0 * (y : StatedSp 2 K) * n0⁻¹ ∈ X' := by
    change _ ∈ X.map (MulAut.conj n0).toMonoidHom
    rw [Subgroup.mem_map]
    exact ⟨y, hyX, by simp [MulAut.conj_apply]⟩
  have hy'ps : n0 * (y : StatedSp 2 K) * n0⁻¹ ∈ pointStab (K := K) :=
    pointStab_conj y.2 hn0e hn0ie
  let y' : pointStab (K := K) := ⟨n0 * (y : StatedSp 2 K) * n0⁻¹, hy'ps⟩
  have hy'val : (y' : StatedSp 2 K) = n0 * (y : StatedSp 2 K) * n0⁻¹ := rfl
  have c00 : (spMat (n0 * (y : StatedSp 2 K) * n0⁻¹)) (Sum.inl 1) (Sum.inl 1) =
      (spMat (y : StatedSp 2 K)) (Sum.inr 1) (Sum.inr 1) := by
    simpa using (isPermSp_lam_sl2W (1 : Fin 2)).conj_apply (y : StatedSp 2 K)
      (Sum.inr 1) (Sum.inr 1)
  have c01 : (spMat (n0 * (y : StatedSp 2 K) * n0⁻¹)) (Sum.inl 1) (Sum.inr 1) =
      (spMat (y : StatedSp 2 K)) (Sum.inr 1) (Sum.inl 1) := by
    simpa using (isPermSp_lam_sl2W (1 : Fin 2)).conj_apply (y : StatedSp 2 K)
      (Sum.inr 1) (Sum.inl 1)
  have c10 : (spMat (n0 * (y : StatedSp 2 K) * n0⁻¹)) (Sum.inr 1) (Sum.inl 1) =
      (spMat (y : StatedSp 2 K)) (Sum.inl 1) (Sum.inr 1) := by
    simpa using (isPermSp_lam_sl2W (1 : Fin 2)).conj_apply (y : StatedSp 2 K)
      (Sum.inl 1) (Sum.inr 1)
  have c11 : (spMat (n0 * (y : StatedSp 2 K) * n0⁻¹)) (Sum.inr 1) (Sum.inr 1) =
      (spMat (y : StatedSp 2 K)) (Sum.inl 1) (Sum.inl 1) := by
    simpa using (isPermSp_lam_sl2W (1 : Fin 2)).conj_apply (y : StatedSp 2 K)
      (Sum.inl 1) (Sum.inl 1)
  have hy'U : blockElt y' ∈ CFSG.CGT.Timmesfeld75.utri K := by
    rw [CFSG.CGT.Timmesfeld75.mem_utri_entries]
    constructor
    · rw [coe_blockElt, blockMat_apply, hy'val, planeIdx_one, planeIdx_zero]
      rw [c10]
      simpa [blockMat_apply, planeIdx] using hy01
    · rw [coe_blockElt, blockMat_apply, hy'val, planeIdx_zero]
      rw [c00]
      simpa [blockMat_apply, planeIdx] using hy11
  have hone : blockElt y' = 1 := blockElt_eq_one_of_mem_utri hK hT' hX' hy'X hy'U
  have hb' : blockMat y' = 1 := congrArg Subtype.val hone
  have h00 : blockMat y 0 0 = 1 := by
    have h := congrFun (congrFun hb' 1) 1
    rw [blockMat_apply, hy'val, planeIdx_one] at h
    rw [c11] at h
    simpa [blockMat_apply, planeIdx] using h
  have h01 : blockMat y 0 1 = 0 := by
    have h := congrFun (congrFun hb' 1) 0
    rw [blockMat_apply, hy'val, planeIdx_one, planeIdx_zero] at h
    rw [c10] at h
    simpa [blockMat_apply, planeIdx] using h
  have h10 : blockMat y 1 0 = 0 := by
    have h := congrFun (congrFun hb' 0) 1
    rw [blockMat_apply, hy'val, planeIdx_zero, planeIdx_one] at h
    rw [c01] at h
    simpa [blockMat_apply, planeIdx] using h
  have h11 : blockMat y 1 1 = 1 := by
    have h := congrFun (congrFun hb' 0) 0
    rw [blockMat_apply, hy'val, planeIdx_zero] at h
    rw [c00] at h
    simpa [blockMat_apply, planeIdx] using h
  apply Subtype.ext
  change blockMat y = (1 : Matrix (Fin 2) (Fin 2) K)
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h10, h11]

omit [Finite K] in
theorem inv_fixesLine {y : StatedSp 2 K} {c : K} (h : FixesLine y c) :
    FixesLine y⁻¹ c⁻¹ := by
  have hc : c ≠ 0 := scalar_ne_zero_of_fixesLine h
  set M := spMat y with hM
  set N := spMat y⁻¹ with hN
  have hMN : M * N = 1 := by
    rw [hM, hN, ← TorusQS.spMat_mul, mul_inv_cancel]
    rfl
  have hNM : N * M = 1 := by
    rw [hM, hN, ← TorusQS.spMat_mul, inv_mul_cancel]
    rfl
  have hinj : Function.Injective (fun u => M *ᵥ u) := by
    intro u v huv
    have := congrArg (fun w => N *ᵥ w) huv
    simpa [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec] using this
  change N *ᵥ Pi.single (Sum.inl 0) 1 = c⁻¹ • Pi.single (Sum.inl 0) 1
  apply hinj
  change M *ᵥ (N *ᵥ Pi.single (Sum.inl 0) 1) = M *ᵥ (c⁻¹ • Pi.single (Sum.inl 0) 1)
  rw [Matrix.mulVec_mulVec, hMN, Matrix.one_mulVec, Matrix.mulVec_smul]
  rw [show M *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1 from h]
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

omit [Finite K] in
theorem pointStab_conj_smul {g n : StatedSp 2 K} {c : K} (hg : g ∈ pointStab (K := K))
    (hn : (spMat n) *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1) (hc : c ≠ 0)
    (hn' : (spMat n⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = c⁻¹ • Pi.single (Sum.inl 0) 1) :
    n * g * n⁻¹ ∈ pointStab (K := K) := by
  obtain ⟨d, hd⟩ := hg
  refine ⟨d, ?_⟩
  change (spMat (n * g * n⁻¹)) *ᵥ Pi.single (Sum.inl 0) 1 = d • Pi.single (Sum.inl 0) 1
  rw [TorusQS.spMat_mul, TorusQS.spMat_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hn', Matrix.mulVec_smul, hd, Matrix.mulVec_smul,
    Matrix.mulVec_smul, hn, smul_smul, smul_smul, mul_right_comm, inv_mul_cancel₀ hc,
    one_mul]

omit [Finite K] in
theorem blockElt_torus_mem {t : StatedSp 2 K} (ht : t ∈ torus 2 K) :
    blockElt ⟨t, torus_le_pointStab ht⟩ ∈ CFSG.CGT.Timmesfeld75.torus K := by
  obtain ⟨s, rfl⟩ := ht
  rw [show (⟨torusHom s, torus_le_pointStab (torusHom_mem_torus s)⟩ : pointStab (K := K)) =
      torusPoint s from Subtype.ext rfl]
  rw [blockElt_torusPoint, CFSG.CGT.Timmesfeld75.mem_torus_entries, coe_sl2Diag]
  constructor <;> simp

omit [Finite K] in
theorem torus_le_pointImage {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) :
    CFSG.CGT.Timmesfeld75.torus K ≤ pointImage X := by
  intro g hg
  rw [CFSG.CGT.Timmesfeld75.mem_torus_entries] at hg
  have hg01 : (g : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 := hg.1
  have hg10 : (g : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hg.2
  have h00 : (g : Matrix (Fin 2) (Fin 2) K) 0 0 ≠ 0 := by
    intro h
    have hd : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
    rw [Matrix.det_fin_two, h, hg01, hg10] at hd
    simp at hd
  let a : Kˣ := Units.mk0 ((g : Matrix (Fin 2) (Fin 2) K) 0 0) h00
  have hg11 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 = ((a⁻¹ : Kˣ) : K) := by
    have hd : (g : Matrix (Fin 2) (Fin 2) K).det = 1 := g.2
    rw [Matrix.det_fin_two, hg01, hg10] at hd
    have hprod : (g : Matrix (Fin 2) (Fin 2) K) 0 0 *
        (g : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by simpa using hd
    have h1 : (g : Matrix (Fin 2) (Fin 2) K) 1 1 =
        ((g : Matrix (Fin 2) (Fin 2) K) 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [h1]
    rfl
  refine mem_pointImage.mpr ⟨torusPoint ![1, a], hT (torusHom_mem_torus _), ?_⟩
  rw [blockElt_torusPoint]
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diag, sl2DiagElt, a, hg01, hg10, hg11, Units.val_mk0]

theorem pointImage_le_normalizer_torus (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X) :
    pointImage X ≤ Subgroup.normalizer
      (CFSG.CGT.Timmesfeld75.torus K : Set (Matrix.SpecialLinearGroup (Fin 2) K)) :=
  le_normalizer_torus_of_inf_eq_bot (le_trans (by norm_num) hK) (torus_le_pointImage hT)
    (pointImage_inf_utri_eq_bot hK hT hX) (pointImage_inf_ltri_eq_bot hK hT hX)

theorem conj_mem_torus_of_fixes (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {x : StatedSp 2 K} (hx : x ∈ X) {c : K}
    (hxc : (spMat x) *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1)
    {t : StatedSp 2 K} (ht : t ∈ torus 2 K) : x * t * x⁻¹ ∈ torus 2 K := by
  classical
  have hc : c ≠ 0 := scalar_ne_zero_of_fixesLine hxc
  have hxc' : (spMat x⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = c⁻¹ • Pi.single (Sum.inl 0) 1 :=
    inv_fixesLine hxc
  let xps : pointStab (K := K) := ⟨x, ⟨c, hxc⟩⟩
  let tps : pointStab (K := K) := ⟨t, torus_le_pointStab ht⟩
  have hsX : x * t * x⁻¹ ∈ X := X.mul_mem (X.mul_mem hx (hT ht)) (X.inv_mem hx)
  have hsps : x * t * x⁻¹ ∈ pointStab (K := K) := pointStab_conj_smul tps.2 hxc hc hxc'
  let s : pointStab (K := K) := ⟨x * t * x⁻¹, hsps⟩
  have hbS : blockElt s ∈ CFSG.CGT.Timmesfeld75.torus K := by
    have hN : blockElt xps ∈ pointImage X :=
      mem_pointImage.mpr ⟨xps, hx, rfl⟩
    have hN' := pointImage_le_normalizer_torus hK hT hX hN
    have htT : blockElt tps ∈ CFSG.CGT.Timmesfeld75.torus K := blockElt_torus_mem ht
    have heq : blockElt s = blockElt xps * blockElt tps * (blockElt xps)⁻¹ := by
      rw [show s = xps * tps * xps⁻¹ from Subtype.ext rfl]
      rw [map_mul, map_mul, map_inv]
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp hN' (blockElt tps)).mp htT
  have hbS' := CFSG.CGT.Timmesfeld75.mem_torus_entries.mp hbS
  have hb01 : blockMat s 0 1 = 0 := hbS'.1
  have hb10 : blockMat s 1 0 = 0 := hbS'.2
  have hprod : blockMat s 0 0 * blockMat s 1 1 = 1 := by
    have hd := blockMat_det s
    rw [Matrix.det_fin_two, hb01, hb10] at hd
    simpa using hd
  have h00 : blockMat s 0 0 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact zero_ne_one hprod
  let p : Kˣ := Units.mk0 (blockMat s 0 0) h00
  have h11 : blockMat s 1 1 = ((p⁻¹ : Kˣ) : K) := by
    have h1 : blockMat s 1 1 = (blockMat s 0 0)⁻¹ := eq_inv_of_mul_eq_one_right hprod
    rw [h1]
    rfl
  have hbm : blockMat s = (sl2Diag p : Matrix (Fin 2) (Fin 2) K) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Diag, sl2DiagElt, p, hb01, hb10, h11]
  let t' : pointStab (K := K) := torusPoint ![chi s, p]
  have ht'T : (t' : StatedSp 2 K) ∈ torus 2 K := torusHom_mem_torus _
  have hchi_t' : chi t' = chi s := by
    rw [show chi t' = ![chi s, p] 0 from chi_torusPoint _]
    simp
  have hblock_t' : blockElt t' = sl2Diag p := by
    rw [blockElt_torusPoint]
    simp
  have hblock_s : blockElt s = sl2Diag p := by
    apply Subtype.ext
    exact hbm
  have hchi_s : chi s = chi t' := hchi_t'.symm
  have hb_eq : blockElt s = blockElt t' := by
    rw [hblock_s, hblock_t']
  let u : pointStab (K := K) := s * t'⁻¹
  have hchi_u : chi u = 1 := by
    simp only [u, map_mul, map_inv]
    rw [← hchi_s]
    exact mul_inv_cancel (chi s)
  have hblock_u : blockElt u = 1 := by
    simp only [u, map_mul, map_inv]
    rw [← hb_eq]
    exact mul_inv_cancel (blockElt s)
  have huQ : IsPointUnip (u : StatedSp 2 K) :=
    isPointUnip_of_chi_eq_one_of_blockElt_eq_one hchi_u hblock_u
  have huX : (u : StatedSp 2 K) ∈ X := by
    simp only [u, Subgroup.coe_mul, Subgroup.coe_inv]
    exact X.mul_mem hsX (X.inv_mem (hT ht'T))
  have hu1 : (u : StatedSp 2 K) = 1 := eq_one_of_isPointUnip hK hT hX huX huQ
  have hst : (s : StatedSp 2 K) = (t' : StatedSp 2 K) := by
    have h : (s : StatedSp 2 K) * ((t' : StatedSp 2 K))⁻¹ = 1 := by
      simpa only [u, Subgroup.coe_mul, Subgroup.coe_inv] using hu1
    exact eq_of_mul_inv_eq_one h
  have hs_val : (s : StatedSp 2 K) = x * t * x⁻¹ := rfl
  rw [← hs_val, hst]
  exact ht'T

theorem mem_normalizer_torus_of_fixes_inl_zero (hK : 8 ≤ Nat.card K)
    {X : Subgroup (StatedSp 2 K)} (hT : torus 2 K ≤ X) (hX : IsRootFree X)
    {x : StatedSp 2 K} (hx : x ∈ X) {c : K}
    (hxc : (spMat x) *ᵥ Pi.single (Sum.inl 0) 1 = c • Pi.single (Sum.inl 0) 1) :
    x ∈ Subgroup.normalizer (torus 2 K : Set (StatedSp 2 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · intro ht
    exact conj_mem_torus_of_fixes hK hT hX hx hxc ht
  · intro ht
    have hxc' : (spMat x⁻¹) *ᵥ Pi.single (Sum.inl 0) 1 = c⁻¹ • Pi.single (Sum.inl 0) 1 :=
      inv_fixesLine hxc
    have h : x⁻¹ * (x * t * x⁻¹) * (x⁻¹)⁻¹ ∈ torus 2 K :=
      conj_mem_torus_of_fixes hK hT hX (X.inv_mem hx) hxc' ht
    simpa [mul_assoc] using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Sp4TorusRed

end
