module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08SuGen
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.ClassicalGroups.Unitary.Transport
public import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
public import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open
open CFSG.LieType.BorelTits (unitaryInvolution)
open CFSG.SectionRank.OddCover (diagHom coe_diagHom det_diagHom)
open CFSG.RankThree.Classical (permGL)

open scoped Matrix commutatorElement

variable {F : Type} [Field F] [Finite F]

@[expose] def ggQ2s08r6Stab (F : Type) [Field F] (w : Fin 6) :
    Subgroup ↥(LargeEvenSUGroup (Fin 6) F 2) where
  carrier := {g | ∀ i, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w =
    if i = w then 1 else 0}
  one_mem' := by
    intro i
    change (1 : Matrix (Fin 6) (Fin 6) F) i w = if i = w then 1 else 0
    rw [Matrix.one_apply]
  mul_mem' := by
    intro g h hg hh i
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single w]
    · rw [hh w, if_pos rfl, mul_one]
      exact hg i
    · intro k _ hk
      rw [hh k, if_neg hk, mul_zero]
    · simp
  inv_mem' := by
    intro g hg
    have hcol : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
        (Pi.single w (1 : F)) = Pi.single w 1 := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, hg i, Pi.single_apply]
    have hprod : (((g⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) * ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
      have hGL : ((g⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) *
          (g : GL (Fin 6) F) = 1 := inv_mul_cancel _
      simpa using congrArg (fun u : GL (Fin 6) F => (u : Matrix (Fin 6) (Fin 6) F)) hGL
    have hinv : (((g⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) :
        Matrix (Fin 6) (Fin 6) F) *ᵥ (Pi.single w (1 : F)) = Pi.single w 1 := by
      calc
        (((g⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) :
              Matrix (Fin 6) (Fin 6) F) *ᵥ (Pi.single w (1 : F))
            = (((g⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) :
                Matrix (Fin 6) (Fin 6) F) *ᵥ
                (((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
                  (Pi.single w (1 : F))) := by rw [hcol]
        _ = ((((g⁻¹ : ↥(LargeEvenSUGroup (Fin 6) F 2)) : GL (Fin 6) F) :
                Matrix (Fin 6) (Fin 6) F) *
              ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) *ᵥ
                (Pi.single w (1 : F)) := by rw [← Matrix.mulVec_mulVec]
        _ = Pi.single w 1 := by rw [hprod, Matrix.one_mulVec]
    intro i
    have := congrFun hinv i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    exact this

private theorem ggQ2s08r6_stab_col_iff {w : Fin 6}
    {g : ↥(LargeEvenSUGroup (Fin 6) F 2)} :
    (∀ i, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w = if i = w then 1 else 0) ↔
      ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ (Pi.single w (1 : F)) =
        Pi.single w 1 := by
  constructor
  · intro h
    funext i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, h i, Pi.single_apply]
  · intro h i
    have := congrFun h i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    exact this

private theorem ggQ2s08r6_su_eq [Fact (Nat.Prime 2)] [CharP F 2] (hF : Nat.card F = 4) :
    CFSG.LieType.Universal.Unitary.SUid
        (unitaryInvolution F 2 1) 6 = LargeEvenSUGroup (Fin 6) F 2 := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc 6]
  rfl

private abbrev ggQ2s08r6StabSUid (σ : F ≃+* F) (w : Fin 6) :
    Subgroup ↥(CFSG.LieType.Universal.Unitary.SUid σ 6) :=
  MulAction.stabilizer (CFSG.LieType.Universal.Unitary.SUid σ 6)
    (Pi.single w (1 : F) : Fin 6 → F)

private theorem ggQ2s08r6Stab_eq_stabSUid_map
    (σ : F ≃+* F) (hSU : CFSG.LieType.Universal.Unitary.SUid σ 6 =
      LargeEvenSUGroup (Fin 6) F 2) (w : Fin 6) :
    ggQ2s08r6Stab F w =
      (ggQ2s08r6StabSUid (F := F) σ w).map
        (MulEquiv.subgroupCongr hSU).toMonoidHom := by
  classical
  ext g
  constructor
  · intro hg
    refine Subgroup.mem_map.mpr ⟨(MulEquiv.subgroupCongr hSU).symm g, ?_, ?_⟩
    · rw [ggQ2s08r6StabSUid, MulAction.mem_stabilizer_iff]
      have hcol : ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
          (Pi.single w (1 : F)) = Pi.single w 1 :=
        (ggQ2s08r6_stab_col_iff).mp hg
      change ((((MulEquiv.subgroupCongr hSU).symm g :
        ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)) : GL (Fin 6) F) :
          Matrix (Fin 6) (Fin 6) F) *ᵥ (Pi.single w (1 : F)) = Pi.single w 1
      exact hcol
    · exact MulEquiv.apply_symm_apply (MulEquiv.subgroupCongr hSU) g
  · rintro ⟨k, hk, rfl⟩
    have hk' : ((k : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
        (Pi.single w (1 : F)) = Pi.single w 1 := by
      have hk2 := (MulAction.mem_stabilizer_iff).mp hk
      rw [CFSG.ClassicalGroups.Unitary.smul_def] at hk2
      exact hk2
    have hcol : ∀ i, ((k : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w =
        if i = w then 1 else 0 := by
      intro i
      have := congrFun hk' i
      rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    intro i
    exact hcol i

private theorem ggQ2s08r6_suid_stab_row (σ : F ≃+* F) (w : Fin 6)
    {g : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)}
    (hg : g ∈ ggQ2s08r6StabSUid (F := F) σ w) (i : Fin 6) :
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) w i = if i = w then 1 else 0 := by
  have hcol : ∀ k, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) k w =
      if k = w then 1 else 0 := by
    intro k
    have h := congrFun (MulAction.mem_stabilizer_iff.mp hg) k
    rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_single_one,
      Matrix.col_apply, Pi.single_apply] at h
    exact h
  by_cases hi : i = w
  · rw [hi]
    exact hcol w
  · have hiso : CFSG.ClassicalGroups.Unitary.herm σ
        (g • (Pi.single w (1 : F))) (g • (Pi.single i (1 : F))) =
        CFSG.ClassicalGroups.Unitary.herm σ (Pi.single w (1 : F))
          (Pi.single i (1 : F)) :=
      CFSG.ClassicalGroups.Unitary.herm_smul_smul σ g _ _
    rw [MulAction.mem_stabilizer_iff.mp hg] at hiso
    rw [CFSG.ClassicalGroups.Unitary.herm_single_left,
      CFSG.ClassicalGroups.Unitary.herm_single_left] at hiso
    simp only [map_one, one_mul, Pi.single_eq_of_ne (Ne.symm hi)] at hiso
    rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_single_one,
      Matrix.col_apply] at hiso
    rw [hiso, if_neg hi]

theorem ggQ2s08r6_stab_row (hF : Nat.card F = 4) {w : Fin 6}
    {g : ↥(LargeEvenSUGroup (Fin 6) F 2)} (hg : g ∈ ggQ2s08r6Stab F w) (i : Fin 6) :
    ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) w i = if i = w then 1 else 0 := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP F 2 := hU.charP
  let σ : F ≃+* F := unitaryInvolution F 2 1
  have hSU := ggQ2s08r6_su_eq (F := F) hF
  have hmap := ggQ2s08r6Stab_eq_stabSUid_map (F := F) σ hSU w
  have hg' : g ∈ (ggQ2s08r6StabSUid (F := F) σ w).map
      (MulEquiv.subgroupCongr hSU).toMonoidHom := hmap ▸ hg
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg'
  have hrow := ggQ2s08r6_suid_stab_row (F := F) σ w hk i
  rw [← hkg]
  exact hrow

theorem ggQ2s08r6_stab_commute (hF : Nat.card F = 4) {w : Fin 6}
    {g : ↥(LargeEvenSUGroup (Fin 6) F 2)} (hg : g ∈ ggQ2s08r6Stab F w) {t : Fin 6 → Fˣ}
    (ht : ∀ i j, i ≠ w → j ≠ w → t i = t j) :
    (g : GL (Fin 6) F) * diagHom 6 t = diagHom 6 t * g := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, coe_diagHom, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  by_cases hi : i = w
  · rw [hi]
    rw [ggQ2s08r6_stab_row hF hg j]
    by_cases hj : j = w
    · simp [hj]
    · simp [hj]
  · by_cases hj : j = w
    · rw [hj, hg i, if_neg hi]
      simp
    · rw [ht i j hi hj]
      ring

theorem ggQ2s08r6_permGL_mem_stab {σ : Equiv.Perm (Fin 6)} {w : Fin 6} (hσ : σ w = w)
    (g : ↥(LargeEvenSUGroup (Fin 6) F 2)) (hg : (g : GL (Fin 6) F) = permGL σ) :
    g ∈ ggQ2s08r6Stab F w := by
  change ∀ i, ((g : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i w =
    if i = w then 1 else 0
  rw [hg]
  have hcol : ((permGL σ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
      (Pi.single w (1 : F)) = Pi.single w 1 := by
    funext i
    rw [CFSG.RankThree.Classical.permGL_mulVec]
    simp only [Function.comp_apply, Pi.single_apply]
    by_cases hi : i = w
    · rw [if_pos hi]
      have h : σ⁻¹ i = w := by
        rw [hi, Equiv.Perm.inv_def, ← hσ, Equiv.symm_apply_apply, hσ]
      rw [if_pos h]
    · rw [if_neg hi]
      have hne : σ⁻¹ i ≠ w := by
        intro h
        apply hi
        rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq] at h
        rwa [hσ] at h
      rw [if_neg hne]
  intro i
  have := congrFun hcol i
  rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this

private def ggQ2s08r6_ee : Fin 1 ⊕ Fin 5 ≃ Fin 6 where
  toFun x := Sum.elim (fun _ => 0) (fun j => j.succ) x
  invFun i := Fin.cases (Sum.inl 0) (fun j => Sum.inr j) i
  left_inv x := by
    rcases x with i | j
    · have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      rfl
    · rfl
  right_inv i := by
    induction i using Fin.cases with
    | zero => rfl
    | succ j => rfl

@[simp] private theorem ggQ2s08r6_ee_inl (i : Fin 1) :
    ggQ2s08r6_ee (Sum.inl i) = 0 := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rfl

@[simp] private theorem ggQ2s08r6_ee_inr (j : Fin 5) :
    ggQ2s08r6_ee (Sum.inr j) = j.succ := rfl

private noncomputable def ggQ2s08r6_blockMat0 (X : Matrix (Fin 5) (Fin 5) F) :
    Matrix (Fin 6) (Fin 6) F :=
  Matrix.reindexAlgEquiv F F ggQ2s08r6_ee (Matrix.fromBlocks 1 0 0 X)

private theorem ggQ2s08r6_blockMat0_apply (X : Matrix (Fin 5) (Fin 5) F)
    (p q : Fin 1 ⊕ Fin 5) :
    ggQ2s08r6_blockMat0 X (ggQ2s08r6_ee p) (ggQ2s08r6_ee q) =
      Matrix.fromBlocks 1 0 0 X p q := by
  rw [ggQ2s08r6_blockMat0, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  simp

private theorem ggQ2s08r6_blockMat0_zero_zero (X : Matrix (Fin 5) (Fin 5) F) :
    ggQ2s08r6_blockMat0 X 0 0 = 1 := by
  have h := ggQ2s08r6_blockMat0_apply (F := F) X (Sum.inl 0) (Sum.inl 0)
  simpa using h

private theorem ggQ2s08r6_blockMat0_zero_succ (X : Matrix (Fin 5) (Fin 5) F)
    (j : Fin 5) : ggQ2s08r6_blockMat0 X 0 j.succ = 0 := by
  have h := ggQ2s08r6_blockMat0_apply (F := F) X (Sum.inl 0) (Sum.inr j)
  simpa using h

private theorem ggQ2s08r6_blockMat0_succ_zero (X : Matrix (Fin 5) (Fin 5) F)
    (i : Fin 5) : ggQ2s08r6_blockMat0 X i.succ 0 = 0 := by
  have h := ggQ2s08r6_blockMat0_apply (F := F) X (Sum.inr i) (Sum.inl 0)
  simpa using h

private theorem ggQ2s08r6_blockMat0_succ_succ (X : Matrix (Fin 5) (Fin 5) F)
    (i j : Fin 5) : ggQ2s08r6_blockMat0 X i.succ j.succ = X i j := by
  have h := ggQ2s08r6_blockMat0_apply (F := F) X (Sum.inr i) (Sum.inr j)
  simpa using h

private theorem ggQ2s08r6_blockMat0_det (X : Matrix (Fin 5) (Fin 5) F) :
    (ggQ2s08r6_blockMat0 X).det = X.det := by
  rw [ggQ2s08r6_blockMat0, Matrix.det_reindexAlgEquiv,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

private theorem ggQ2s08r6_blockMat0_mul (X Y : Matrix (Fin 5) (Fin 5) F) :
    ggQ2s08r6_blockMat0 (X * Y) =
      ggQ2s08r6_blockMat0 X * ggQ2s08r6_blockMat0 Y := by
  rw [ggQ2s08r6_blockMat0, ggQ2s08r6_blockMat0, ggQ2s08r6_blockMat0,
    ← Matrix.reindexAlgEquiv_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

private theorem ggQ2s08r6_blockMat0_one :
    ggQ2s08r6_blockMat0 (1 : Matrix (Fin 5) (Fin 5) F) = 1 := by
  rw [ggQ2s08r6_blockMat0, Matrix.fromBlocks_one]
  exact map_one _

private theorem ggQ2s08r6_blockMat0_map (f : F →+* F)
    (X : Matrix (Fin 5) (Fin 5) F) :
    (ggQ2s08r6_blockMat0 X).map f = ggQ2s08r6_blockMat0 (X.map f) := by
  ext i j
  rw [Matrix.map_apply, ggQ2s08r6_blockMat0, ggQ2s08r6_blockMat0,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.reindex_apply]
  change f (Matrix.fromBlocks 1 0 0 X (ggQ2s08r6_ee.symm i)
    (ggQ2s08r6_ee.symm j)) =
    (Matrix.reindexAlgEquiv F F ggQ2s08r6_ee)
      (Matrix.fromBlocks 1 0 0 (X.map f)) i j
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  change (Matrix.fromBlocks 1 0 0 X).map f (ggQ2s08r6_ee.symm i)
      (ggQ2s08r6_ee.symm j) =
    Matrix.fromBlocks 1 0 0 (X.map f) (ggQ2s08r6_ee.symm i)
      (ggQ2s08r6_ee.symm j)
  rw [Matrix.fromBlocks_map]
  simp

private theorem ggQ2s08r6_blockMat0_transpose (X : Matrix (Fin 5) (Fin 5) F) :
    (ggQ2s08r6_blockMat0 X)ᵀ = ggQ2s08r6_blockMat0 Xᵀ := by
  rw [ggQ2s08r6_blockMat0, ggQ2s08r6_blockMat0, Matrix.coe_reindexAlgEquiv,
    Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  congr 1
  simp

private noncomputable def ggQ2s08r6_blockGL (X : GL (Fin 5) F) : GL (Fin 6) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (ggQ2s08r6_blockMat0 (X : Matrix (Fin 5) (Fin 5) F))
    (by rw [ggQ2s08r6_blockMat0_det]; exact Matrix.GeneralLinearGroup.det_ne_zero X)

private theorem ggQ2s08r6_val_blockGL (X : GL (Fin 5) F) :
    ((ggQ2s08r6_blockGL X : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ggQ2s08r6_blockMat0 (X : Matrix (Fin 5) (Fin 5) F) :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

private theorem ggQ2s08r6_blockGL_mem_SUid (σ : F ≃+* F) {X : GL (Fin 5) F}
    (hX : X ∈ CFSG.LieType.Universal.Unitary.SUid σ 5) :
    ggQ2s08r6_blockGL X ∈ CFSG.LieType.Universal.Unitary.SUid σ 6 := by
  rw [CFSG.LieType.Universal.Unitary.mem_SUid] at hX ⊢
  refine ⟨?_, ?_⟩
  · rw [ggQ2s08r6_val_blockGL, ggQ2s08r6_blockMat0_det, hX.1]
  · rw [ggQ2s08r6_val_blockGL]
    calc
      CFSG.LieType.Universal.Unitary.conjTr σ
            (ggQ2s08r6_blockMat0 (X : Matrix (Fin 5) (Fin 5) F)) *
          ggQ2s08r6_blockMat0 (X : Matrix (Fin 5) (Fin 5) F)
          = (ggQ2s08r6_blockMat0
              ((X : Matrix (Fin 5) (Fin 5) F).map σ))ᵀ *
              ggQ2s08r6_blockMat0 (X : Matrix (Fin 5) (Fin 5) F) := by
              rw [CFSG.LieType.Universal.Unitary.conjTr]
              congr 1
              simpa using ggQ2s08r6_blockMat0_map (f := σ.toRingHom)
                (X := (X : Matrix (Fin 5) (Fin 5) F))
      _ = ggQ2s08r6_blockMat0
            ((X : Matrix (Fin 5) (Fin 5) F).map σ)ᵀ *
              ggQ2s08r6_blockMat0 (X : Matrix (Fin 5) (Fin 5) F) := by
              rw [ggQ2s08r6_blockMat0_transpose]
      _ = ggQ2s08r6_blockMat0
            (((X : Matrix (Fin 5) (Fin 5) F).map σ)ᵀ *
              (X : Matrix (Fin 5) (Fin 5) F)) := by
              rw [ggQ2s08r6_blockMat0_mul]
      _ = ggQ2s08r6_blockMat0 1 := by
              rw [show ((X : Matrix (Fin 5) (Fin 5) F).map σ)ᵀ *
                  (X : Matrix (Fin 5) (Fin 5) F) =
                CFSG.LieType.Universal.Unitary.conjTr σ
                    (X : Matrix (Fin 5) (Fin 5) F) *
                  (X : Matrix (Fin 5) (Fin 5) F) from rfl, hX.2]
      _ = 1 := ggQ2s08r6_blockMat0_one

private theorem ggQ2s08r6_blockMat0_fixes_e0 (X : Matrix (Fin 5) (Fin 5) F) :
    ggQ2s08r6_blockMat0 X *ᵥ (Pi.single (0 : Fin 6) (1 : F)) = Pi.single 0 1 := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  induction i using Fin.cases with
  | zero => rw [ggQ2s08r6_blockMat0_zero_zero]; simp
  | succ j => rw [ggQ2s08r6_blockMat0_succ_zero]; simp

private theorem ggQ2s08r6_blkMat_blockMat0 (X : Matrix (Fin 5) (Fin 5) F) :
    CFSG.ClassicalGroups.Unitary.blkMat (ggQ2s08r6_blockMat0 X) = X := by
  ext i j
  rw [CFSG.ClassicalGroups.Unitary.blkMat, Matrix.submatrix_apply,
    ggQ2s08r6_blockMat0_succ_succ]

private theorem ggQ2s08r6_blockMat0_blkMat (σ : F ≃+* F)
    {M : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)}
    (hM : M ∈ ggQ2s08r6StabSUid (F := F) σ 0) :
    ggQ2s08r6_blockMat0 (CFSG.ClassicalGroups.Unitary.blkMat
      ((M : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) =
      ((M : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
  have hrow := ggQ2s08r6_suid_stab_row (F := F) σ 0 hM
  have hcol : ∀ i, ((M : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) i 0 =
      if i = 0 then 1 else 0 := by
    intro i
    have h := congrFun (MulAction.mem_stabilizer_iff.mp hM) i
    rw [CFSG.ClassicalGroups.Unitary.smul_def, Matrix.mulVec_single_one,
      Matrix.col_apply, Pi.single_apply] at h
    exact h
  ext i j
  induction i using Fin.cases with
  | zero =>
      induction j using Fin.cases with
      | zero => rw [ggQ2s08r6_blockMat0_zero_zero, hcol 0]; simp
      | succ j => rw [ggQ2s08r6_blockMat0_zero_succ, hrow j.succ]; simp
  | succ i =>
      induction j using Fin.cases with
      | zero => rw [ggQ2s08r6_blockMat0_succ_zero, hcol i.succ]; simp
      | succ j => rw [ggQ2s08r6_blockMat0_succ_succ,
          CFSG.ClassicalGroups.Unitary.blkMat, Matrix.submatrix_apply]

private noncomputable def ggQ2s08r6_blockHom (σ : F ≃+* F) :
    ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) →*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ 6) where
  toFun X := ⟨ggQ2s08r6_blockGL (X : GL (Fin 5) F),
    ggQ2s08r6_blockGL_mem_SUid σ X.2⟩
  map_one' := by
    apply Subtype.ext
    change (ggQ2s08r6_blockGL (1 : GL (Fin 5) F) : GL (Fin 6) F) = 1
    apply Units.ext
    rw [ggQ2s08r6_val_blockGL]
    exact ggQ2s08r6_blockMat0_one
  map_mul' X Y := by
    apply Subtype.ext
    change (ggQ2s08r6_blockGL ((X : GL (Fin 5) F) * (Y : GL (Fin 5) F)) :
      GL (Fin 6) F) = ggQ2s08r6_blockGL (X : GL (Fin 5) F) *
        ggQ2s08r6_blockGL (Y : GL (Fin 5) F)
    apply Units.ext
    rw [Units.val_mul]
    rw [ggQ2s08r6_val_blockGL, ggQ2s08r6_val_blockGL, ggQ2s08r6_val_blockGL]
    rw [show ((((X : GL (Fin 5) F)) * (Y : GL (Fin 5) F) : GL (Fin 5) F) :
        Matrix (Fin 5) (Fin 5) F) =
      ((X : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) *
        ((Y : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) from rfl,
      ggQ2s08r6_blockMat0_mul]

private noncomputable def ggQ2s08r6_blockHomStab (σ : F ≃+* F) :
    ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) →*
      ↥(ggQ2s08r6StabSUid (F := F) σ 0) where
  toFun X := ⟨ggQ2s08r6_blockHom σ X, by
    rw [ggQ2s08r6StabSUid, MulAction.mem_stabilizer_iff]
    rw [CFSG.ClassicalGroups.Unitary.smul_def]
    rw [show ((ggQ2s08r6_blockHom σ X :
        ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)) : GL (Fin 6) F) =
      ggQ2s08r6_blockGL (X : GL (Fin 5) F) from rfl, ggQ2s08r6_val_blockGL]
    exact ggQ2s08r6_blockMat0_fixes_e0 _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' X Y := Subtype.ext (map_mul _ X Y)

private noncomputable def ggQ2s08r6_stab0Equiv (σ : F ≃+* F) :
    ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) ≃*
      ↥(ggQ2s08r6StabSUid (F := F) σ 0) where
  toFun := ggQ2s08r6_blockHomStab σ
  invFun M := CFSG.ClassicalGroups.Unitary.blk (σ := σ) M.1
    (MulAction.mem_stabilizer_iff.mp M.2)
  left_inv X := by
    apply Subtype.ext
    apply Units.ext
    change (CFSG.ClassicalGroups.Unitary.blkMat
      ((((ggQ2s08r6_blockHomStab σ) X : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)) :
        GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) =
      ((X : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)
    simp only [ggQ2s08r6_blockHomStab, ggQ2s08r6_blockHom,
      ggQ2s08r6_val_blockGL, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact ggQ2s08r6_blkMat_blockMat0 _
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change ggQ2s08r6_blockMat0 (CFSG.ClassicalGroups.Unitary.blkMat
      ((M : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) =
      ((M : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)
    exact ggQ2s08r6_blockMat0_blkMat (σ := σ) (M := M) M.2
  map_mul' X Y := map_mul (ggQ2s08r6_blockHomStab σ) X Y

private theorem ggQ2s08r6_stabSUid_conj (σ : F ≃+* F)
    (P : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)) {v w : Fin 6}
    (hP : P • (Pi.single v (1 : F) : Fin 6 → F) =
      (Pi.single w (1 : F) : Fin 6 → F)) :
    (ggQ2s08r6StabSUid (F := F) σ v).map (MulAut.conj P).toMonoidHom =
      ggQ2s08r6StabSUid (F := F) σ w := by
  have hPinv : P⁻¹ • (Pi.single w (1 : F) : Fin 6 → F) =
      (Pi.single v (1 : F) : Fin 6 → F) := by
    have := congrArg (fun z => P⁻¹ • z) hP
    simpa [mul_smul] using this.symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [ggQ2s08r6StabSUid, MulAction.mem_stabilizer_iff] at hy ⊢
    calc
      (P * y * P⁻¹) • (Pi.single w (1 : F) : Fin 6 → F)
          = P • (y • (P⁻¹ • (Pi.single w (1 : F) : Fin 6 → F))) := by simp [mul_smul]
      _ = P • (y • (Pi.single v (1 : F) : Fin 6 → F)) := by rw [hPinv]
      _ = P • (Pi.single v (1 : F) : Fin 6 → F) := by rw [hy]
      _ = (Pi.single w (1 : F) : Fin 6 → F) := hP
  · intro hx
    refine ⟨P⁻¹ * x * P, ?_, ?_⟩
    · simp only [ggQ2s08r6StabSUid, MulAction.mem_stabilizer_iff] at hx ⊢
      calc
        (P⁻¹ * x * P) • (Pi.single v (1 : F) : Fin 6 → F)
            = P⁻¹ • (x • (P • (Pi.single v (1 : F) : Fin 6 → F))) := by simp [mul_smul]
        _ = P⁻¹ • (x • (Pi.single w (1 : F) : Fin 6 → F)) := by rw [hP]
        _ = P⁻¹ • (Pi.single w (1 : F) : Fin 6 → F) := by rw [hx]
        _ = (Pi.single v (1 : F) : Fin 6 → F) := hPinv
    · change P * (P⁻¹ * x * P) * P⁻¹ = x
      group

private noncomputable def ggQ2s08r6_stabConjEquiv (σ : F ≃+* F)
    (P : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)) {v w : Fin 6}
    (hP : P • (Pi.single v (1 : F) : Fin 6 → F) =
      (Pi.single w (1 : F) : Fin 6 → F)) :
    ↥(ggQ2s08r6StabSUid (F := F) σ v) ≃*
      ↥(ggQ2s08r6StabSUid (F := F) σ w) :=
  (MulEquiv.subgroupMap (MulAut.conj P) (ggQ2s08r6StabSUid (F := F) σ v)).trans
    (MulEquiv.subgroupCongr (ggQ2s08r6_stabSUid_conj σ P hP))

private noncomputable def ggQ2s08r6_stabEquiv (σ : F ≃+* F)
    (hSU : CFSG.LieType.Universal.Unitary.SUid σ 6 =
      LargeEvenSUGroup (Fin 6) F 2) (w : Fin 6) :
    ↥(ggQ2s08r6Stab F w) ≃*
      ↥(ggQ2s08r6StabSUid (F := F) σ w) :=
  (MulEquiv.subgroupCongr (ggQ2s08r6Stab_eq_stabSUid_map σ hSU w)).trans
    (MulEquiv.subgroupMap (MulEquiv.subgroupCongr hSU)
      (ggQ2s08r6StabSUid (F := F) σ w)).symm

private theorem ggQ2s08r6_permGL_mem_SUid
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (σ : F ≃+* F)
    (hSU : CFSG.LieType.Universal.Unitary.SUid σ 6 = StatedSU 6 (2 ^ 1) F)
    (π : Equiv.Perm (Fin 6)) :
    permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ 6 := by
  rw [hSU]
  exact CFSG.StandardType.LineU.permGL_mem_unitarySU hU π

private theorem ggQ2s08r6_permGL_smul_single {σ : F ≃+* F}
    (hP : ∀ π : Equiv.Perm (Fin 6),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ 6)
    (π : Equiv.Perm (Fin 6)) (i : Fin 6) :
    (⟨permGL π, hP π⟩ : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6)) •
        (Pi.single i (1 : F) : Fin 6 → F) =
      (Pi.single (π i) (1 : F) : Fin 6 → F) := by
  funext k
  rw [CFSG.ClassicalGroups.Unitary.smul_def,
    CFSG.RankThree.Classical.permGL_mulVec]
  simp only [Function.comp_apply, Pi.single_apply]
  by_cases hk : k = π i
  · rw [if_pos hk]
    have h : π⁻¹ k = i := by
      rw [hk, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
    rw [if_pos h]
  · rw [if_neg hk]
    have h : π⁻¹ k ≠ i := by
      intro h
      apply hk
      calc k = π (π⁻¹ k) := (Equiv.apply_symm_apply π k).symm
        _ = π i := by rw [h]
    rw [if_neg h]

private theorem ggQ2s08r6_exists_perm (w w' : Fin 6) (h : w ≠ w') :
    ∃ π : Equiv.Perm (Fin 6), π 0 = w ∧ π 5 = w' := by
  let f : Fin 2 → Fin 6 := ![0, 5]
  let g : Fin 2 → Fin 6 := ![w, w']
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g, h]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨π, ?_, ?_⟩
  · simpa [f, g] using hπ 0
  · simpa [f, g] using hπ 1

private noncomputable def ggQ2s08r6_stabWEquiv (σ : F ≃+* F)
    (hP : ∀ π : Equiv.Perm (Fin 6),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ 6) (w : Fin 6) :
    ↥(ggQ2s08r6StabSUid (F := F) σ w) ≃*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) := by
  classical
  let π : Equiv.Perm (Fin 6) := Equiv.swap 0 w
  have hπ0 : π 0 = w := Equiv.swap_apply_left 0 w
  let P : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6) := ⟨permGL π, hP π⟩
  have hP0 : P • (Pi.single 0 (1 : F) : Fin 6 → F) =
      (Pi.single w (1 : F) : Fin 6 → F) := by
    rw [ggQ2s08r6_permGL_smul_single hP π 0, hπ0]
  exact (ggQ2s08r6_stabConjEquiv σ P hP0).symm.trans
    (ggQ2s08r6_stab0Equiv σ).symm

private theorem ggQ2s08r6_stabSUid_sup
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (σ : F ≃+* F) (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ)
    (hP : ∀ π : Equiv.Perm (Fin 6),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ 6)
    {w w' : Fin 6} (h : w ≠ w') :
    ggQ2s08r6StabSUid (F := F) σ w ⊔
      ggQ2s08r6StabSUid (F := F) σ w' = ⊤ := by
  obtain ⟨π, hπ0, hπ5⟩ := ggQ2s08r6_exists_perm w w' h
  let P : ↥(CFSG.LieType.Universal.Unitary.SUid σ 6) := ⟨permGL π, hP π⟩
  have hP0 : P • (Pi.single 0 (1 : F) : Fin 6 → F) =
      (Pi.single w (1 : F) : Fin 6 → F) := by
    rw [ggQ2s08r6_permGL_smul_single hP π 0, hπ0]
  have hP5 : P • (Pi.single 5 (1 : F) : Fin 6 → F) =
      (Pi.single w' (1 : F) : Fin 6 → F) := by
    rw [ggQ2s08r6_permGL_smul_single hP π 5, hπ5]
  have hgen : ggQ2s08r6StabSUid (F := F) σ 0 ⊔
      ggQ2s08r6StabSUid (F := F) σ 5 = ⊤ := by
    have h := ggQ2s08_su_stab_generate (K := F) hσ (n := 5) (by norm_num)
    simpa [ggQ2s08r6StabSUid, CFSG.ClassicalGroups.Unitary.e0, Fin.last] using h
  have hmap := ggQ2s08r6_stabSUid_conj σ P hP0
  have hmap' := ggQ2s08r6_stabSUid_conj σ P hP5
  calc
    ggQ2s08r6StabSUid (F := F) σ w ⊔ ggQ2s08r6StabSUid (F := F) σ w'
        = (ggQ2s08r6StabSUid (F := F) σ 0).map (MulAut.conj P).toMonoidHom ⊔
            (ggQ2s08r6StabSUid (F := F) σ 5).map (MulAut.conj P).toMonoidHom := by
            rw [hmap, hmap']
    _ = ((ggQ2s08r6StabSUid (F := F) σ 0 ⊔
            ggQ2s08r6StabSUid (F := F) σ 5)).map
              (MulAut.conj P).toMonoidHom := by rw [Subgroup.map_sup]
    _ = ⊤ := by
            rw [hgen, Subgroup.map_top]
            exact MonoidHom.range_eq_top.mpr (MulEquiv.surjective _)

theorem ggQ2s08r6_stab_sup (hF : Nat.card F = 4) {w w' : Fin 6} (h : w ≠ w') :
    ggQ2s08r6Stab F w ⊔ ggQ2s08r6Stab F w' = ⊤ := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP F 2 := hU.charP
  let σ : F ≃+* F := unitaryInvolution F 2 1
  have hSU := ggQ2s08r6_su_eq (F := F) hF
  have hSU6 : CFSG.LieType.Universal.Unitary.SUid σ 6 = StatedSU 6 (2 ^ 1) F := by
    dsimp [σ]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc 6
  have hP : ∀ π : Equiv.Perm (Fin 6),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ 6 := by
    intro π
    exact ggQ2s08r6_permGL_mem_SUid hU σ hSU6 π
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ := by
    dsimp [σ]
    exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hFc
  have hsup : ggQ2s08r6StabSUid (F := F) σ w ⊔
      ggQ2s08r6StabSUid (F := F) σ w' = ⊤ :=
    ggQ2s08r6_stabSUid_sup hU σ hσ hP h
  have hmapw := ggQ2s08r6Stab_eq_stabSUid_map σ hSU w
  have hmapw' := ggQ2s08r6Stab_eq_stabSUid_map σ hSU w'
  rw [hmapw, hmapw']
  have hrange : (MulEquiv.subgroupCongr hSU).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective _)
  have := congrArg (Subgroup.map (MulEquiv.subgroupCongr hSU).toMonoidHom) hsup
  rw [Subgroup.map_sup, Subgroup.map_top, hrange] at this
  exact this

theorem ggQ2s08r6_stab_perfect (hF : Nat.card F = 4) (w : Fin 6) :
    ⁅ggQ2s08r6Stab F w, ggQ2s08r6Stab F w⁆ = ggQ2s08r6Stab F w := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP F 2 := hU.charP
  let σ : F ≃+* F := unitaryInvolution F 2 1
  have hSU := ggQ2s08r6_su_eq (F := F) hF
  have hSU6 : CFSG.LieType.Universal.Unitary.SUid σ 6 = StatedSU 6 (2 ^ 1) F := by
    dsimp [σ]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc 6
  have hP : ∀ π : Equiv.Perm (Fin 6),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ 6 := by
    intro π
    exact ggQ2s08r6_permGL_mem_SUid hU σ hSU6 π
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ := by
    dsimp [σ]
    exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hFc
  haveI : Group.IsPerfect ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid hσ (n := 5) (by norm_num) (by norm_num)
  let e : ↥(ggQ2s08r6Stab F w) ≃*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) :=
    (ggQ2s08r6_stabEquiv σ hSU w).trans (ggQ2s08r6_stabWEquiv σ hP w)
  haveI : Group.IsPerfect ↥(ggQ2s08r6Stab F w) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp ‹Group.IsPerfect ↥(ggQ2s08r6Stab F w)›

theorem ggQ2s08r6_stab_simple (hF : Nat.card F = 4) (w : Fin 6) :
    IsSimpleGroup ↥(ggQ2s08r6Stab F w) := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP F 2 := hU.charP
  let σ : F ≃+* F := unitaryInvolution F 2 1
  have hSU := ggQ2s08r6_su_eq (F := F) hF
  have hSU6 : CFSG.LieType.Universal.Unitary.SUid σ 6 = StatedSU 6 (2 ^ 1) F := by
    dsimp [σ]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc 6
  have hSU5 : CFSG.LieType.Universal.Unitary.SUid σ 5 = StatedSU 5 (2 ^ 1) F := by
    dsimp [σ]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc 5
  have hP : ∀ π : Equiv.Perm (Fin 6),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ 6 := by
    intro π
    exact ggQ2s08r6_permGL_mem_SUid hU σ hSU6 π
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ := by
    dsimp [σ]
    exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hFc
  have hscal : (CFSG.Open.StatedScalars (Fin 5) F).subgroupOf
      (StatedSU 5 (2 ^ 1) F) = ⊥ := by
    ext g
    constructor
    · intro hg
      rw [Subgroup.mem_subgroupOf] at hg
      obtain ⟨c, hc⟩ := hg
      have hmem : Matrix.GeneralLinearGroup.scalar (Fin 5) c ∈ StatedSU 5 (2 ^ 1) F := by
        rw [hc]; exact g.2
      have h := (CFSG.LinearGroups.scalar_mem_statedSU_iff
        (p := 2) (f := 1) Nat.prime_two hFc (n := 5) (by norm_num) c).mp hmem
      have hc3 : c ^ 3 = 1 := by simpa using h.2
      have hc5 : c ^ 5 = 1 := h.1
      have hdvd3 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hc3
      have hdvd5 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one hc5
      have hdvd1 : orderOf c ∣ 1 := by
        have := Nat.dvd_gcd hdvd3 hdvd5
        rwa [show Nat.gcd 3 5 = 1 by norm_num] at this
      have hc1 : c = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
      rw [Subgroup.mem_bot]
      apply Subtype.ext
      rw [Subgroup.coe_one, ← hc, hc1, map_one]
    · intro hg
      rw [Subgroup.mem_bot] at hg
      rw [hg, Subgroup.mem_subgroupOf]
      exact ⟨1, by simp⟩
  haveI : IsSimpleGroup ↥(StatedSU 5 (2 ^ 1) F) := by
    have hsimple := CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU
      F 2 1 hFc 5 (by norm_num) (by norm_num)
    have e : CFSG.Open.StatedProj (StatedSU 5 (2 ^ 1) F) ≃*
        ↥(StatedSU 5 (2 ^ 1) F) :=
      (QuotientGroup.quotientMulEquivOfEq
        (G := ↥(StatedSU 5 (2 ^ 1) F)) hscal).trans QuotientGroup.quotientBot
    exact MulEquiv.isSimpleGroup e.symm
  haveI : IsSimpleGroup ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) := by
    rw [hSU5]
    infer_instance
  let e : ↥(ggQ2s08r6Stab F w) ≃*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ 5) :=
    (ggQ2s08r6_stabEquiv σ hSU w).trans (ggQ2s08r6_stabWEquiv σ hP w)
  exact MulEquiv.isSimpleGroup e

theorem ggQ2s08r6_three_dvd_card_stab (hF : Nat.card F = 4) (w : Fin 6) :
    3 ∣ Nat.card ↥(ggQ2s08r6Stab F w) := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a : Fin 6 := w.succAbove 0
  let b : Fin 6 := w.succAbove 1
  let c : Fin 6 := w.succAbove 2
  have ha : a ≠ w := Fin.succAbove_ne w 0
  have hb : b ≠ w := Fin.succAbove_ne w 1
  have hc : c ≠ w := Fin.succAbove_ne w 2
  have hab : a ≠ b := fun h =>
    (by decide : (0 : Fin 5) ≠ 1) (Fin.succAbove_right_injective h)
  have hac : a ≠ c := fun h =>
    (by decide : (0 : Fin 5) ≠ 2) (Fin.succAbove_right_injective h)
  have hbc : b ≠ c := fun h =>
    (by decide : (1 : Fin 5) ≠ 2) (Fin.succAbove_right_injective h)
  let ρ : Equiv.Perm (Fin 6) := Equiv.swap a b * Equiv.swap a c
  have hρw : ρ w = w := by
    change (Equiv.swap a b * Equiv.swap a c) w = w
    rw [Equiv.Perm.mul_apply,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hc),
      Equiv.swap_apply_of_ne_of_ne (Ne.symm ha) (Ne.symm hb)]
  have hρa : ρ a = c := by
    change (Equiv.swap a b * Equiv.swap a c) a = c
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left,
      Equiv.swap_apply_of_ne_of_ne (Ne.symm hac) (Ne.symm hbc)]
  have hcyc : ρ.IsThreeCycle :=
    Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hρ3 : ρ ^ 3 = 1 := by
    rw [← hcyc.orderOf]
    exact pow_orderOf_eq_one ρ
  have hmemSU : (permGL ρ : GL (Fin 6) F) ∈ LargeEvenSUGroup (Fin 6) F 2 := by
    have h := CFSG.StandardType.LineU.permGL_mem_unitarySU hU ρ
    have h' : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F 6 =
        LargeEvenSUGroup (Fin 6) F 2 := rfl
    rwa [h'] at h
  let g0 : ↥(LargeEvenSUGroup (Fin 6) F 2) := ⟨permGL ρ, hmemSU⟩
  have hmemStab : g0 ∈ ggQ2s08r6Stab F w :=
    ggQ2s08r6_permGL_mem_stab hρw g0 rfl
  let P : ↥(ggQ2s08r6Stab F w) := ⟨g0, hmemStab⟩
  have hP3 : P ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((permGL ρ : GL (Fin 6) F)) ^ 3 = 1
    rw [← map_pow (permGL (K := F)), hρ3, map_one]
  have hP1 : P ≠ 1 := by
    intro hP
    have hgl : (permGL ρ : GL (Fin 6) F) = 1 := by
      simpa [P, g0] using
        congrArg (fun x : ↥(ggQ2s08r6Stab F w) => (x : GL (Fin 6) F)) hP
    have hcol : ((permGL ρ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *ᵥ
        (Pi.single a (1 : F) : Fin 6 → F) = (Pi.single a (1 : F) : Fin 6 → F) := by
      rw [hgl]
      change (1 : Matrix (Fin 6) (Fin 6) F) *ᵥ
        (Pi.single a (1 : F) : Fin 6 → F) = (Pi.single a (1 : F) : Fin 6 → F)
      rw [Matrix.one_mulVec]
    have hstar := congrFun hcol a
    rw [CFSG.RankThree.Classical.permGL_mulVec] at hstar
    simp only [Function.comp_apply, Pi.single_apply] at hstar
    have hinv : ρ⁻¹ a = a := by
      by_contra hne
      rw [if_neg hne] at hstar
      exact zero_ne_one hstar
    have hfix : ρ a = a := by
      rw [Equiv.Perm.inv_def, Equiv.symm_apply_eq] at hinv
      exact hinv.symm
    exact (Ne.symm hac) (hρa.symm.trans hfix)
  have hord : orderOf P = 3 := orderOf_eq_prime hP3 hP1
  have := orderOf_dvd_natCard P
  rwa [hord] at this

noncomputable def ggQ2s08r6_stabSUEquiv (hF : Nat.card F = 4) (w : Fin 6) :
    ↥(ggQ2s08r6Stab F w) ≃* ↥(StatedSU 5 (2 ^ 1) F) := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  haveI : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  haveI : CharP F 2 := hU.charP
  have hSU := ggQ2s08r6_su_eq (F := F) hF
  have hSU6 : CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution F 2 1) 6 =
      StatedSU 6 (2 ^ 1) F := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc 6
  have hSU5 : CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution F 2 1) 5 =
      StatedSU 5 (2 ^ 1) F := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc 5
  have hP : ∀ π : Equiv.Perm (Fin 6),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution F 2 1) 6 :=
    fun π => ggQ2s08r6_permGL_mem_SUid hU _ hSU6 π
  exact ((ggQ2s08r6_stabEquiv _ hSU w).trans (ggQ2s08r6_stabWEquiv _ hP w)).trans
    (MulEquiv.subgroupCongr hSU5)

end CFSG.StandardType

end
