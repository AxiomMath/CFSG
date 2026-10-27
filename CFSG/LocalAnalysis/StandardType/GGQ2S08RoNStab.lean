module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08SuGen
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.SectionRank.OddCover.DegreeThree
public import CFSG.ClassicalGroups.Unitary.Simple
public import CFSG.LieType.Universal.Unitary.Clause0
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

variable {F : Type} [Field F] [Finite F] {n : ℕ}

@[expose] def ggQ2s08rNStab (F : Type) [Field F] (w : Fin (n + 1)) :
    Subgroup ↥(LargeEvenSUGroup (Fin (n + 1)) F 2) where
  carrier := {g | ∀ i, ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i w =
    if i = w then 1 else 0}
  one_mem' := by
    intro i
    change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i w = if i = w then 1 else 0
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
    have hcol : ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
        (Pi.single w (1 : F)) = Pi.single w 1 := by
      funext i
      rw [Matrix.mulVec_single_one, Matrix.col_apply, hg i, Pi.single_apply]
    have hprod : (((g⁻¹ : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)) : GL (Fin (n + 1)) F) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) * ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1))
          (Fin (n + 1)) F) = 1 := by
      simp
    have hinv : (((g⁻¹ : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)) : GL (Fin (n + 1)) F) :
        Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ (Pi.single w (1 : F)) = Pi.single w 1 := by
      calc
        (((g⁻¹ : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)) : GL (Fin (n + 1)) F) :
              Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ (Pi.single w (1 : F))
            = (((g⁻¹ : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)) : GL (Fin (n + 1)) F) :
                Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
                (((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
                  (Pi.single w (1 : F))) := by rw [hcol]
        _ = ((((g⁻¹ : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)) : GL (Fin (n + 1)) F) :
                Matrix (Fin (n + 1)) (Fin (n + 1)) F) *
              ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) *ᵥ
                (Pi.single w (1 : F)) := by rw [← Matrix.mulVec_mulVec]
        _ = Pi.single w 1 := by rw [hprod, Matrix.one_mulVec]
    intro i
    have := congrFun hinv i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    exact this

omit [Finite F] in
private theorem ggQ2s08rN_stab_col_iff {w : Fin (n + 1)}
    {g : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)} :
    (∀ i,
      ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i w = if i = w then 1 else
      0) ↔
      ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ (Pi.single w (1 : F)) =
        Pi.single w 1 := by
  constructor
  · intro h
    funext i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, h i, Pi.single_apply]
  · intro h i
    have := congrFun h i
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    exact this

private theorem ggQ2s08rN_su_eq [Fact (Nat.Prime 2)] [CharP F 2] (hF : Nat.card F = 4) :
    CFSG.LieType.Universal.Unitary.SUid
        (unitaryInvolution F 2 1) (n + 1) = LargeEvenSUGroup (Fin (n + 1)) F 2 := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  rw [CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc (n + 1)]
  rfl

private abbrev ggQ2s08rNStabSUid (σ : F ≃+* F) (w : Fin (n + 1)) :
    Subgroup ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1)) :=
  MulAction.stabilizer (CFSG.LieType.Universal.Unitary.SUid σ (n + 1))
    (Pi.single w (1 : F) : Fin (n + 1) → F)

omit [Finite F] in
private theorem ggQ2s08rNStab_eq_stabSUid_map
    (σ : F ≃+* F) (hSU : CFSG.LieType.Universal.Unitary.SUid σ (n + 1) =
      LargeEvenSUGroup (Fin (n + 1)) F 2) (w : Fin (n + 1)) :
    ggQ2s08rNStab F w =
      (ggQ2s08rNStabSUid (F := F) (n := n) σ w).map
        (MulEquiv.subgroupCongr hSU).toMonoidHom := by
  classical
  ext g
  constructor
  · intro hg
    refine Subgroup.mem_map.mpr ⟨(MulEquiv.subgroupCongr hSU).symm g, ?_, ?_⟩
    · rw [ggQ2s08rNStabSUid, MulAction.mem_stabilizer_iff]
      have hcol : ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
          (Pi.single w (1 : F)) = Pi.single w 1 :=
        (ggQ2s08rN_stab_col_iff).mp hg
      change ((((MulEquiv.subgroupCongr hSU).symm g :
        ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))) : GL (Fin (n + 1)) F) :
          Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ (Pi.single w (1 : F)) = Pi.single w 1
      exact hcol
    · exact MulEquiv.apply_symm_apply (MulEquiv.subgroupCongr hSU) g
  · rintro ⟨k, hk, rfl⟩
    have hk' : ((k : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
        (Pi.single w (1 : F)) = Pi.single w 1 := by
      have hk2 := (MulAction.mem_stabilizer_iff).mp hk
      rw [CFSG.ClassicalGroups.Unitary.smul_def] at hk2
      exact hk2
    have hcol : ∀ i, ((k : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i w =
        if i = w then 1 else 0 := by
      intro i
      have := congrFun hk' i
      rwa [Matrix.mulVec_single_one, Matrix.col_apply, Pi.single_apply] at this
    intro i
    exact hcol i

omit [Finite F] in
private theorem ggQ2s08rN_suid_stab_row (σ : F ≃+* F) (w : Fin (n + 1))
    {g : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))}
    (hg : g ∈ ggQ2s08rNStabSUid (F := F) (n := n) σ w) (i : Fin (n + 1)) :
    ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) w i = if i = w then 1 else 0
      := by
  have hcol : ∀ k, ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) k w =
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

theorem ggQ2s08rN_stab_row (hF : Nat.card F = 4) {w : Fin (n + 1)}
    {g : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)} (hg : g ∈ ggQ2s08rNStab F w) (i : Fin (n + 1)) :
    ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) w i = if i = w then 1 else 0
      := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  have : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  have : CharP F 2 := hU.charP
  let σ : F ≃+* F := unitaryInvolution F 2 1
  have hSU := ggQ2s08rN_su_eq (F := F) (n := n) hF
  have hmap := ggQ2s08rNStab_eq_stabSUid_map (F := F) σ hSU w
  have hg' : g ∈ (ggQ2s08rNStabSUid (F := F) (n := n) σ w).map
      (MulEquiv.subgroupCongr hSU).toMonoidHom := hmap ▸ hg
  obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hg'
  have hrow := ggQ2s08rN_suid_stab_row (F := F) σ w hk i
  rw [← hkg]
  exact hrow

theorem ggQ2s08rN_stab_commute (hF : Nat.card F = 4) {w : Fin (n + 1)}
    {g : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)} (hg : g ∈ ggQ2s08rNStab F w) {t : Fin (n + 1) → Fˣ}
    (ht : ∀ i j, i ≠ w → j ≠ w → t i = t j) :
    (g : GL (Fin (n + 1)) F) * diagHom (n + 1) t = diagHom (n + 1) t * g := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, coe_diagHom, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  by_cases hi : i = w
  · rw [hi]
    rw [ggQ2s08rN_stab_row hF hg j]
    by_cases hj : j = w
    · simp [hj]
    · simp [hj]
  · by_cases hj : j = w
    · rw [hj, hg i, if_neg hi]
      simp
    · rw [ht i j hi hj]
      ring

omit [Finite F] in
theorem ggQ2s08rN_permGL_mem_stab {σ : Equiv.Perm (Fin (n + 1))} {w : Fin (n + 1)} (hσ : σ w = w)
    (g : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2)) (hg : (g : GL (Fin (n + 1)) F) = permGL σ) :
    g ∈ ggQ2s08rNStab F w := by
  change ∀ i, ((g : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i w =
    if i = w then 1 else 0
  rw [hg]
  have hcol : ((permGL σ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
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

private def ggQ2s08rN_ee : Fin 1 ⊕ Fin n ≃ Fin (n + 1) where
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

@[simp] private theorem ggQ2s08rN_ee_inl {n : ℕ} (i : Fin 1) :
    (ggQ2s08rN_ee (n := n)) (Sum.inl i) = 0 := by
  have hi : i = 0 := Subsingleton.elim i 0
  subst hi
  rfl

@[simp] private theorem ggQ2s08rN_ee_inr {n : ℕ} (j : Fin n) :
    (ggQ2s08rN_ee (n := n)) (Sum.inr j) = j.succ := rfl

private noncomputable def ggQ2s08rN_blockMat0 (X : Matrix (Fin n) (Fin n) F) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) F :=
  Matrix.reindexAlgEquiv F F ggQ2s08rN_ee (Matrix.fromBlocks 1 0 0 X)

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_apply (X : Matrix (Fin n) (Fin n) F)
    (p q : Fin 1 ⊕ Fin n) :
    ggQ2s08rN_blockMat0 X (ggQ2s08rN_ee p) (ggQ2s08rN_ee q) =
      Matrix.fromBlocks 1 0 0 X p q := by
  rw [ggQ2s08rN_blockMat0, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  simp

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_zero_zero (X : Matrix (Fin n) (Fin n) F) :
    ggQ2s08rN_blockMat0 X 0 0 = 1 := by
  have h := ggQ2s08rN_blockMat0_apply (F := F) X (Sum.inl 0) (Sum.inl 0)
  simpa using h

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_zero_succ (X : Matrix (Fin n) (Fin n) F)
    (j : Fin n) : ggQ2s08rN_blockMat0 X 0 j.succ = 0 := by
  have h := ggQ2s08rN_blockMat0_apply (F := F) X (Sum.inl 0) (Sum.inr j)
  simpa using h

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_succ_zero (X : Matrix (Fin n) (Fin n) F)
    (i : Fin n) : ggQ2s08rN_blockMat0 X i.succ 0 = 0 := by
  have h := ggQ2s08rN_blockMat0_apply (F := F) X (Sum.inr i) (Sum.inl 0)
  simpa using h

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_succ_succ (X : Matrix (Fin n) (Fin n) F)
    (i j : Fin n) : ggQ2s08rN_blockMat0 X i.succ j.succ = X i j := by
  have h := ggQ2s08rN_blockMat0_apply (F := F) X (Sum.inr i) (Sum.inr j)
  simpa using h

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_det (X : Matrix (Fin n) (Fin n) F) :
    (ggQ2s08rN_blockMat0 X).det = X.det := by
  rw [ggQ2s08rN_blockMat0, Matrix.det_reindexAlgEquiv,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_mul (X Y : Matrix (Fin n) (Fin n) F) :
    ggQ2s08rN_blockMat0 (X * Y) =
      ggQ2s08rN_blockMat0 X * ggQ2s08rN_blockMat0 Y := by
  rw [ggQ2s08rN_blockMat0, ggQ2s08rN_blockMat0, ggQ2s08rN_blockMat0,
    ← Matrix.reindexAlgEquiv_mul]
  congr 1
  rw [Matrix.fromBlocks_multiply]
  simp

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_one :
    ggQ2s08rN_blockMat0 (1 : Matrix (Fin n) (Fin n) F) = 1 := by
  rw [ggQ2s08rN_blockMat0, Matrix.fromBlocks_one]
  exact map_one _

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_map (f : F →+* F)
    (X : Matrix (Fin n) (Fin n) F) :
    (ggQ2s08rN_blockMat0 X).map f = ggQ2s08rN_blockMat0 (X.map f) := by
  ext i j
  rw [Matrix.map_apply, ggQ2s08rN_blockMat0, ggQ2s08rN_blockMat0,
    Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.reindex_apply]
  change f (Matrix.fromBlocks 1 0 0 X (ggQ2s08rN_ee.symm i)
    (ggQ2s08rN_ee.symm j)) =
    (Matrix.reindexAlgEquiv F F ggQ2s08rN_ee)
      (Matrix.fromBlocks 1 0 0 (X.map f)) i j
  rw [Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply]
  change (Matrix.fromBlocks 1 0 0 X).map f (ggQ2s08rN_ee.symm i)
      (ggQ2s08rN_ee.symm j) =
    Matrix.fromBlocks 1 0 0 (X.map f) (ggQ2s08rN_ee.symm i)
      (ggQ2s08rN_ee.symm j)
  rw [Matrix.fromBlocks_map]
  simp

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_transpose (X : Matrix (Fin n) (Fin n) F) :
    (ggQ2s08rN_blockMat0 X)ᵀ = ggQ2s08rN_blockMat0 Xᵀ := by
  rw [ggQ2s08rN_blockMat0, ggQ2s08rN_blockMat0, Matrix.coe_reindexAlgEquiv,
    Matrix.transpose_reindex, Matrix.fromBlocks_transpose]
  congr 1
  simp

private noncomputable def ggQ2s08rN_blockGL (X : GL (Fin n) F) : GL (Fin (n + 1)) F :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    (ggQ2s08rN_blockMat0 (X : Matrix (Fin n) (Fin n) F))
    (by rw [ggQ2s08rN_blockMat0_det]; exact Matrix.GeneralLinearGroup.det_ne_zero X)

omit [Finite F] in
private theorem ggQ2s08rN_val_blockGL (X : GL (Fin n) F) :
    ((ggQ2s08rN_blockGL X : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) =
      ggQ2s08rN_blockMat0 (X : Matrix (Fin n) (Fin n) F) :=
  Matrix.GeneralLinearGroup.val_mkOfDetNeZero _ _

omit [Finite F] in
private theorem ggQ2s08rN_blockGL_mem_SUid (σ : F ≃+* F) {X : GL (Fin n) F}
    (hX : X ∈ CFSG.LieType.Universal.Unitary.SUid σ n) :
    ggQ2s08rN_blockGL X ∈ CFSG.LieType.Universal.Unitary.SUid σ (n + 1) := by
  rw [CFSG.LieType.Universal.Unitary.mem_SUid] at hX ⊢
  refine ⟨?_, ?_⟩
  · rw [ggQ2s08rN_val_blockGL, ggQ2s08rN_blockMat0_det, hX.1]
  · rw [ggQ2s08rN_val_blockGL]
    calc
      CFSG.LieType.Universal.Unitary.conjTr σ
            (ggQ2s08rN_blockMat0 (X : Matrix (Fin n) (Fin n) F)) *
          ggQ2s08rN_blockMat0 (X : Matrix (Fin n) (Fin n) F)
          = (ggQ2s08rN_blockMat0
              ((X : Matrix (Fin n) (Fin n) F).map σ))ᵀ *
              ggQ2s08rN_blockMat0 (X : Matrix (Fin n) (Fin n) F) := by
              rw [CFSG.LieType.Universal.Unitary.conjTr]
              congr 1
              simpa using ggQ2s08rN_blockMat0_map (f := σ.toRingHom)
                (X := (X : Matrix (Fin n) (Fin n) F))
      _ = ggQ2s08rN_blockMat0
            ((X : Matrix (Fin n) (Fin n) F).map σ)ᵀ *
              ggQ2s08rN_blockMat0 (X : Matrix (Fin n) (Fin n) F) := by
              rw [ggQ2s08rN_blockMat0_transpose]
      _ = ggQ2s08rN_blockMat0
            (((X : Matrix (Fin n) (Fin n) F).map σ)ᵀ *
              (X : Matrix (Fin n) (Fin n) F)) := by
              rw [ggQ2s08rN_blockMat0_mul]
      _ = ggQ2s08rN_blockMat0 1 := by
              rw [show ((X : Matrix (Fin n) (Fin n) F).map σ)ᵀ *
                  (X : Matrix (Fin n) (Fin n) F) =
                CFSG.LieType.Universal.Unitary.conjTr σ
                    (X : Matrix (Fin n) (Fin n) F) *
                  (X : Matrix (Fin n) (Fin n) F) from rfl, hX.2]
      _ = 1 := ggQ2s08rN_blockMat0_one

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_fixes_e0 (X : Matrix (Fin n) (Fin n) F) :
    ggQ2s08rN_blockMat0 X *ᵥ (Pi.single (0 : Fin (n + 1)) (1 : F)) = Pi.single 0 1 := by
  funext i
  rw [Matrix.mulVec_single_one, Matrix.col_apply]
  induction i using Fin.cases with
  | zero => rw [ggQ2s08rN_blockMat0_zero_zero]; simp
  | succ j => rw [ggQ2s08rN_blockMat0_succ_zero]; simp

omit [Finite F] in
private theorem ggQ2s08rN_blkMat_blockMat0 (X : Matrix (Fin n) (Fin n) F) :
    CFSG.ClassicalGroups.Unitary.blkMat (ggQ2s08rN_blockMat0 X) = X := by
  ext i j
  rw [CFSG.ClassicalGroups.Unitary.blkMat, Matrix.submatrix_apply,
    ggQ2s08rN_blockMat0_succ_succ]

omit [Finite F] in
private theorem ggQ2s08rN_blockMat0_blkMat (σ : F ≃+* F)
    {M : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))}
    (hM : M ∈ ggQ2s08rNStabSUid (F := F) (n := n) σ 0) :
    ggQ2s08rN_blockMat0 (CFSG.ClassicalGroups.Unitary.blkMat
      ((M : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
      ((M : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) := by
  have hrow := ggQ2s08rN_suid_stab_row (F := F) σ 0 hM
  have hcol : ∀ i, ((M : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) i 0 =
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
      | zero => rw [ggQ2s08rN_blockMat0_zero_zero, hcol 0]; simp
      | succ j => rw [ggQ2s08rN_blockMat0_zero_succ, hrow j.succ]; simp
  | succ i =>
      induction j using Fin.cases with
      | zero => rw [ggQ2s08rN_blockMat0_succ_zero, hcol i.succ]; simp
      | succ j => rw [ggQ2s08rN_blockMat0_succ_succ,
          CFSG.ClassicalGroups.Unitary.blkMat, Matrix.submatrix_apply]

private noncomputable def ggQ2s08rN_blockHom (σ : F ≃+* F) :
    ↥(CFSG.LieType.Universal.Unitary.SUid σ n) →*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1)) where
  toFun X := ⟨ggQ2s08rN_blockGL (X : GL (Fin n) F),
    ggQ2s08rN_blockGL_mem_SUid σ X.2⟩
  map_one' := by
    apply Subtype.ext
    change (ggQ2s08rN_blockGL (1 : GL (Fin n) F) : GL (Fin (n + 1)) F) = 1
    apply Units.ext
    rw [ggQ2s08rN_val_blockGL]
    exact ggQ2s08rN_blockMat0_one
  map_mul' X Y := by
    apply Subtype.ext
    change (ggQ2s08rN_blockGL ((X : GL (Fin n) F) * (Y : GL (Fin n) F)) :
      GL (Fin (n + 1)) F) = ggQ2s08rN_blockGL (X : GL (Fin n) F) *
        ggQ2s08rN_blockGL (Y : GL (Fin n) F)
    apply Units.ext
    rw [Units.val_mul]
    rw [ggQ2s08rN_val_blockGL, ggQ2s08rN_val_blockGL, ggQ2s08rN_val_blockGL]
    rw [show ((((X : GL (Fin n) F)) * (Y : GL (Fin n) F) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) =
      ((X : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) *
        ((Y : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) from rfl,
      ggQ2s08rN_blockMat0_mul]

private noncomputable def ggQ2s08rN_blockHomStab (σ : F ≃+* F) :
    ↥(CFSG.LieType.Universal.Unitary.SUid σ n) →*
      ↥(ggQ2s08rNStabSUid (F := F) (n := n) σ 0) where
  toFun X := ⟨ggQ2s08rN_blockHom σ X, by
    rw [ggQ2s08rNStabSUid, MulAction.mem_stabilizer_iff]
    rw [CFSG.ClassicalGroups.Unitary.smul_def]
    rw [show ((ggQ2s08rN_blockHom σ X :
        ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))) : GL (Fin (n + 1)) F) =
      ggQ2s08rN_blockGL (X : GL (Fin n) F) from rfl, ggQ2s08rN_val_blockGL]
    exact ggQ2s08rN_blockMat0_fixes_e0 _⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' X Y := Subtype.ext (map_mul _ X Y)

private noncomputable def ggQ2s08rN_stab0Equiv (σ : F ≃+* F) :
    ↥(CFSG.LieType.Universal.Unitary.SUid σ n) ≃*
      ↥(ggQ2s08rNStabSUid (F := F) (n := n) σ 0) where
  toFun := ggQ2s08rN_blockHomStab σ
  invFun M := CFSG.ClassicalGroups.Unitary.blk (σ := σ) M.1
    (MulAction.mem_stabilizer_iff.mp M.2)
  left_inv X := by
    apply Subtype.ext
    apply Units.ext
    change (CFSG.ClassicalGroups.Unitary.blkMat
      ((((ggQ2s08rN_blockHomStab σ) X : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))) :
        GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
      ((X : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
    simp only [ggQ2s08rN_blockHomStab, ggQ2s08rN_blockHom]
    exact ggQ2s08rN_blkMat_blockMat0 _
  right_inv M := by
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    change ggQ2s08rN_blockMat0 (CFSG.ClassicalGroups.Unitary.blkMat
      ((M : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)) =
      ((M : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    exact ggQ2s08rN_blockMat0_blkMat (n := n) (σ := σ) (M := M) M.2
  map_mul' X Y := map_mul (ggQ2s08rN_blockHomStab σ) X Y

omit [Finite F] in
private theorem ggQ2s08rN_stabSUid_conj (σ : F ≃+* F)
    (P : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))) {v w : Fin (n + 1)}
    (hP : P • (Pi.single v (1 : F) : Fin (n + 1) → F) =
      (Pi.single w (1 : F) : Fin (n + 1) → F)) :
    (ggQ2s08rNStabSUid (F := F) (n := n) σ v).map (MulAut.conj P).toMonoidHom =
      ggQ2s08rNStabSUid (F := F) (n := n) σ w := by
  have hPinv : P⁻¹ • (Pi.single w (1 : F) : Fin (n + 1) → F) =
      (Pi.single v (1 : F) : Fin (n + 1) → F) := by
    have := congrArg (fun z => P⁻¹ • z) hP
    simpa [mul_smul] using this.symm
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simp only [ggQ2s08rNStabSUid, MulAction.mem_stabilizer_iff] at hy ⊢
    calc
      (P * y * P⁻¹) • (Pi.single w (1 : F) : Fin (n + 1) → F)
          = P • (y • (P⁻¹ • (Pi.single w (1 : F) : Fin (n + 1) → F))) := by simp [mul_smul]
      _ = P • (y • (Pi.single v (1 : F) : Fin (n + 1) → F)) := by rw [hPinv]
      _ = P • (Pi.single v (1 : F) : Fin (n + 1) → F) := by rw [hy]
      _ = (Pi.single w (1 : F) : Fin (n + 1) → F) := hP
  · intro hx
    refine ⟨P⁻¹ * x * P, ?_, ?_⟩
    · simp only [ggQ2s08rNStabSUid, MulAction.mem_stabilizer_iff] at hx ⊢
      calc
        (P⁻¹ * x * P) • (Pi.single v (1 : F) : Fin (n + 1) → F)
            = P⁻¹ • (x • (P • (Pi.single v (1 : F) : Fin (n + 1) → F))) := by simp [mul_smul]
        _ = P⁻¹ • (x • (Pi.single w (1 : F) : Fin (n + 1) → F)) := by rw [hP]
        _ = P⁻¹ • (Pi.single w (1 : F) : Fin (n + 1) → F) := by rw [hx]
        _ = (Pi.single v (1 : F) : Fin (n + 1) → F) := hPinv
    · change P * (P⁻¹ * x * P) * P⁻¹ = x
      group

private noncomputable def ggQ2s08rN_stabConjEquiv (σ : F ≃+* F)
    (P : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))) {v w : Fin (n + 1)}
    (hP : P • (Pi.single v (1 : F) : Fin (n + 1) → F) =
      (Pi.single w (1 : F) : Fin (n + 1) → F)) :
    ↥(ggQ2s08rNStabSUid (F := F) (n := n) σ v) ≃*
      ↥(ggQ2s08rNStabSUid (F := F) (n := n) σ w) :=
  (MulEquiv.subgroupMap (MulAut.conj P) (ggQ2s08rNStabSUid (F := F) (n := n) σ v)).trans
    (MulEquiv.subgroupCongr (ggQ2s08rN_stabSUid_conj σ P hP))

private noncomputable def ggQ2s08rN_stabEquiv (σ : F ≃+* F)
    (hSU : CFSG.LieType.Universal.Unitary.SUid σ (n + 1) =
      LargeEvenSUGroup (Fin (n + 1)) F 2) (w : Fin (n + 1)) :
    ↥(ggQ2s08rNStab F w) ≃*
      ↥(ggQ2s08rNStabSUid (F := F) (n := n) σ w) :=
  (MulEquiv.subgroupCongr (ggQ2s08rNStab_eq_stabSUid_map σ hSU w)).trans
    (MulEquiv.subgroupMap (MulEquiv.subgroupCongr hSU)
      (ggQ2s08rNStabSUid (F := F) (n := n) σ w)).symm

omit [Finite F] in
private theorem ggQ2s08rN_permGL_mem_SUid
    (hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (σ : F ≃+* F)
    (hSU : CFSG.LieType.Universal.Unitary.SUid σ (n + 1) = StatedSU (n + 1) (2 ^ 1) F)
    (π : Equiv.Perm (Fin (n + 1))) :
    permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ (n + 1) := by
  rw [hSU]
  exact CFSG.StandardType.LineU.permGL_mem_unitarySU hU π

omit [Finite F] in
private theorem ggQ2s08rN_permGL_smul_single {σ : F ≃+* F}
    (hP : ∀ π : Equiv.Perm (Fin (n + 1)),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    (⟨permGL π, hP π⟩ : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1))) •
        (Pi.single i (1 : F) : Fin (n + 1) → F) =
      (Pi.single (π i) (1 : F) : Fin (n + 1) → F) := by
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

private theorem ggQ2s08rN_exists_perm (hn : 1 ≤ n) (w w' : Fin (n + 1)) (h : w ≠ w') :
    ∃ π : Equiv.Perm (Fin (n + 1)), π 0 = w ∧ π (Fin.last n) = w' := by
  have hlast : (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h0
    have := congrArg Fin.val h0
    simp [Fin.last] at this
    omega
  let f : Fin 2 → Fin (n + 1) := ![0, Fin.last n]
  let g : Fin 2 → Fin (n + 1) := ![w, w']
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have hg : Function.Injective g := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [g]
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨π, ?_, ?_⟩
  · simpa [f, g] using hπ 0
  · simpa [f, g] using hπ 1

private noncomputable def ggQ2s08rN_stabWEquiv (σ : F ≃+* F)
    (hP : ∀ π : Equiv.Perm (Fin (n + 1)),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ (n + 1)) (w : Fin (n + 1)) :
    ↥(ggQ2s08rNStabSUid (F := F) (n := n) σ w) ≃*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ n) := by
  classical
  let π : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 w
  have hπ0 : π 0 = w := Equiv.swap_apply_left 0 w
  let P : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1)) := ⟨permGL π, hP π⟩
  have hP0 : P • (Pi.single 0 (1 : F) : Fin (n + 1) → F) =
      (Pi.single w (1 : F) : Fin (n + 1) → F) := by
    rw [ggQ2s08rN_permGL_smul_single hP π 0, hπ0]
  exact (ggQ2s08rN_stabConjEquiv σ P hP0).symm.trans
    (ggQ2s08rN_stab0Equiv σ).symm

private theorem ggQ2s08rN_stabSUid_sup
    (_hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F)
    (σ : F ≃+* F) (hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ)
    (hP : ∀ π : Equiv.Perm (Fin (n + 1)),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ (n + 1))
    (hn : 5 ≤ n)
    {w w' : Fin (n + 1)} (h : w ≠ w') :
    ggQ2s08rNStabSUid (F := F) (n := n) σ w ⊔
      ggQ2s08rNStabSUid (F := F) (n := n) σ w' = ⊤ := by
  obtain ⟨π, hπ0, hπlast⟩ := ggQ2s08rN_exists_perm (by omega) w w' h
  let P : ↥(CFSG.LieType.Universal.Unitary.SUid σ (n + 1)) := ⟨permGL π, hP π⟩
  have hP0 : P • (Pi.single 0 (1 : F) : Fin (n + 1) → F) =
      (Pi.single w (1 : F) : Fin (n + 1) → F) := by
    rw [ggQ2s08rN_permGL_smul_single hP π 0, hπ0]
  have hP5 : P • (Pi.single (Fin.last n) (1 : F) : Fin (n + 1) → F) =
      (Pi.single w' (1 : F) : Fin (n + 1) → F) := by
    rw [ggQ2s08rN_permGL_smul_single hP π (Fin.last n), hπlast]
  have hgen : ggQ2s08rNStabSUid (F := F) (n := n) σ 0 ⊔
      ggQ2s08rNStabSUid (F := F) (n := n) σ (Fin.last n) = ⊤ := by
    have h := ggQ2s08_su_stab_generate (K := F) (n := n) hσ (by omega)
    simpa [ggQ2s08rNStabSUid, CFSG.ClassicalGroups.Unitary.e0, Fin.last] using h
  have hmap := ggQ2s08rN_stabSUid_conj σ P hP0
  have hmap' := ggQ2s08rN_stabSUid_conj σ P hP5
  calc
    ggQ2s08rNStabSUid (F := F) (n := n) σ w ⊔ ggQ2s08rNStabSUid (F := F) (n := n) σ w'
        = (ggQ2s08rNStabSUid (F := F) (n := n) σ 0).map (MulAut.conj P).toMonoidHom ⊔
            (ggQ2s08rNStabSUid (F := F) (n := n) σ (Fin.last n)).map
              (MulAut.conj P).toMonoidHom := by
            rw [hmap, hmap']
    _ = ((ggQ2s08rNStabSUid (F := F) (n := n) σ 0 ⊔
            ggQ2s08rNStabSUid (F := F) (n := n) σ (Fin.last n))).map
              (MulAut.conj P).toMonoidHom := by rw [Subgroup.map_sup]
    _ = ⊤ := by
            rw [hgen, Subgroup.map_top]
            exact MonoidHom.range_eq_top.mpr (MulEquiv.surjective _)

theorem ggQ2s08rN_stab_sup (hF : Nat.card F = 4) (hn : 5 ≤ n) {w w' : Fin (n + 1)} (h : w ≠ w') :
    ggQ2s08rNStab F w ⊔ ggQ2s08rNStab F w' = ⊤ := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  have : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  have : CharP F 2 := hU.charP
  let σ : F ≃+* F := unitaryInvolution F 2 1
  have hSU := ggQ2s08rN_su_eq (F := F) (n := n) hF
  have hSU6 : CFSG.LieType.Universal.Unitary.SUid σ (n + 1) = StatedSU (n + 1) (2 ^ 1) F := by
    dsimp [σ]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc (n + 1)
  have hP : ∀ π : Equiv.Perm (Fin (n + 1)),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ (n + 1) := by
    intro π
    exact ggQ2s08rN_permGL_mem_SUid hU σ hSU6 π
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ := by
    dsimp [σ]
    exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hFc
  have hsup : ggQ2s08rNStabSUid (F := F) (n := n) σ w ⊔
      ggQ2s08rNStabSUid (F := F) (n := n) σ w' = ⊤ :=
    ggQ2s08rN_stabSUid_sup hU σ hσ hP hn h
  have hmapw := ggQ2s08rNStab_eq_stabSUid_map σ hSU w
  have hmapw' := ggQ2s08rNStab_eq_stabSUid_map σ hSU w'
  rw [hmapw, hmapw']
  have hrange : (MulEquiv.subgroupCongr hSU).toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr (MulEquiv.surjective _)
  have := congrArg (Subgroup.map (MulEquiv.subgroupCongr hSU).toMonoidHom) hsup
  rw [Subgroup.map_sup, Subgroup.map_top, hrange] at this
  exact this

theorem ggQ2s08rN_stab_perfect (hF : Nat.card F = 4) (hn : 4 ≤ n) (w : Fin (n + 1)) :
    ⁅ggQ2s08rNStab F w, ggQ2s08rNStab F w⁆ = ggQ2s08rNStab F w := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  have : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  have : CharP F 2 := hU.charP
  let σ : F ≃+* F := unitaryInvolution F 2 1
  have hSU := ggQ2s08rN_su_eq (F := F) (n := n) hF
  have hSU6 : CFSG.LieType.Universal.Unitary.SUid σ (n + 1) = StatedSU (n + 1) (2 ^ 1) F := by
    dsimp [σ]
    exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc (n + 1)
  have hP : ∀ π : Equiv.Perm (Fin (n + 1)),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid σ (n + 1) := by
    intro π
    exact ggQ2s08rN_permGL_mem_SUid hU σ hSU6 π
  have hσ : CFSG.ClassicalGroups.Unitary.IsUnitaryInvolution σ := by
    dsimp [σ]
    exact CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hFc
  have : Group.IsPerfect ↥(CFSG.LieType.Universal.Unitary.SUid σ n) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_SUid hσ (n := n) (by omega) (by omega)
  let e : ↥(ggQ2s08rNStab F w) ≃*
      ↥(CFSG.LieType.Universal.Unitary.SUid σ n) :=
    (ggQ2s08rN_stabEquiv σ hSU w).trans (ggQ2s08rN_stabWEquiv σ hP w)
  have : Group.IsPerfect ↥(ggQ2s08rNStab F w) :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp ‹Group.IsPerfect ↥(ggQ2s08rNStab F w)›

theorem ggQ2s08rN_three_dvd_card_stab (hF : Nat.card F = 4) (hn : 3 ≤ n) (w : Fin (n + 1)) :
    3 ∣ Nat.card ↥(ggQ2s08rNStab F w) := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let a : Fin (n + 1) := w.succAbove ⟨0, by omega⟩
  let b : Fin (n + 1) := w.succAbove ⟨1, by omega⟩
  let c : Fin (n + 1) := w.succAbove ⟨2, by omega⟩
  have ha : a ≠ w := Fin.succAbove_ne w ⟨0, by omega⟩
  have hb : b ≠ w := Fin.succAbove_ne w ⟨1, by omega⟩
  have hc : c ≠ w := Fin.succAbove_ne w ⟨2, by omega⟩
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ :=
    Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega : (0 : Nat) < 1))
  have h02 : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ :=
    Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega : (0 : Nat) < 2))
  have h12 : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ :=
    Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega : (1 : Nat) < 2))
  have hab : a ≠ b := fun h => h01 (Fin.succAbove_right_injective h)
  have hac : a ≠ c := fun h => h02 (Fin.succAbove_right_injective h)
  have hbc : b ≠ c := fun h => h12 (Fin.succAbove_right_injective h)
  let ρ : Equiv.Perm (Fin (n + 1)) := Equiv.swap a b * Equiv.swap a c
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
  have hmemSU : (permGL ρ : GL (Fin (n + 1)) F) ∈ LargeEvenSUGroup (Fin (n + 1)) F 2 := by
    have h := CFSG.StandardType.LineU.permGL_mem_unitarySU hU ρ
    have h' : CFSG.ClassicalGroups.UnitaryFlag.unitarySU 2 1 F (n + 1) =
        LargeEvenSUGroup (Fin (n + 1)) F 2 := rfl
    rwa [h'] at h
  let g0 : ↥(LargeEvenSUGroup (Fin (n + 1)) F 2) := ⟨permGL ρ, hmemSU⟩
  have hmemStab : g0 ∈ ggQ2s08rNStab F w :=
    ggQ2s08rN_permGL_mem_stab hρw g0 rfl
  let P : ↥(ggQ2s08rNStab F w) := ⟨g0, hmemStab⟩
  have hP3 : P ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((permGL ρ : GL (Fin (n + 1)) F)) ^ 3 = 1
    rw [← map_pow (permGL (K := F)), hρ3, map_one]
  have hP1 : P ≠ 1 := by
    intro hP
    have hgl : (permGL ρ : GL (Fin (n + 1)) F) = 1 := by
      simpa [P, g0] using
        congrArg (fun x : ↥(ggQ2s08rNStab F w) => (x : GL (Fin (n + 1)) F)) hP
    have hcol : ((permGL ρ : GL (Fin (n + 1)) F) : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
        (Pi.single a (1 : F) : Fin (n + 1) → F) = (Pi.single a (1 : F) : Fin (n + 1) → F) := by
      rw [hgl]
      change (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) F) *ᵥ
        (Pi.single a (1 : F) : Fin (n + 1) → F) = (Pi.single a (1 : F) : Fin (n + 1) → F)
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

noncomputable def ggQ2s08rN_stabSUEquiv (hF : Nat.card F = 4) (w : Fin (n + 1)) :
    ↥(ggQ2s08rNStab F w) ≃* ↥(StatedSU n (2 ^ 1) F) := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hU := CFSG.ClassicalGroups.UnitaryFlag.unitaryFieldDataOfCard hFc
  have : Fact (Nat.Prime 2) := ⟨hU.prime⟩
  have : CharP F 2 := hU.charP
  have hSU := ggQ2s08rN_su_eq (F := F) (n := n) hF
  have hSU6 : CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution F 2 1) (n + 1) =
      StatedSU (n + 1) (2 ^ 1) F := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc (n + 1)
  have hSU5 : CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution F 2 1) n =
      StatedSU n (2 ^ 1) F := CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hFc n
  have hP : ∀ π : Equiv.Perm (Fin (n + 1)),
      permGL π ∈ CFSG.LieType.Universal.Unitary.SUid (unitaryInvolution F 2 1) (n + 1) :=
    fun π => ggQ2s08rN_permGL_mem_SUid hU _ hSU6 π
  exact ((ggQ2s08rN_stabEquiv _ hSU w).trans (ggQ2s08rN_stabWEquiv _ hP w)).trans
    (MulEquiv.subgroupCongr hSU5)

theorem ggQ2s08rN_stab_quasisimple (hF : Nat.card F = 4) (hn : 4 ≤ n) (w : Fin (n + 1)) :
    CFSG.Assembly.IsQuasisimple ↥(ggQ2s08rNStab F w) := by
  have hFc : Nat.card F = (2 ^ 1) ^ 2 := by simpa using hF
  have hnq : (n, 2) ≠ (3, 2) := by
    intro h
    have := congrArg Prod.fst h
    omega
  have hq := CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card
    (p := 2) (f := 1) (F := F) (n := n) hFc (by omega) hnq
  have e : ↥(ggQ2s08rNStab F w) ≃* ↥(StatedSU n (2 ^ 1) F) :=
    ggQ2s08rN_stabSUEquiv hF w
  have hq' := CFSG.LieType.Universal.Unitary.isQuasisimple_of_mulEquiv e.symm hq.1
  exact ⟨hq'.1.commutator_eq_top, hq'.2.1⟩

end CFSG.StandardType

end
