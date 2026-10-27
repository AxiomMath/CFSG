module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Universal.SymplecticExtras
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSp
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCGeneration
public import CFSG.Timmesfeld.ARS.CaseMSpPlane
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.TypeCFrame
public import CFSG.ClassicalInvolution.WeakCT.StandardPair
public import CFSG.Timmesfeld.ARS.CaseEFrame
public import CFSG.Timmesfeld.ARS.CaseMLevi
public import CFSG.Timmesfeld.ARS.Sec12Center
public import CFSG.Timmesfeld.ARS.Sec13Closed
public import CFSG.Timmesfeld.ARS.Sec13Maximal
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.StandardType.ClassicalPosition

open Matrix
open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType

private theorem gSpr_J_transpose {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)ᵀ =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem gSpr_J_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, CharTwo.neg_eq]

private theorem gSpr_J_mulVec_single {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (b : Fin n ⊕ Fin n) :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
        Pi.single b 1 = Pi.single b.swap 1 := by
  ext k
  rcases b with i | i <;> rcases k with k | k <;>
    simp [Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.fromBlocks, Fintype.sum_sum_type,
      Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem gSpr_mat_mul_inv {n : ℕ} {F : Type} [Field F] (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem gSpr_mat_inv_mul {n : ℕ} {F : Type} [Field F] (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

private theorem gSpr_mat_inv_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  have hsp : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) =
      Matrix.fromBlocks 0 1 (-1) 0 :=
    (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2
  have h2 : ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
      Matrix.fromBlocks 0 1 (-1) 0) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (Matrix.fromBlocks 0 1 (-1) 0), hsp, gSpr_J_mul_self]
  exact (left_inv_eq_right_inv h2 (gSpr_mat_mul_inv u)).symm

private theorem gSpr_transpose_inv_mul_J {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹)ᵀ *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) := by
  have htrans : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹)ᵀ =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    rw [gSpr_mat_inv_eq, Matrix.transpose_mul, Matrix.transpose_mul, gSpr_J_transpose,
      Matrix.transpose_transpose]
    noncomm_ring
  rw [htrans]
  change ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
      Matrix.fromBlocks 0 1 (-1) 0) * Matrix.fromBlocks 0 1 (-1) 0 =
    Matrix.fromBlocks 0 1 (-1) 0 * CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u
  rw [Matrix.mul_assoc ((Matrix.fromBlocks 0 1 (-1) 0) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u))
      (Matrix.fromBlocks 0 1 (-1) 0), gSpr_J_mul_self, Matrix.mul_one]

private theorem gSpr_vecMul_eq_transpose_mulVec {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (z : Fin n ⊕ Fin n → F) :
    z ᵥ* A = Aᵀ *ᵥ z := by
  have h := Matrix.vecMul_transpose (A := Aᵀ) z
  rwa [Matrix.transpose_transpose] at h

private theorem gSpr_conj_vecMulVec {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y : Fin n ⊕ Fin n → F) (c : F)
    (h : GL (Fin n ⊕ Fin n) F)
    (hh : (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 + c • Matrix.vecMulVec x y) :
    (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • Matrix.vecMulVec
        ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)
        (y ᵥ* (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹)) := by
  rw [show (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h =
      (u : GL (Fin n ⊕ Fin n) F) * h * (u : GL (Fin n ⊕ Fin n) F)⁻¹ from rfl]
  rw [Units.val_mul, Units.val_mul]
  change (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
      (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) = _
  rw [hh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, gSpr_mat_mul_inv, zero_add]

private theorem gSpr_conj_add_vecMulVec {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y x' y' : Fin n ⊕ Fin n → F) (c : F)
    (h : GL (Fin n ⊕ Fin n) F)
    (hh : (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.vecMulVec x y + Matrix.vecMulVec x' y')) :
    (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.vecMulVec
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)
          (y ᵥ* (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹)) +
        Matrix.vecMulVec ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x')
          (y' ᵥ* (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹))) := by
  rw [show (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h =
      (u : GL (Fin n ⊕ Fin n) F) * h * (u : GL (Fin n ⊕ Fin n) F)⁻¹ from rfl]
  rw [Units.val_mul, Units.val_mul]
  change (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *
      (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) = _
  rw [hh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, gSpr_mat_mul_inv, zero_add]

private theorem gSpr_conj_matTransvGroup_le {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) (v : Fin n ⊕ Fin n → F) :
    (matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v)).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom ≤
      matTransvGroup ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ v)
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ v)) := by
  have hJU := gSpr_transpose_inv_mul_J u
  rw [matTransvGroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨h, ⟨c, hc⟩, rfl⟩
  refine Subgroup.subset_closure ⟨c, ?_⟩
  change (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
  rw [gSpr_conj_vecMulVec u v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v) c h hc]
  congr 2
  rw [← Matrix.transpose_transpose (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹),
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]

private theorem gSpr_conj_matTransvGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) (v : Fin n ⊕ Fin n → F) :
    (matTransvGroup v ((Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ v)).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom =
      matTransvGroup ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ v)
        ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ v)) := by
  apply le_antisymm (gSpr_conj_matTransvGroup_le u v)
  have hle := gSpr_conj_matTransvGroup_le (u := u⁻¹)
    (v := (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ v)
  have hveq : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) *ᵥ
      ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, gSpr_mat_inv_mul, Matrix.one_mulVec]
  rw [hveq] at hle
  have hcomp : (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom.comp
      (MulAut.conj ((u⁻¹ : ↥(CFSG.Open.StatedSp n F)) :
        GL (Fin n ⊕ Fin n) F)).toMonoidHom = MonoidHom.id _ := by
    apply MonoidHom.ext
    intro x
    change (MulAut.conj (u : GL (Fin n ⊕ Fin n) F))
        ((MulAut.conj ((u⁻¹ : ↥(CFSG.Open.StatedSp n F)) :
          GL (Fin n ⊕ Fin n) F)) x) = x
    rw [MulAut.conj_apply, MulAut.conj_apply]
    rw [show ((u⁻¹ : ↥(CFSG.Open.StatedSp n F)) : GL (Fin n ⊕ Fin n) F) =
      (u : GL (Fin n ⊕ Fin n) F)⁻¹ from rfl]
    group
  have hmap := Subgroup.map_mono (f := (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom) hle
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hmap
  exact hmap

private theorem gSpr_conj_altSiegelGroup {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y : Fin n ⊕ Fin n → F) :
    (altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)
        ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y) := by
  have hJU := gSpr_transpose_inv_mul_J u
  rw [altSiegelGroup, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, ⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_⟩
    change (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
    have e1 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y) ᵥ*
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) =
        Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y) := by
      rw [← Matrix.transpose_transpose
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹),
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]
    have e2 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x) ᵥ*
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) =
        Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x) := by
      rw [← Matrix.transpose_transpose
          (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹),
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]
    rw [gSpr_conj_add_vecMulVec u x (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y)
        y (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x) c h hc, e1, e2]
  · rintro ⟨c, hg⟩
    refine ⟨(MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ g, ⟨c, ?_⟩, ?_⟩
    · have hle := gSpr_conj_add_vecMulVec (u := u⁻¹)
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y))
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y)
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)) c g hg
      have hcomp : (MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ =
          MulAut.conj ((u⁻¹ : ↥(CFSG.Open.StatedSp n F)) :
            GL (Fin n ⊕ Fin n) F) := (map_inv _ _).symm
      have e1 : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) *ᵥ
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x) = x := by
        rw [Matrix.mulVec_mulVec, gSpr_mat_inv_mul, Matrix.one_mulVec]
      have e2 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y)) ᵥ*
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F ((u⁻¹)⁻¹)) =
          Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y := by
        rw [show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F (u⁻¹)⁻¹) =
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) from by rw [inv_inv],
          gSpr_vecMul_eq_transpose_mulVec (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u),
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) =
            Matrix.fromBlocks 0 1 (-1) 0 from
          (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2]
      have e3 : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u⁻¹) *ᵥ
          ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ y) = y := by
        rw [Matrix.mulVec_mulVec, gSpr_mat_inv_mul, Matrix.one_mulVec]
      have e4 : (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            ((CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) *ᵥ x)) ᵥ*
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F ((u⁻¹)⁻¹)) =
          Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x := by
        rw [show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F (u⁻¹)⁻¹) =
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) from by rw [inv_inv],
          gSpr_vecMul_eq_transpose_mulVec (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u),
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          show (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u)ᵀ *
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F u) =
            Matrix.fromBlocks 0 1 (-1) 0 from
          (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2]
      rw [← hcomp] at hle
      rw [hle, e1, e2, e3, e4]
    · change (MulAut.conj (u : GL (Fin n ⊕ Fin n) F))
          ((MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ g) = g
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

private theorem gSpr_conj_one {n : ℕ} {F : Type} [Field F] :
    (MulAut.conj (1 : ↥(CFSG.Open.StatedSp n F))).toMonoidHom = MonoidHom.id _ := by
  ext x
  simp [MulAut.conj]

private theorem gSpr_map_conj_rootGroup {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) (γ : Fin n → ℤ) :
    ((Symplectic.rootGroup n F γ).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
      ((Symplectic.rootGroup n F γ).map (CFSG.Open.StatedSp n F).subtype).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem gSpr_map_conj_rootGroupDatum {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) (γ : Fin (Symplectic.rootDatum n F).rank → ℤ) :
    (((Symplectic.rootDatum n F).rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
      (((Symplectic.rootDatum n F).rootGroup γ).map (CFSG.Open.StatedSp n F).subtype).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem gSpr_exists_pair {n : ℕ} {F : Type} [Field F] (hn : 0 < n)
    {v w v' w' : Fin n ⊕ Fin n → F}
    (h : v ⬝ᵥ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w) = 1)
    (h' : v' ⬝ᵥ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w') = 1) :
    ∃ g : ↥(CFSG.Open.StatedSp n F),
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F g) *ᵥ v = v' ∧
      (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F g) *ᵥ w = w' := by
  let k : Fin n := ⟨0, hn⟩
  have hf : CFSG.ClassicalInvolution.Models.SymplecticPairs.form v w = 1 := h
  have hf' : CFSG.ClassicalInvolution.Models.SymplecticPairs.form v' w' = 1 := h'
  obtain ⟨g₁, hg₁v, hg₁w⟩ :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_sp_apply_eq_at k v w hf
  obtain ⟨g₂, hg₂v, hg₂w⟩ :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_sp_apply_eq_at k v' w' hf'
  refine ⟨g₂ * g₁⁻¹, ?_, ?_⟩
  · rw [map_mul, ← Matrix.mulVec_mulVec]
    have h1 : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F g₁⁻¹) *ᵥ v =
        Pi.single (Sum.inl k) 1 := by
      rw [← hg₁v, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mulVec]
    rw [h1, hg₂v]
  · rw [map_mul, ← Matrix.mulVec_mulVec]
    have h1 : (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F g₁⁻¹) *ᵥ w =
        Pi.single (Sum.inr k) 1 := by
      rw [← hg₁w, Matrix.mulVec_mulVec, ← map_mul, inv_mul_cancel, map_one,
        Matrix.one_mulVec]
    rw [h1, hg₂w]

private theorem gSpr_altSiegelGroup_comm {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (G : Matrix ι ι F) (v w : ι → F) :
    altSiegelGroup G v w = altSiegelGroup G w v := by
  rw [altSiegelGroup, altSiegelGroup]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq]
  constructor <;> rintro ⟨c, hc⟩ <;>
    exact ⟨c, by
      rw [hc, add_comm (Matrix.vecMulVec v (Matrix.mulVec G w))
        (Matrix.vecMulVec w (Matrix.mulVec G v))]⟩

private theorem gSpr_std_altSiegel_diff {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (i j : Fin n) (hij : i ≠ j) (γ : Fin n → ℤ)
    (hr : Symplectic.stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference i j hij) =
      Symplectic.toStd n γ) :
    (Symplectic.rootGroup n F γ).map (CFSG.Open.StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Pi.single (Sum.inl i) 1) (Pi.single (Sum.inr j) 1) := by
  have hE : Symplectic.SpExtras.E F
      (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference i j hij) =
      Matrix.single (Sum.inl i) (Sum.inl j) 1 +
        Matrix.single (Sum.inr j) (Sum.inr i) 1 := by
    ext a b
    simp [Symplectic.SpExtras.E, CharTwo.sub_eq_add]
  have hJ₁ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ Pi.single (Sum.inr j) 1 =
      Pi.single (Sum.inl j) 1 := gSpr_J_mulVec_single _
  have hJ₂ : (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *ᵥ Pi.single (Sum.inl i) 1 =
      Pi.single (Sum.inr i) 1 := gSpr_J_mulVec_single _
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (Symplectic.SpExtras.mem_rootGroup_iff hr).1 hy
    refine Subgroup.subset_closure ⟨c, ?_⟩
    change (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F
      (Symplectic.SpExtras.elt
        (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference i j hij) c)) = _
    rw [Symplectic.SpExtras.mat_elt, hE]
    congr 2
    rw [hJ₁, hJ₂, Matrix.single_eq_single_vecMulVec_single,
      Matrix.single_eq_single_vecMulVec_single]
  · rw [altSiegelGroup, Subgroup.closure_le]
    rintro x ⟨c, hx⟩
    refine ⟨Symplectic.SpExtras.elt
      (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference i j hij) c,
      (Symplectic.SpExtras.mem_rootGroup_iff hr).2 ⟨c, rfl⟩, ?_⟩
    apply Units.ext
    change (CFSG.LieType.Universal.Symplectic.SpExtras.mat n F
      (Symplectic.SpExtras.elt
        (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference i j hij) c)) =
      (x : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
    rw [hx, Symplectic.SpExtras.mat_elt, hE]
    congr 2
    rw [hJ₁, hJ₂, Matrix.single_eq_single_vecMulVec_single,
      Matrix.single_eq_single_vecMulVec_single]

private theorem gSpr_two_smul_short_not_mem {n : ℕ} {F : Type} [Field F] (hn : 2 ≤ n) :
    (2 : ℤ) • (Pi.single ⟨0, by omega⟩ (1 : ℤ) : Fin n → ℤ) ∉
      (Symplectic.rootDatum n F).roots := by
  intro hmem
  obtain ⟨r, hr⟩ := Symplectic.SpExtras.exists_stdVec_of_mem_roots hmem
  have hk : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp
  have hk0 : ((⟨0, by omega⟩ : Fin n)).val + 1 < n := by simp; omega
  have hstd : Symplectic.toStd n ((2 : ℤ) • (Pi.single ⟨0, by omega⟩ (1 : ℤ) : Fin n → ℤ)) =
      2 • Symplectic.stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference
        ⟨0, by omega⟩ ⟨1, by omega⟩ hk) := by
    rw [Symplectic.SpExtras.toStd_zsmul',
      Symplectic.SpExtras.stdVec_shortPos_eq (k := ⟨0, by omega⟩) hk0]
    rfl
  rw [hstd] at hr
  have h0 := congrFun hr ⟨0, by omega⟩
  have h1 := congrFun hr ⟨1, by omega⟩
  simp only [Pi.smul_apply, smul_eq_mul, Symplectic.stdVec, Pi.sub_apply, Pi.single_apply,
    Fin.zero_eta, Fin.mk_one, Fin.val_zero, Fin.val_one, zero_ne_one, ↓reduceIte,
    mul_zero, mul_one, one_mul, zero_sub, neg_mul] at h0 h1
  rcases r with i | i | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ | ⟨i, j, hij⟩ <;>
    simp only [Symplectic.stdVec, Pi.smul_apply, Pi.neg_apply, Pi.sub_apply, Pi.add_apply,
      Pi.single_apply, Fin.val_zero, Fin.val_one, smul_eq_mul, Fin.ext_iff] at h0 h1 <;>
    simp at h0 h1 <;> omega

theorem exists_conj_rootGroup_eq_matTransvGroup_PSp (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (hn : 1 ≤ n) (v w : Fin n ⊕ Fin n → F)
    (hvw : v ⬝ᵥ Matrix.mulVec
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w = 1) :
    ∃ β, β ∈ (Symplectic.rootDatum n F).roots ∧ GGLongRoot (Symplectic.rootDatum n F) β ∧ ∃ u :
      ↥(CFSG.Open.StatedSp n F),
      (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (CFSG.Open.StatedSp n F).subtype =
          matTransvGroup v
            (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            v) ∧
        (((Symplectic.rootDatum n F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
          matTransvGroup w
            (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            w) := by
  have hn0 : 0 < n := by omega
  obtain ⟨θ, hθ, hmax⟩ :=
    CFSG.StandardType.exists_maxHeight (D := Symplectic.rootDatum n F) hn0
  have hlθ : GGLongRoot (Symplectic.rootDatum n F) θ :=
    ⟨1, θ, hθ, hmax, by rw [map_one, Module.End.one_apply]⟩
  obtain ⟨v₀, w₀, hB₀, hX₀, hX₀'⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_matTransvGroup_eq_conj_rootGroup_Sp n F hθ hlθ 1
  obtain ⟨g, hgv, hgw⟩ := gSpr_exists_pair hn0 hB₀ hvw
  refine ⟨θ, hθ, hlθ, g, ?_, ?_⟩
  · rw [gSpr_map_conj_rootGroupDatum]
    have hX : ((Symplectic.rootDatum n F).rootGroup θ).map
        (CFSG.Open.StatedSp n F).subtype =
        matTransvGroup v₀ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v₀) := by
      rw [gSpr_conj_one, Subgroup.map_id] at hX₀
      exact hX₀
    rw [hX, gSpr_conj_matTransvGroup, hgv]
  · rw [gSpr_map_conj_rootGroupDatum]
    have hX : ((Symplectic.rootDatum n F).rootGroup (-θ)).map
        (CFSG.Open.StatedSp n F).subtype =
        matTransvGroup w₀ (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) w₀) := by
      rw [gSpr_conj_one, Subgroup.map_id] at hX₀'
      exact hX₀'
    rw [hX, gSpr_conj_matTransvGroup, hgw]

theorem exists_conj_rootGroup_eq_altSiegelGroup_PSp (n : ℕ) (F : Type) [Field F] [CharP F 2]
    (hn : 2 ≤ n) (a₁ a₂ b₁ b₂ : Fin n ⊕ Fin n → F)
    (h₁ : a₁ ⬝ᵥ Matrix.mulVec
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ = 1)
    (h₂ : a₂ ⬝ᵥ Matrix.mulVec
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 1)
    (h₀ : a₁ ⬝ᵥ Matrix.mulVec
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₂ = 0 ∧ b₁ ⬝ᵥ
      Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₂ = 0
      ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        b₂ = 0 ∧ a₂ ⬝ᵥ Matrix.mulVec
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ = 0) :
    ∃ β ∈ (Symplectic.rootDatum n F).roots, 2 • β ∉ (Symplectic.rootDatum n F).roots ∧ ∃ u :
      ↥(CFSG.Open.StatedSp n F),
      (((Symplectic.rootDatum n F).rootGroup β).map (MulAut.conj u).toMonoidHom).map
      (CFSG.Open.StatedSp n F).subtype = altSiegelGroup
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₁ a₂ ∧
        (((Symplectic.rootDatum n F).rootGroup (-β)).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
          altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            b₁ b₂ := by
  let k0 : Fin n := ⟨0, by omega⟩
  let k1 : Fin n := ⟨1, by omega⟩
  let β : Fin n → ℤ := Pi.single k0 1
  have hk : k0 ≠ k1 := by simp [k0, k1]
  have hk0 : k0.val + 1 < n := by simp [k0]; omega
  have hr : Symplectic.stdVec (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference k0 k1 hk) =
      Symplectic.toStd n β := by
    rw [Symplectic.SpExtras.stdVec_shortPos_eq (k := k0) hk0]
  have hβ : β ∈ (Symplectic.rootDatum n F).roots :=
    Symplectic.SpExtras.mem_roots_of_stdVec hr
  have h2β : (2 : ℤ) • β ∉ (Symplectic.rootDatum n F).roots :=
    gSpr_two_smul_short_not_mem hn
  have hstd : (Symplectic.rootGroup n F β).map (CFSG.Open.StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Pi.single (Sum.inl k0) 1) (Pi.single (Sum.inr k1) 1) :=
    gSpr_std_altSiegel_diff k0 k1 hk β hr
  have hr' : Symplectic.stdVec
      (TauCeti.GLSymplecticFin.RootSubgroupIndex.difference k1 k0 hk.symm) =
      Symplectic.toStd n (-β) := by
    rw [Symplectic.SpExtras.toStd_neg', ← hr]
    simp [Symplectic.stdVec]
  have hstd' : (Symplectic.rootGroup n F (-β)).map (CFSG.Open.StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Pi.single (Sum.inr k0) 1) (Pi.single (Sum.inl k1) 1) := by
    rw [← gSpr_altSiegelGroup_comm (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
      (Pi.single (Sum.inl k1) 1) (Pi.single (Sum.inr k0) 1)]
    exact gSpr_std_altSiegel_diff k1 k0 hk.symm (-β) hr'
  obtain ⟨h0a, h0b, h0ab, h0ba⟩ := h₀
  have h₂' : CFSG.ClassicalInvolution.Models.SymplecticPairs.form b₂ a₂ = 1 := by
    rw [CFSG.Timmesfeld.ARS.CaseM.form_eq_spForm,
      CFSG.Timmesfeld.ARS.CaseM.spForm_comm,
      ← CFSG.Timmesfeld.ARS.CaseM.form_eq_spForm]
    rw [show CFSG.ClassicalInvolution.Models.SymplecticPairs.form a₂ b₂ = 1 from h₂]
    simp [CharTwo.neg_eq]
  have o₄ : CFSG.ClassicalInvolution.Models.SymplecticPairs.form b₁ a₂ = 0 := by
    rw [CFSG.Timmesfeld.ARS.CaseM.form_eq_spForm,
      CFSG.Timmesfeld.ARS.CaseM.spForm_comm,
      ← CFSG.Timmesfeld.ARS.CaseM.form_eq_spForm]
    rw [show CFSG.ClassicalInvolution.Models.SymplecticPairs.form a₂ b₁ = 0 from h0ba]
    simp [CharTwo.neg_eq]
  obtain ⟨g, hga₁, hgb₁, hgb₂, hga₂⟩ :=
    CFSG.ClassicalInvolution.Models.SymplecticPairs.exists_sp_apply_eq_two_at hk
      a₁ b₁ b₂ a₂ h₁ h₂' h0ab h0a h0b o₄
  refine ⟨β, hβ, h2β, g, ?_, ?_⟩
  · change ((Symplectic.rootGroup n F β).map (MulAut.conj g).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) a₁ a₂
    rw [gSpr_map_conj_rootGroup, hstd, gSpr_conj_altSiegelGroup, hga₁, hga₂]
  · change ((Symplectic.rootGroup n F (-β)).map (MulAut.conj g).toMonoidHom).map
        (CFSG.Open.StatedSp n F).subtype =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) b₁ b₂
    rw [gSpr_map_conj_rootGroup, hstd', gSpr_conj_altSiegelGroup, hgb₁, hgb₂]

end CFSG.StandardType.ClassicalPosition
