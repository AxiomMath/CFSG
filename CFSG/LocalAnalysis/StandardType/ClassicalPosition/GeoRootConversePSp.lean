module

public import CFSG.LocalAnalysis.StandardType.GGSixPositionDefs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2GeoSp
public import CFSG.Open.StatedDefs

public section

namespace CFSG.StandardType.ClassicalPosition

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

private theorem grcPSp_add_smul_dot {ι F : Type} [Fintype ι] [Field F]
    (s t : F) (x y z : ι → F) :
    (s • x + t • y) ⬝ᵥ z = s * (x ⬝ᵥ z) + t * (y ⬝ᵥ z) := by
  rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul, smul_eq_mul]

private theorem grcPSp_ne_zero_of_dot_eq_one {ι F : Type} [Fintype ι] [Field F]
    {x y : ι → F} (h : x ⬝ᵥ y = 1) : x ≠ 0 := by
  rintro rfl
  rw [zero_dotProduct] at h
  exact one_ne_zero h.symm

private theorem grcPSp_linearIndependent_pair_of_pairing {ι F : Type} [Fintype ι] [Field F]
    {a₁ a₂ b₁ b₂ : ι → F} (h₁ : a₁ ⬝ᵥ b₁ = 1) (h₂ : a₂ ⬝ᵥ b₂ = 1)
    (h0ba : a₂ ⬝ᵥ b₁ = 0) (h0ab : a₁ ⬝ᵥ b₂ = 0) :
    LinearIndependent F ![a₁, a₂] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  constructor
  · have h := congrArg (fun x => x ⬝ᵥ b₁) hst
    rw [grcPSp_add_smul_dot, zero_dotProduct, h₁, h0ba] at h
    simpa using h
  · have h := congrArg (fun x => x ⬝ᵥ b₂) hst
    rw [grcPSp_add_smul_dot, zero_dotProduct, h0ab, h₂] at h
    simpa using h

private theorem grcPSp_map_conj_rootGroup {n f : ℕ} {γ : Fin n → ℤ}
    (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f))) :
    (((Symplectic.rootGroup n (GaloisField 2 f) γ).map
        (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype) =
      (((Symplectic.rootGroup n (GaloisField 2 f) γ).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f))).toMonoidHom) := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

private theorem grcPSp_conj_one {n f : ℕ} :
    (MulAut.conj (1 : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))).toMonoidHom =
      MonoidHom.id _ := by
  ext x
  simp [MulAut.conj]

private theorem grcPSp_long_rootGroup_standard {n f : ℕ} {γ : Fin n → ℤ}
    (hγ : γ ∈ (Symplectic.rootDatum n (GaloisField 2 f)).roots)
    (hl : GGLongRoot (Symplectic.rootDatum n (GaloisField 2 f)) γ) :
    ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
      (Symplectic.rootGroup n (GaloisField 2 f) γ).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
      matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
  obtain ⟨v, w, hvw, hX, _⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_matTransvGroup_eq_conj_rootGroup_Sp n
      (GaloisField 2 f) hγ hl 1
  refine ⟨v, grcPSp_ne_zero_of_dot_eq_one hvw, ?_⟩
  rw [grcPSp_conj_one, Subgroup.map_id] at hX
  exact hX

private theorem grcPSp_J_transpose {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    Matrix.transpose (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      Matrix.fromBlocks 0 1 (-1) 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply, CharTwo.neg_eq, eq_comm]

private theorem grcPSp_J_mul_self {n : ℕ} {F : Type} [Field F] [CharP F 2] :
    (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      Matrix.fromBlocks 0 1 (-1) 0 = 1 := by
  rw [Matrix.fromBlocks_multiply]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.one_apply, CharTwo.neg_eq]

private theorem grcPSp_mat_mul_inv {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (Symplectic.SpExtras.mat n F u) * (Symplectic.SpExtras.mat n F u⁻¹) = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

private theorem grcPSp_mat_inv_mul {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (Symplectic.SpExtras.mat n F u⁻¹) * (Symplectic.SpExtras.mat n F u) = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

private theorem grcPSp_mat_inv_eq {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    (Symplectic.SpExtras.mat n F u⁻¹) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        Matrix.transpose (Symplectic.SpExtras.mat n F u) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
  have hsp : Matrix.transpose (Symplectic.SpExtras.mat n F u) *
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (Symplectic.SpExtras.mat n F u) =
      Matrix.fromBlocks 0 1 (-1) 0 :=
    (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2
  have h2 : ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      Matrix.transpose (Symplectic.SpExtras.mat n F u) *
      Matrix.fromBlocks 0 1 (-1) 0) *
        (Symplectic.SpExtras.mat n F u) = 1 := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc _ (Matrix.fromBlocks 0 1 (-1) 0), hsp, grcPSp_J_mul_self]
  exact (left_inv_eq_right_inv h2 (grcPSp_mat_mul_inv u)).symm

private theorem grcPSp_transpose_inv_mul_J {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) :
    Matrix.transpose (Symplectic.SpExtras.mat n F u⁻¹) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (Symplectic.SpExtras.mat n F u) := by
  have htrans : Matrix.transpose (Symplectic.SpExtras.mat n F u⁻¹) =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
        (Symplectic.SpExtras.mat n F u) *
        (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) := by
    rw [grcPSp_mat_inv_eq, Matrix.transpose_mul, Matrix.transpose_mul, grcPSp_J_transpose,
      Matrix.transpose_transpose]
    noncomm_ring
  rw [htrans]
  change ((Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (Symplectic.SpExtras.mat n F u) *
      Matrix.fromBlocks 0 1 (-1) 0) * Matrix.fromBlocks 0 1 (-1) 0 =
    Matrix.fromBlocks 0 1 (-1) 0 * Symplectic.SpExtras.mat n F u
  rw [Matrix.mul_assoc ((Matrix.fromBlocks 0 1 (-1) 0) *
      (Symplectic.SpExtras.mat n F u))
      (Matrix.fromBlocks 0 1 (-1) 0), grcPSp_J_mul_self, Matrix.mul_one]

private theorem grcPSp_conj_vecMulVec {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y : Fin n ⊕ Fin n → F) (c : F)
    (h : GL (Fin n ⊕ Fin n) F)
    (hh : (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = 1 + c • Matrix.vecMulVec x y) :
    (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • Matrix.vecMulVec
        (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x)
        (Matrix.vecMul y (Symplectic.SpExtras.mat n F u⁻¹)) := by
  rw [show (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h =
      (u : GL (Fin n ⊕ Fin n) F) * h * (u : GL (Fin n ⊕ Fin n) F)⁻¹ from rfl]
  rw [Units.val_mul, Units.val_mul]
  change (Symplectic.SpExtras.mat n F u) *
      (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (Symplectic.SpExtras.mat n F u⁻¹) = _
  rw [hh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, grcPSp_mat_mul_inv, zero_add]

private theorem grcPSp_conj_matTransvGroup_le {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) (v : Fin n ⊕ Fin n → F) :
    (matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v)).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom ≤
      matTransvGroup (Matrix.mulVec (Symplectic.SpExtras.mat n F u) v)
        (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) v)) := by
  have hJU := grcPSp_transpose_inv_mul_J u
  rw [matTransvGroup, MonoidHom.map_closure, Subgroup.closure_le]
  rintro g ⟨h, ⟨c, hc⟩, rfl⟩
  refine Subgroup.subset_closure ⟨c, ?_⟩
  change (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
  rw [grcPSp_conj_vecMulVec u v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v) c h hc]
  congr 2
  rw [← Matrix.transpose_transpose (Symplectic.SpExtras.mat n F u⁻¹),
    Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]

private theorem grcPSp_conj_matTransvGroup_gen {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) (v : Fin n ⊕ Fin n → F) :
    (matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) v)).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom =
      matTransvGroup (Matrix.mulVec (Symplectic.SpExtras.mat n F u) v)
        (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) v)) := by
  apply le_antisymm (grcPSp_conj_matTransvGroup_le u v)
  have hle := grcPSp_conj_matTransvGroup_le (u := u⁻¹)
    (v := Matrix.mulVec (Symplectic.SpExtras.mat n F u) v)
  have hveq : Matrix.mulVec (Symplectic.SpExtras.mat n F u⁻¹)
      (Matrix.mulVec (Symplectic.SpExtras.mat n F u) v) = v := by
    rw [Matrix.mulVec_mulVec, grcPSp_mat_inv_mul, Matrix.one_mulVec]
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
  have hmap := Subgroup.map_mono
    (f := (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom) hle
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at hmap
  exact hmap

private theorem grcPSp_conj_matTransvGroup {n f : ℕ}
    (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (v : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    (matTransvGroup v (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v)).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f))).toMonoidHom =
      matTransvGroup (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) v)
        (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
          (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) v)) := by
  exact grcPSp_conj_matTransvGroup_gen u v

private theorem grcPSp_short_rootGroup_standard {n f : ℕ} {γ : Fin n → ℤ}
    (hγ : γ ∈ (Symplectic.rootDatum n (GaloisField 2 f)).roots)
    (hl : ¬ GGLongRoot (Symplectic.rootDatum n (GaloisField 2 f)) γ) :
    ∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      (Symplectic.rootGroup n (GaloisField 2 f) γ).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ := by
  obtain ⟨a₁, a₂, b₁, b₂, h₁, h₂, h₀, hX, _⟩ :=
    CFSG.StandardType.LieKnownR2.Geo.exists_altSiegelGroup_eq_conj_rootGroup_Sp n
      (GaloisField 2 f) hγ hl 1
  obtain ⟨h0a, h0b, h0ab, h0ba⟩ := h₀
  rw [grcPSp_conj_one, Subgroup.map_id] at hX
  refine ⟨a₁, a₂, grcPSp_ne_zero_of_dot_eq_one h₁, grcPSp_ne_zero_of_dot_eq_one h₂,
    ?_, h0a, hX⟩
  exact grcPSp_linearIndependent_pair_of_pairing
    (b₁ := Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₁)
    (b₂ := Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) b₂)
    h₁ h₂ h0ba h0ab

private theorem grcPSp_vecMul_eq_transpose_mulVec {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (z : Fin n ⊕ Fin n → F) :
    Matrix.vecMul z A = Matrix.mulVec (Matrix.transpose A) z := by
  have h := Matrix.vecMul_transpose (A := Matrix.transpose A) z
  rwa [Matrix.transpose_transpose] at h

private theorem grcPSp_conj_add_vecMulVec {n : ℕ} {F : Type} [Field F]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y x' y' : Fin n ⊕ Fin n → F) (c : F)
    (h : GL (Fin n ⊕ Fin n) F)
    (hh : (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.vecMulVec x y + Matrix.vecMulVec x' y')) :
    (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) =
      1 + c • (Matrix.vecMulVec
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x)
          (Matrix.vecMul y (Symplectic.SpExtras.mat n F u⁻¹)) +
        Matrix.vecMulVec (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x')
          (Matrix.vecMul y' (Symplectic.SpExtras.mat n F u⁻¹))) := by
  rw [show (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h =
      (u : GL (Fin n ⊕ Fin n) F) * h * (u : GL (Fin n ⊕ Fin n) F)⁻¹ from rfl]
  rw [Units.val_mul, Units.val_mul]
  change (Symplectic.SpExtras.mat n F u) *
      (h : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
      (Symplectic.SpExtras.mat n F u⁻¹) = _
  rw [hh]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, grcPSp_mat_mul_inv, zero_add]

private theorem grcPSp_conj_altSiegelGroup_gen {n : ℕ} {F : Type} [Field F] [CharP F 2]
    (u : ↥(CFSG.Open.StatedSp n F)) (x y : Fin n ⊕ Fin n → F) :
    (altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x y).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) F)).toMonoidHom =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
        (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x)
        (Matrix.mulVec (Symplectic.SpExtras.mat n F u) y) := by
  have hJU := grcPSp_transpose_inv_mul_J u
  rw [altSiegelGroup, MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨h, ⟨c, hc⟩, rfl⟩
    refine ⟨c, ?_⟩
    change (((MulAut.conj (u : GL (Fin n ⊕ Fin n) F)) h : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = _
    have e1 : Matrix.vecMul (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y)
        (Symplectic.SpExtras.mat n F u⁻¹) =
        Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) y) := by
      rw [← Matrix.transpose_transpose (Symplectic.SpExtras.mat n F u⁻¹),
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]
    have e2 : Matrix.vecMul (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x)
        (Symplectic.SpExtras.mat n F u⁻¹) =
        Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x) := by
      rw [← Matrix.transpose_transpose (Symplectic.SpExtras.mat n F u⁻¹),
        Matrix.vecMul_transpose, Matrix.mulVec_mulVec, hJU, ← Matrix.mulVec_mulVec]
    rw [grcPSp_conj_add_vecMulVec u x (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y)
        y (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x) c h hc, e1, e2]
  · rintro ⟨c, hg⟩
    refine ⟨(MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ g, ⟨c, ?_⟩, ?_⟩
    · have hle := grcPSp_conj_add_vecMulVec (u := u⁻¹)
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x)
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            (Matrix.mulVec (Symplectic.SpExtras.mat n F u) y))
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) y)
          (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x)) c g hg
      have hcomp : (MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ =
          MulAut.conj ((u⁻¹ : ↥(CFSG.Open.StatedSp n F)) :
            GL (Fin n ⊕ Fin n) F) := (map_inv _ _).symm
      have e1 : Matrix.mulVec (Symplectic.SpExtras.mat n F u⁻¹)
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x) = x := by
        rw [Matrix.mulVec_mulVec, grcPSp_mat_inv_mul, Matrix.one_mulVec]
      have e2 : Matrix.vecMul (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            (Matrix.mulVec (Symplectic.SpExtras.mat n F u) y))
            (Symplectic.SpExtras.mat n F ((u⁻¹)⁻¹)) =
          Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) y := by
        rw [show (Symplectic.SpExtras.mat n F (u⁻¹)⁻¹) =
            (Symplectic.SpExtras.mat n F u) from by rw [inv_inv],
          grcPSp_vecMul_eq_transpose_mulVec (Symplectic.SpExtras.mat n F u),
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          show Matrix.transpose (Symplectic.SpExtras.mat n F u) *
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            (Symplectic.SpExtras.mat n F u) =
            Matrix.fromBlocks 0 1 (-1) 0 from
          (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2]
      have e3 : Matrix.mulVec (Symplectic.SpExtras.mat n F u⁻¹)
          (Matrix.mulVec (Symplectic.SpExtras.mat n F u) y) = y := by
        rw [Matrix.mulVec_mulVec, grcPSp_mat_inv_mul, Matrix.one_mulVec]
      have e4 : Matrix.vecMul (Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F)
            (Matrix.mulVec (Symplectic.SpExtras.mat n F u) x))
            (Symplectic.SpExtras.mat n F ((u⁻¹)⁻¹)) =
          Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) x := by
        rw [show (Symplectic.SpExtras.mat n F (u⁻¹)⁻¹) =
            (Symplectic.SpExtras.mat n F u) from by rw [inv_inv],
          grcPSp_vecMul_eq_transpose_mulVec (Symplectic.SpExtras.mat n F u),
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
          show Matrix.transpose (Symplectic.SpExtras.mat n F u) *
            (Matrix.fromBlocks 0 1 (-1) 0 : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) *
            (Symplectic.SpExtras.mat n F u) =
            Matrix.fromBlocks 0 1 (-1) 0 from
          (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2]
      rw [← hcomp] at hle
      rw [hle, e1, e2, e3, e4]
    · change (MulAut.conj (u : GL (Fin n ⊕ Fin n) F))
          ((MulAut.conj (u : GL (Fin n ⊕ Fin n) F))⁻¹ g) = g
      rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]

private theorem grcPSp_conj_altSiegelGroup {n f : ℕ}
    (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    (x y : (Fin n ⊕ Fin n) → GaloisField 2 f) :
    (altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) x y).map
        (MulAut.conj (u : GL (Fin n ⊕ Fin n) (GaloisField 2 f))).toMonoidHom =
      altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) x)
        (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) y) := by
  exact grcPSp_conj_altSiegelGroup_gen u x y

private theorem grcPSp_mat_mulVec_ne_zero {n f : ℕ}
    (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    {v : (Fin n ⊕ Fin n) → GaloisField 2 f} (hv : v ≠ 0) :
    Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) v ≠ 0 := by
  intro h
  apply hv
  have h' := congrArg (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u⁻¹)) h
  rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, grcPSp_mat_inv_mul, Matrix.one_mulVec] at h'
  exact h'

private theorem grcPSp_dot_mulVec_assoc {n : ℕ} {F : Type} [Field F]
    (A : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (z y : Fin n ⊕ Fin n → F) :
    Matrix.mulVec A z ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Matrix.mulVec A y) =
      z ⬝ᵥ Matrix.mulVec (Matrix.transpose A * (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * A) y := by
  rw [← Matrix.toBilin'_apply' (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) (Matrix.mulVec A z) (Matrix.mulVec A y)]
  rw [← Matrix.toBilin'_apply' (Matrix.transpose A * (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) * A) z y]
  rw [← Matrix.toBilin'_comp (Matrix.fromBlocks 0 1 (-1) 0 :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) A A]
  rfl

private theorem grcPSp_map_mulVec_preserves {n f : ℕ}
    (u : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)))
    {a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f}
    (ha₁ : a₁ ≠ 0) (ha₂ : a₂ ≠ 0)
    (hli : LinearIndependent (GaloisField 2 f) ![a₁, a₂])
    (horth : a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0) :
    (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₁ ≠ 0) ∧
    (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₂ ≠ 0) ∧
    LinearIndependent (GaloisField 2 f) ![
      Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₁,
      Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₂] ∧
    (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₁) ⬝ᵥ
      Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
        (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₂) = 0 := by
  refine ⟨grcPSp_mat_mulVec_ne_zero u ha₁, grcPSp_mat_mulVec_ne_zero u ha₂, ?_, ?_⟩
  · have hker : (Matrix.mulVecLin (Symplectic.SpExtras.mat n (GaloisField 2 f) u)).ker = ⊥ := by
      rw [Matrix.ker_mulVecLin_eq_bot_iff]
      intro w hw
      have h' := congrArg (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u⁻¹)) hw
      rw [Matrix.mulVec_zero, Matrix.mulVec_mulVec, grcPSp_mat_inv_mul, Matrix.one_mulVec] at h'
      exact h'
    have h := hli.map' (Matrix.mulVecLin (Symplectic.SpExtras.mat n (GaloisField 2 f) u)) hker
    have hfun : (Matrix.mulVecLin (Symplectic.SpExtras.mat n (GaloisField 2 f) u)) ∘ ![a₁, a₂] =
        ![Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₁,
          Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₂] := by
      ext i
      fin_cases i <;> simp [Function.comp_apply, Matrix.mulVecLin_apply]
    rw [hfun] at h
    exact h
  · have hsp : Matrix.transpose (Symplectic.SpExtras.mat n (GaloisField 2 f) u) *
        (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
        (Symplectic.SpExtras.mat n (GaloisField 2 f) u) =
        Matrix.fromBlocks 0 1 (-1) 0 :=
      (CFSG.Open.StatedAPI.mem_statedSp_iff).1 u.2
    calc
      (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₁) ⬝ᵥ
          Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f))
            (Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u) a₂)
        = a₁ ⬝ᵥ Matrix.mulVec (Matrix.transpose (Symplectic.SpExtras.mat n (GaloisField 2 f) u) *
            (Matrix.fromBlocks 0 1 (-1) 0 :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) *
            (Symplectic.SpExtras.mat n (GaloisField 2 f) u)) a₂ :=
          grcPSp_dot_mulVec_assoc _ _ _
      _ = a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ := by rw [hsp]
      _ = 0 := horth

theorem exists_matTransvGroup_eq_rootGroup_PSp
    (n f
        : ℕ)
    {γ : Fin (ggU .PSp n f).D.rank → ℤ} (hγ : γ ∈ (ggU .PSp n f).D.roots)
    (hl : GGLongRoot (ggU .PSp n f).D γ) (u : (ggU .PSp n f).K) :
    ∃ v : (Fin n ⊕ Fin n) → GaloisField 2 f, v ≠ 0 ∧
      (((ggU .PSp n f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        matTransvGroup v (Matrix.mulVec
          (Matrix.fromBlocks 0 1 (-1) 0 :
            Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) v) := by
  let u' : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) := u
  obtain ⟨v, hv, hX⟩ := grcPSp_long_rootGroup_standard (n := n) (f := f) hγ hl
  refine ⟨Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u') v, ?_, ?_⟩
  · exact grcPSp_mat_mulVec_ne_zero u' hv
  · exact (grcPSp_map_conj_rootGroup u').trans
      ((congrArg (fun H => H.map
          (MulAut.conj (u' : GL (Fin n ⊕ Fin n) (GaloisField 2 f))).toMonoidHom) hX).trans
        (grcPSp_conj_matTransvGroup u' v))

theorem exists_altSiegelGroup_eq_rootGroup_PSp
    (n f
        : ℕ)
    {γ : Fin (ggU .PSp n f).D.rank → ℤ} (hγ : γ ∈ (ggU .PSp n f).D.roots)
    (hl : ¬ GGLongRoot (ggU .PSp n f).D γ) (u : (ggU .PSp n f).K) :
    ∃ a₁ a₂ : (Fin n ⊕ Fin n) → GaloisField 2 f, a₁ ≠ 0 ∧ a₂ ≠ 0 ∧
      LinearIndependent (GaloisField 2 f) ![a₁, a₂] ∧
      a₁ ⬝ᵥ Matrix.mulVec (Matrix.fromBlocks 0 1 (-1) 0 :
        Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₂ = 0 ∧
      (((ggU .PSp n f).D.rootGroup γ).map (MulAut.conj u).toMonoidHom).map
        (CFSG.Open.StatedSp n (GaloisField 2 f)).subtype =
        altSiegelGroup (Matrix.fromBlocks 0 1 (-1) 0 :
          Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) (GaloisField 2 f)) a₁ a₂ := by
  let u' : ↥(CFSG.Open.StatedSp n (GaloisField 2 f)) := u
  obtain ⟨a₁, a₂, ha₁, ha₂, hli, horth, hX⟩ :=
    grcPSp_short_rootGroup_standard (n := n) (f := f) hγ hl
  obtain ⟨hb₁, hb₂, hbli, hborth⟩ := grcPSp_map_mulVec_preserves u' ha₁ ha₂ hli horth
  refine ⟨Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u') a₁,
    Matrix.mulVec (Symplectic.SpExtras.mat n (GaloisField 2 f) u') a₂,
    hb₁, hb₂, hbli, hborth, ?_⟩
  exact (grcPSp_map_conj_rootGroup u').trans
    ((congrArg (fun H => H.map
        (MulAut.conj (u' : GL (Fin n ⊕ Fin n) (GaloisField 2 f))).toMonoidHom) hX).trans
      (grcPSp_conj_altSiegelGroup u' a₁ a₂))

end CFSG.StandardType.ClassicalPosition
