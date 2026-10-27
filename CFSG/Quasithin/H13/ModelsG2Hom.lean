module

public import CFSG.Quasithin.H13.ModelsG2Zorn
public import CFSG.Quasithin.Background.G2UColumns

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U
open scoped Matrix

section Compress

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
  [DecidableEq n] (E : Matrix m n R) (F : Matrix n m R) (J : Matrix m m R)

omit [DecidableEq m] [DecidableEq n] in
theorem compress_mul {M N : Matrix n n R} (hM : F * E * M * F = M * F)
    (hN : F * E * N * F = N * F) : F * E * (M * N) * F = M * N * F := by
  calc F * E * (M * N) * F = F * E * M * (N * F) := by simp only [Matrix.mul_assoc]
    _ = F * E * M * (F * E * N * F) := by rw [hN]
    _ = F * E * M * F * (E * N * F) := by simp only [Matrix.mul_assoc]
    _ = M * F * (E * N * F) := by rw [hM]
    _ = M * (F * E * N * F) := by simp only [Matrix.mul_assoc]
    _ = M * N * F := by rw [hN, Matrix.mul_assoc]

@[expose] def compressStab (hFEF : F * E * F = F) : Subgroup (GL n R) where
  carrier := {g | F * E * (g : Matrix n n R) * F = (g : Matrix n n R) * F ∧
    F * E * ((g⁻¹ : GL n R) : Matrix n n R) * F = ((g⁻¹ : GL n R) : Matrix n n R) * F}
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact compress_mul E F hg.1 hh.1
    · rw [mul_inv_rev, Units.val_mul]
      exact compress_mul E F hh.2 hg.2
  one_mem' := by
    refine ⟨?_, ?_⟩ <;> simp [hFEF]
  inv_mem' {g} hg := by
    refine ⟨hg.2, ?_⟩
    rw [inv_inv]
    exact hg.1

omit [DecidableEq m] in
theorem mem_compressStab {hFEF : F * E * F = F} {g : GL n R} :
    g ∈ compressStab E F hFEF ↔ F * E * (g : Matrix n n R) * F = (g : Matrix n n R) * F ∧
      F * E * ((g⁻¹ : GL n R) : Matrix n n R) * F = ((g⁻¹ : GL n R) : Matrix n n R) * F :=
  Iff.rfl

omit [DecidableEq n] in
theorem fEF_eq (hFJ : F * J = 0) (hJEF : J + E * F = 1) : F * E * F = F := by
  have h : F * (J + E * F) = F := by rw [hJEF, Matrix.mul_one]
  rwa [Matrix.mul_add, hFJ, zero_add, ← Matrix.mul_assoc] at h

omit [DecidableEq n] in
theorem jJ_eq (hJE : J * E = 0) (hJEF : J + E * F = 1) : J * J = J := by
  have h : J * (J + E * F) = J := by rw [hJEF, Matrix.mul_one]
  rwa [Matrix.mul_add, ← Matrix.mul_assoc, hJE, Matrix.zero_mul, add_zero] at h

@[expose] def compressHom (hJE : J * E = 0) (hFJ : F * J = 0) (hJEF : J + E * F = 1) :
    compressStab E F (fEF_eq E F J hFJ hJEF) →* Matrix m m R where
  toFun g := J + E * ((g : GL n R) : Matrix n n R) * F
  map_one' := by simpa using hJEF
  map_mul' g h := by
    have hh : F * E * ((h : GL n R) : Matrix n n R) * F = ((h : GL n R) : Matrix n n R) * F :=
      h.2.1
    rw [Subgroup.coe_mul, Units.val_mul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      jJ_eq E F J hJE hJEF]
    have h1 : J * (E * ((h : GL n R) : Matrix n n R) * F) = 0 := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hJE, Matrix.zero_mul, Matrix.zero_mul]
    have h2 : E * ((g : GL n R) : Matrix n n R) * F * J = 0 := by
      rw [Matrix.mul_assoc, hFJ, Matrix.mul_zero]
    have h3 : E * ((g : GL n R) : Matrix n n R) * F * (E * ((h : GL n R) : Matrix n n R) * F) =
        E * (((g : GL n R) : Matrix n n R) * ((h : GL n R) : Matrix n n R)) * F := by
      calc E * ((g : GL n R) : Matrix n n R) * F * (E * ((h : GL n R) : Matrix n n R) * F)
          = E * ((g : GL n R) : Matrix n n R) * (F * E * ((h : GL n R) : Matrix n n R) * F) := by
            simp only [Matrix.mul_assoc]
        _ = E * (((g : GL n R) : Matrix n n R) * ((h : GL n R) : Matrix n n R)) * F := by
            rw [hh]
            simp only [Matrix.mul_assoc]
    rw [h1, h2, h3, add_zero, zero_add]

end Compress

section ZornMat

variable {K : Type*} [CommRing K]

@[expose] def zornMatEquiv (g : GL (Fin 8) K) : quasithinZorn K ≃ₗ[K] quasithinZorn K :=
  LinearEquiv.ofLinearMap (zornMatLin (g : Matrix (Fin 8) (Fin 8) K))
    (zornMatLin ((g⁻¹ : GL (Fin 8) K) : Matrix (Fin 8) (Fin 8) K))
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← zornMatLin_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        zornMatLin_one, LinearMap.id_apply])
    (LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, ← zornMatLin_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        zornMatLin_one, LinearMap.id_apply])

theorem zornMatEquiv_apply (g : GL (Fin 8) K) (x : quasithinZorn K) :
    zornMatEquiv g x = zornMatLin (g : Matrix (Fin 8) (Fin 8) K) x :=
  rfl

variable (K) in
@[expose] def zornMatHom : GL (Fin 8) K →* (quasithinZorn K ≃ₗ[K] quasithinZorn K) where
  toFun := zornMatEquiv
  map_one' := LinearEquiv.ext fun x => by
    rw [zornMatEquiv_apply, Units.val_one, zornMatLin_one]
    rfl
  map_mul' g h := LinearEquiv.ext fun x => by
    rw [zornMatEquiv_apply, Units.val_mul, zornMatLin_mul]
    rfl

@[expose] def IsZornAutoMat (G : Matrix (Fin 8) (Fin 8) K) : Prop :=
  ∀ i j : Fin 8, zornMatLin G (quasithinZornMul (zornBasisVec i) (zornBasisVec j)) =
    quasithinZornMul (zornMatLin G (zornBasisVec i)) (zornMatLin G (zornBasisVec j))

theorem zornMatHom_mem_zornAut {g : GL (Fin 8) K}
    (hg : IsZornAutoMat (g : Matrix (Fin 8) (Fin 8) K)) : zornMatHom K g ∈ zornAut K :=
  fun x y => zornMatLin_mul_of_basis _ hg x y

end ZornMat

@[expose] def zornE : Matrix (Fin 8) (Fin 14) (ZMod 3) :=
  !![0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0;
    0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0]

@[expose] def zornF : Matrix (Fin 14) (Fin 8) (ZMod 3) :=
  !![0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 1, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 1, 0, 0;
    0, 0, 0, 0, 0, 0, 1, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0, 0, 1;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 2, 0, 0, 0, 0;
    0, 0, 1, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 2, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0]

@[expose] def zornJ : Matrix (Fin 8) (Fin 8) (ZMod 3) :=
  !![2, 0, 0, 0, 0, 0, 0, 2;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    0, 0, 0, 0, 0, 0, 0, 0;
    2, 0, 0, 0, 0, 0, 0, 2]

theorem zornJ_mul_zornE : zornJ * zornE = 0 := by
  decide +kernel

theorem zornF_mul_zornJ : zornF * zornJ = 0 := by
  decide +kernel

theorem zornJ_add_zornE_mul_zornF : zornJ + zornE * zornF = 1 := by
  decide +kernel

theorem zornF_mul_zornE_mul_zornF : zornF * zornE * zornF = zornF :=
  fEF_eq zornE zornF zornJ zornF_mul_zornJ zornJ_add_zornE_mul_zornF

theorem XMat_mul_neg : ∀ (i : Fin Tag.G2.rank) (t : ZMod 3),
    XMat (ZMod 3) i t * XMat (ZMod 3) i (-t) = 1 ∧
      YMat (ZMod 3) i t * YMat (ZMod 3) i (-t) = 1 := by
  decide +kernel

theorem XMat_compress : ∀ (i : Fin Tag.G2.rank) (t : ZMod 3),
    zornF * zornE * XMat (ZMod 3) i t * zornF = XMat (ZMod 3) i t * zornF ∧
      zornF * zornE * YMat (ZMod 3) i t * zornF = YMat (ZMod 3) i t * zornF := by
  decide +kernel

theorem XMat_isZornAutoMat : ∀ (i : Fin Tag.G2.rank) (t : ZMod 3),
    IsZornAutoMat (zornJ + zornE * XMat (ZMod 3) i t * zornF) ∧
      IsZornAutoMat (zornJ + zornE * YMat (ZMod 3) i t * zornF) := by
  unfold IsZornAutoMat
  decide +kernel

theorem compress_XMat_ne : zornMatLin (zornJ + zornE * XMat (ZMod 3) (ix 0) 1 * zornF)
    (zornBasisVec 2) ≠ zornBasisVec 2 := by
  decide +kernel

end CFSG.Quasithin.H13
