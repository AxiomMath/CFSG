
module


public import CFSG.Monster.B.TwoA.Sp8.SubgeomStd
public import CFSG.Monster.B.TwoA.Sp8.SubgeomOrder

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.Code CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

attribute [local instance] parAction subgeomAction

attribute [local instance] parAction subgeomAction

@[expose] def stdSubFlag : Set ParGeom := {x | x ∈ stdParFlag ∧ parType x ≤ 4}

theorem stdObj_mem_subgeom
    (i : ℕ) (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    stdObj i h1 (by omega) ∈ subgeom :=
  mem_subgeom.2 ⟨h4, 1, Xgrp.one_mem, (conjSub_one _).symm⟩

theorem stdSubFlag_spec :
    stdSubFlag ⊆ subgeom ∧ IsParFlag stdSubFlag ∧
    parType '' stdSubFlag = Set.Icc 1 4 := by
  refine ⟨fun x hx => mem_subgeom.2 ⟨hx.2, 1, Xgrp.one_mem, ?_⟩,
    fun x hx y hy => stdParFlag_isParFlag.1 x hx.1 y hy.1, ?_⟩
  · rw [conjSub_one]
    exact hx.1
  · ext i
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(parType_bounds x).1, hx.2⟩
    · rintro ⟨h1, h4⟩
      exact ⟨stdObj i h1 (by omega), ⟨stdObj_mem i h1 (by omega), h4⟩, rfl⟩

theorem short_symplectic_subgeometry_building :
    (a8Vec (Echain 1) = span (ZMod 2) {bvec 8 1} ∧
      a8Vec (Echain 2) = span (ZMod 2) {bvec 8 1, bvec 8 2} ∧
      a8Vec (Echain 3) = span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4} ∧
      a8Vec (Echain 4) = span (ZMod 2) {bvec 8 1, bvec 8 2, bvec 8 4, bvec 8 24}) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 4 → Echain i ≤ A8 ∧ IsTotallyIsotropic b0 (a8Vec (Echain i)) ∧
      finrank (ZMod 2) (a8Vec (Echain i)) = i) ∧
    (∀ x ∈ subgeom, x.1.2 ≤ A8) ∧
    (∀ p : ℕ × Subgroup Dfull, p ∈ Subtype.val '' subgeom ↔
      1 ≤ p.1 ∧ p.1 ≤ 4 ∧ p.2 ≤ A8 ∧ Nat.card p.2 = 2 ^ p.1 ∧
        ∀ x y : A8, (x : Dfull) ∈ p.2 → (y : Dfull) ∈ p.2 → bA x y = 0) ∧
    (∀ x : subgeom, (subgeomEquiv x : Submodule (ZMod 2) V8) = a8Vec x.1.1.2) ∧
    (∀ W : isoSpaces, ((subgeomEquiv.symm W : subgeom) : ParGeom).1 =
      (finrank (ZMod 2) W.1, a8Grp W.1)) ∧
    (∀ W : Submodule (ZMod 2) V8, W ∈ isoSpaces ↔
      IsTotallyIsotropic b0 W ∧ 1 ≤ finrank (ZMod 2) W ∧ finrank (ZMod 2) W ≤ 4) ∧
    (∀ x : subgeom, parType x.1 = finrank (ZMod 2) (subgeomEquiv x : Submodule (ZMod 2) V8)) ∧
    (∀ x y : subgeom, x.1.1.2 ≤ y.1.1.2 ↔
      (subgeomEquiv x : Submodule (ZMod 2) V8) ≤ (subgeomEquiv y : Submodule (ZMod 2) V8)) ∧
    (∀ x y : subgeom, parInc x.1 y.1 ↔ x = y ∨
      (finrank (ZMod 2) (subgeomEquiv x : Submodule (ZMod 2) V8) ≠
          finrank (ZMod 2) (subgeomEquiv y : Submodule (ZMod 2) V8) ∧
        ((subgeomEquiv x : Submodule (ZMod 2) V8) ≤ (subgeomEquiv y : Submodule (ZMod 2) V8) ∨
          (subgeomEquiv y : Submodule (ZMod 2) V8) ≤ (subgeomEquiv x : Submodule (ZMod 2) V8)))) ∧
    b0.IsAlt ∧ b0.Nondegenerate ∧ finrank (ZMod 2) V8 = 8 ∧
    Nonempty (TauCeti.BilinForm.isometryGroup b0 ≃* CFSG.Assembly.LowTwoRank.StatedSp 4 (ZMod 2)) ∧
    (∃ (Φ : subgeom ≃ StdIsoSpaces) (σ : Xgrp →* CFSG.Assembly.LowTwoRank.StatedSp 4 (ZMod 2)),
      Function.Surjective σ ∧ σ.ker = Lgrp.subgroupOf Xgrp ∧
      (∀ x : subgeom, parType x.1 = finrank (ZMod 2) (Φ x).1) ∧
      (∀ x y : subgeom, x.1.1.2 ≤ y.1.1.2 ↔ (Φ x).1 ≤ (Φ y).1) ∧
      ∀ (x : Xgrp) (c : subgeom), (Φ (x • c)).1 = (Φ c).1.map
        (Matrix.mulVecLin ((σ x : GL (Fin 4 ⊕ Fin 4) (ZMod 2)) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (ZMod 2)))) ∧
    (∀ (x : Xgrp) (c : subgeom), ((x • c : subgeom) : ParGeom) = xToS x • c.1 ∧
      (subgeomEquiv (x • c) : Submodule (ZMod 2) V8) =
        (subgeomEquiv c : Submodule (ZMod 2) V8).map
          (((rhoXSp x : TauCeti.BilinForm.isometryGroup b0) : V8 ≃ₗ[ZMod 2] V8) :
            V8 →ₗ[ZMod 2] V8)) ∧
    Function.Surjective rhoXSp ∧
    (∀ F F' : Set ParGeom, F ⊆ subgeom → F' ⊆ subgeom → IsParFlag F → IsParFlag F' →
      parType '' F = parType '' F' → ∃ x : Xgrp, (xToS x • ·) '' F = F') ∧
    (∀ x : Xgrp, (∀ c ∈ subgeom, xToS x • c = c) ↔ (x : Dfull) ∈ Lgrp) ∧
    (MulAction.toPermHom Xgrp subgeom).ker = Lgrp.subgroupOf Xgrp ∧
    (CFSG.pCore 2 Xgrp).map Xgrp.subtype = Lgrp ∧
    Nonempty ((MulAction.toPermHom Xgrp subgeom).range ≃*
      CFSG.Assembly.LowTwoRank.StatedSp 4 (ZMod 2)) ∧
    (∀ d : Dfull, (fun p : ℕ × Subgroup Dfull => (p.1, conjSub d p.2)) '' (Subtype.val '' subgeom) =
      Subtype.val '' subgeom ↔ d ∈ Xgrp) ∧
    (∀ s : Shat, (s • ·) '' subgeom = subgeom ↔ (s : Dfull) ∈ Xgrp) ∧
    Xgrp ⊓ Kchain 1 = H1 ∧
    (stdSubFlag ⊆ subgeom ∧ IsParFlag stdSubFlag ∧ parType '' stdSubFlag = Set.Icc 1 4) ∧
    (∀ i : ℕ, 1 ≤ i → i ≤ 3 →
      ∃ P : Sylow 2 (Kchain i), ∀ g ∈ (P : Subgroup (Kchain i)), (g : Dfull) ∈ Xgrp) := by
  refine ⟨⟨a8Vec_Echain (i := 1) le_rfl (by norm_num), a8Vec_Echain (i := 2) (by norm_num)
      (by norm_num), a8Vec_Echain (i := 3) (by norm_num) (by norm_num),
      a8Vec_Echain (i := 4) (by norm_num) le_rfl⟩,
    fun i h1 h4 => ⟨Echain_le_A8 h1 h4, isotropic_a8Vec_Echain h1 h4, finrank_a8Vec_Echain h1 h4⟩,
    fun x hx => obj_le_A8 hx, fun p => by rw [image_val_subgeom]; exact mem_subgeomPairs_iff p,
    coe_subgeomEquiv, fun W => rfl, fun W => Iff.rfl,
    parType_eq_finrank, le_iff_subgeomEquiv, parInc_iff_subgeomEquiv, b0_isAlt, b0_nondegenerate,
    by rw [finrank_V8], nonempty_Sp_equiv, exists_subgeom_std_equiv,
    fun x c => ⟨coe_subgeom_smul x c, subgeomEquiv_smul x c⟩, rhoXSp_surjective,
    fun F F' hF hF' hFf hFf' ht => subgeom_flag_transitive hF hF' hFf hFf' ht,
    subgeom_kernel_iff, ?_, pCore_Xgrp,
    nonempty_range_toPermHom_equiv, ?_, stab_S_iff, Xgrp_inf_Kchain_one, stdSubFlag_spec,
    exists_sylow_X_inf_Kchain⟩
  · rw [ker_toPermHom, ker_rhoXSp]
  · intro d
    rw [image_val_subgeom]
    exact stab_D_iff d

end CFSG.Monster.B.TwoA.Sp8
