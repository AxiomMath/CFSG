module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearRingEquiv

namespace CFSG
end CFSG
open CFSG

/-!
# Coefficient automorphisms of projective linear groups

A coefficient-ring automorphism acts entrywise on `PSL₂` and `PGL₂`.
This file packages those actions as faithful homomorphisms and proves that
they commute with the canonical inclusion `PSL₂ → PGL₂`.

These are the field-automorphism coordinates needed for the eventual
construction of `PΓL(2,K)` inside `Aut(PSL₂(K))`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem specialLinearGroup_map_transvection
    {K : Type u} [Field K] (e : K ≃+* K)
    {i j : Fin 2} (hij : i ≠ j) (t : K) :
    Matrix.SpecialLinearGroup.map e.toRingHom
        (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij (e t) := by
  classical
  ext a b
  by_cases h : i = a ∧ j = b <;>
    simp [Matrix.SpecialLinearGroup.transvection_coe, Matrix.one_apply, h]

/-- The coefficient automorphism action on `PSL₂(K)`. -/
@[expose]
public def psl2FieldAut (K : Type u) [CommRing K] :
    (K ≃+* K) →* MulAut (PSL2 K) where
  toFun := psl2RingEquiv
  map_one' := psl2RingEquiv_one K
  map_mul' := psl2RingEquiv_mul

@[simp]
public theorem psl2FieldAut_apply
    (K : Type u) [CommRing K] (e : K ≃+* K) (x : PSL2 K) :
    psl2FieldAut K e x = psl2RingEquiv e x := rfl

/-- The coefficient automorphism action on `PGL₂(K)`. -/
@[expose]
public def pgl2FieldAut (K : Type u) [CommRing K] :
    (K ≃+* K) →* MulAut (PGL2 K) where
  toFun := pgl2RingEquiv
  map_one' := pgl2RingEquiv_one K
  map_mul' := pgl2RingEquiv_mul

public theorem pgl2FieldAut_apply
    (K : Type u) [CommRing K] (e : K ≃+* K) (x : PGL2 K) :
    pgl2FieldAut K e x = pgl2RingEquiv e x := rfl

/-- A field automorphism is determined by its entrywise action on `PSL₂`.
The elementary transvections recover every coefficient. -/
public theorem psl2FieldAut_injective (K : Type u) [Field K] :
    Function.Injective (psl2FieldAut K) := by
  intro e f hef
  apply RingEquiv.ext
  intro t
  let i : Fin 2 := 0
  let j : Fin 2 := 1
  have hij : i ≠ j := by decide
  let u : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.transvection hij t
  have hq := DFunLike.congr_fun hef
    (QuotientGroup.mk' (Subgroup.center _) u)
  change psl2RingEquiv e (QuotientGroup.mk' (Subgroup.center _) u) =
    psl2RingEquiv f (QuotientGroup.mk' (Subgroup.center _) u) at hq
  rw [psl2RingEquiv_mk, psl2RingEquiv_mk,
    specialLinearGroup_map_transvection,
    specialLinearGroup_map_transvection] at hq
  have hcent :
      Matrix.SpecialLinearGroup.transvection hij (e t) /
          Matrix.SpecialLinearGroup.transvection hij (f t) ∈
        Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have hdiff :
      Matrix.SpecialLinearGroup.transvection hij (e t) /
          Matrix.SpecialLinearGroup.transvection hij (f t) =
        Matrix.SpecialLinearGroup.transvection hij (e t - f t) := by
    rw [div_eq_mul_inv, Matrix.SpecialLinearGroup.transvection_inv,
      ← Matrix.SpecialLinearGroup.transvection_add, sub_eq_add_neg]
  rw [hdiff, Matrix.SpecialLinearGroup.transvection_mem_center_iff] at hcent
  exact sub_eq_zero.mp hcent

/-- A field automorphism is determined by its entrywise action on `PGL₂`.
Again the elementary transvections recover every coefficient. -/
public theorem pgl2FieldAut_injective (K : Type u) [Field K] :
    Function.Injective (pgl2FieldAut K) := by
  intro e f hef
  apply RingEquiv.ext
  intro t
  let i : Fin 2 := 0
  let j : Fin 2 := 1
  have hij : i ≠ j := by decide
  let ue : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.transvection hij (e t)
  let uf : Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.transvection hij (f t)
  let u : Matrix.GeneralLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.transvection hij t)
  have hq := DFunLike.congr_fun hef
    (QuotientGroup.mk' (Subgroup.center _) u)
  change pgl2RingEquiv e (QuotientGroup.mk' (Subgroup.center _) u) =
    pgl2RingEquiv f (QuotientGroup.mk' (Subgroup.center _) u) at hq
  rw [pgl2RingEquiv_mk, pgl2RingEquiv_mk] at hq
  have hmap_e : Matrix.GeneralLinearGroup.map e.toRingHom u =
      Matrix.SpecialLinearGroup.toGL ue := by
    classical
    ext a b
    by_cases h : i = a ∧ j = b <;>
      simp [u, ue, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.one_apply, h]
  have hmap_f : Matrix.GeneralLinearGroup.map f.toRingHom u =
      Matrix.SpecialLinearGroup.toGL uf := by
    classical
    ext a b
    by_cases h : i = a ∧ j = b <;>
      simp [u, uf, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.one_apply, h]
  rw [hmap_e, hmap_f] at hq
  have hcentGL :
      Matrix.SpecialLinearGroup.toGL ue /
          Matrix.SpecialLinearGroup.toGL uf ∈
        Subgroup.center (Matrix.GeneralLinearGroup (Fin 2) K) :=
    QuotientGroup.eq_iff_div_mem.mp hq
  have htoGLdiv :
      Matrix.SpecialLinearGroup.toGL (ue / uf) =
        Matrix.SpecialLinearGroup.toGL ue /
          Matrix.SpecialLinearGroup.toGL uf := by
    exact map_div Matrix.SpecialLinearGroup.toGL ue uf
  have hcentSL : ue / uf ∈
      Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) := by
    apply (Matrix.SpecialLinearGroup.toGL_mem_center_iff (ue / uf)).mp
    rw [htoGLdiv]
    exact hcentGL
  have hdiff : ue / uf =
      Matrix.SpecialLinearGroup.transvection hij (e t - f t) := by
    dsimp [ue, uf]
    rw [div_eq_mul_inv, Matrix.SpecialLinearGroup.transvection_inv,
      ← Matrix.SpecialLinearGroup.transvection_add, sub_eq_add_neg]
  rw [hdiff, Matrix.SpecialLinearGroup.transvection_mem_center_iff] at hcentSL
  exact sub_eq_zero.mp hcentSL

/-- The canonical map `PSL₂(K) → PGL₂(K)` is equivariant for
coefficient-field automorphisms. -/
public theorem psl2FieldAut_toPGL
    {K : Type u} [Field K] (e : K ≃+* K) (x : PSL2 K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL ((psl2FieldAut K) e x) =
      (pgl2FieldAut K) e
        (Matrix.ProjectiveSpecialLinearGroup.toPGL x) := by
  refine Quotient.inductionOn' x ?_
  intro y
  change Matrix.ProjectiveSpecialLinearGroup.toPGL
      (psl2RingEquiv e (QuotientGroup.mk' (Subgroup.center _) y)) =
    pgl2RingEquiv e
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (QuotientGroup.mk' (Subgroup.center _) y))
  rw [psl2RingEquiv_mk]
  change QuotientGroup.mk' (Subgroup.center _)
      (Matrix.SpecialLinearGroup.toGL
        (Matrix.SpecialLinearGroup.map e.toRingHom y)) =
    pgl2RingEquiv e
      (QuotientGroup.mk' (Subgroup.center _)
        (Matrix.SpecialLinearGroup.toGL y))
  rw [pgl2RingEquiv_mk]
  congr 1
  ext i j
  rfl

end CFSG.GorensteinWalter
