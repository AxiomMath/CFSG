module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_11
import Mathlib.Algebra.CharP.CharAndCard
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert II.6.14

This file records the two small-field identifications used in
Huppert--Blackburn XI.1.3.
-/

namespace CFSG.BenderSuzuki
namespace External

open scoped LinearAlgebra.Projectivization

universe u

public theorem huppert614_card_specialLinearGroup
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have hdet_range_top :
      (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K)).range = ⊤ := by
    ext u
    constructor
    · intro _
      simp
    · intro _
      let diagonalGL : GL (Fin 2) K :=
        Matrix.GeneralLinearGroup.mkOfDetNeZero
          (Matrix.diagonal ![(u : K), 1]) (by
            simp [Matrix.det_diagonal, Fin.prod_univ_two])
      refine ⟨diagonalGL, ?_⟩
      ext
      simp [diagonalGL, Matrix.det_diagonal, Fin.prod_univ_two]
  have hGL :
      Nat.card (GL (Fin 2) K) =
        (Nat.card K ^ 2 - 1) * (Nat.card K ^ 2 - Nat.card K) := by
    simpa [Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let detHom := Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K)
  have hRange : Nat.card detHom.range = Nat.card K - 1 := by
    rw [hdet_range_top]
    simpa using (Fintype.card_units (α := K))
  have hmul :
      Nat.card detHom.range * Nat.card detHom.ker =
        Nat.card (GL (Fin 2) K) := by
    rw [← Subgroup.index_ker detHom]
    exact detHom.ker.index_mul_card
  have hker :
      Nat.card detHom.ker = Nat.card K * (Nat.card K ^ 2 - 1) := by
    have hdiff :
        Nat.card K ^ 2 - Nat.card K = Nat.card K * (Nat.card K - 1) := by
      rw [pow_two]
      calc
        Nat.card K * Nat.card K - Nat.card K =
            Nat.card K * Nat.card K - Nat.card K * 1 := by simp
        _ = Nat.card K * (Nat.card K - 1) :=
          (Nat.mul_sub_left_distrib _ _ _).symm
    have hcancel :
        (Nat.card K - 1) * Nat.card detHom.ker =
          (Nat.card K - 1) * (Nat.card K * (Nat.card K ^ 2 - 1)) := by
      calc
        (Nat.card K - 1) * Nat.card detHom.ker =
            Nat.card (GL (Fin 2) K) := by
          rw [hRange] at hmul
          exact hmul
        _ = (Nat.card K ^ 2 - 1) *
            (Nat.card K ^ 2 - Nat.card K) := hGL
        _ = (Nat.card K - 1) *
            (Nat.card K * (Nat.card K ^ 2 - 1)) := by
          rw [hdiff]
          ring
    exact Nat.eq_of_mul_eq_mul_left
      (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K))) hcancel
  calc
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) =
        Nat.card detHom.ker := by
      let slEquivDetKer :
          Matrix.SpecialLinearGroup (Fin 2) K ≃ detHom.ker := by
        refine Equiv.ofBijective
          (fun A => ⟨Matrix.SpecialLinearGroup.toGL A, by
            exact Matrix.SpecialLinearGroup.coeToGL_det A⟩) ?_
        constructor
        · intro A B h
          apply Matrix.SpecialLinearGroup.toGL_injective
          exact congrArg Subtype.val h
        · intro A
          refine ⟨⟨(A : GL (Fin 2) K), ?_⟩, ?_⟩
          · have hmem := A.property
            change Matrix.GeneralLinearGroup.det (A : GL (Fin 2) K) = 1 at hmem
            exact Units.ext_iff.mp hmem
          · apply Subtype.ext
            apply Matrix.GeneralLinearGroup.ext
            intro i j
            rfl
      exact Nat.card_congr slEquivDetKer
    _ = Nat.card K * (Nat.card K ^ 2 - 1) := hker

public theorem huppert614_card_center_of_neg_one_eq_one
    {K : Type u} [Field K] [Finite K] (hneg : (-1 : K) = 1) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let e :=
    Equiv.Set.image ((↑) : Kˣ → K) (rootsOfUnity 2 K : Set Kˣ)
      Units.val_injective
  have he :
      Nat.card (rootsOfUnity 2 K) =
        Nat.card (((↑) : Kˣ → K) '' (rootsOfUnity 2 K : Set Kˣ)) :=
    Nat.card_congr e
  rw [Units.val_set_image_rootsOfUnity_two] at he
  have hroots : Nat.card (rootsOfUnity 2 K) = 1 := by
    simpa [hneg] using he
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (R := K) (n := Fin 2) 0).toEquiv]
  exact hroots

public theorem huppert614_card_center_of_neg_one_ne_one
    {K : Type u} [Field K] [Finite K] (hneg : (-1 : K) ≠ 1) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) = 2 := by
  classical
  let : Fintype K := Fintype.ofFinite K
  let e :=
    Equiv.Set.image ((↑) : Kˣ → K) (rootsOfUnity 2 K : Set Kˣ)
      Units.val_injective
  have he :
      Nat.card (rootsOfUnity 2 K) =
        Nat.card (((↑) : Kˣ → K) '' (rootsOfUnity 2 K : Set Kˣ)) :=
    Nat.card_congr e
  rw [Units.val_set_image_rootsOfUnity_two] at he
  have hroots : Nat.card (rootsOfUnity 2 K) = 2 := by
    simpa [hneg, Ne.symm hneg] using he
  rw [Nat.card_congr
    (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity'
      (R := K) (n := Fin 2) 0).toEquiv]
  exact hroots

public theorem huppert614_card_psl_mul_center
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  calc
    Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) *
        Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K)) =
        Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup
        (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K))).symm
    _ = Nat.card K * (Nat.card K ^ 2 - 1) :=
      huppert614_card_specialLinearGroup

/-- Huppert II.6.14(1): `PSL(2,2)` is the symmetric group on three letters. -/
public theorem huppert_II_6_14_a_psl2_card_two
    {K : Type u} [Field K] [Finite K] (hKcard : Nat.card K = 2) :
    Nonempty
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
        Equiv.Perm (Fin 3)) := by
  classical
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime (by
      simpa [Nat.card_eq_fintype_card] using hKcard)
  have hneg_one : (-1 : K) = 1 := by
    apply (neg_eq_iff_add_eq_zero).2
    have hone_add_one : (1 : K) + 1 = 0 := by
      rw [show (1 : K) + 1 = 2 by norm_num]
      exact CharP.cast_eq_zero K 2
    exact hone_add_one
  have hcenter := huppert614_card_center_of_neg_one_eq_one hneg_one
  have hPSLcard := huppert614_card_psl_mul_center (K := K)
  rw [hcenter, hKcard] at hPSLcard
  norm_num at hPSLcard
  let P := ℙ K (Fin 2 → K)
  let PSL := Matrix.ProjectiveSpecialLinearGroup (Fin 2) K
  have hPcard : Nat.card P = 3 := by
    change Nat.card (ℙ K (Fin 2 → K)) = 3
    rw [Projectivization.card_of_finrank_two K (Fin 2 → K) (by simp), hKcard]
  obtain ⟨rho, hrho, _, _⟩ :=
    huppert_II_6_11_projective_action (K := K) 2 (by omega)
  let eP : P ≃ Fin 3 := Finite.equivFinOfCardEq hPcard
  let actFin : PSL →* Equiv.Perm (Fin 3) :=
    (Equiv.permCongrHom eP).toMonoidHom.comp rho
  have hactFin_inj : Function.Injective actFin := by
    intro x y hxy
    apply hrho
    apply (Equiv.permCongrHom eP).injective
    simpa [actFin] using hxy
  have hpermcard : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    rw [Nat.card_perm, Nat.card_fin]
    norm_num [Nat.factorial]
  have hactFin_bij : Function.Bijective actFin :=
    (Nat.bijective_iff_injective_and_card actFin).2
      ⟨hactFin_inj, by simpa [PSL, hPSLcard] using hpermcard.symm⟩
  exact ⟨MulEquiv.ofBijective actFin hactFin_bij⟩


end External
end CFSG.BenderSuzuki
