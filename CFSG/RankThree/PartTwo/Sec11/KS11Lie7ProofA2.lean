module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofSplit
public import CFSG.RankThree.PartTwo.Sec11.KS11Lie7ProofUnitary
public import CFSG.LieType.Chevalley.E6GraphInvertedRootRotation
public import CFSG.RankThree.Classical2.SLnRootAutomorphism
public import CFSG.LieType.Chevalley.LangRootRankOneTorus
public import CFSG.LinearAlgebra.LinearGroups.Generation

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.RankThree.Chevalley
  CFSG.GH74.GLS.Stage2.Bender.Thm1 CFSG.LieType.HighestRoot CFSG.LieType.Steinberg.RankTwo
open scoped MatrixGroups Matrix

local notation "RA2" => CFSG.LieType.RootSystem.roots
  (CFSG.LieType.Universal.SpecialLinear.isFiniteType_A 2) (∅ : Set (Fin 2))

section Roots

@[expose] def a2RootOf (i j : Fin 3) : Fin 2 → ℤ :=
  ![![![0, 0], ![1, 0], ![1, 1]], ![![-1, 0], ![0, 0], ![0, 1]],
    ![![-1, -1], ![0, -1], ![0, 0]]] i j

theorem toStd_a2RootOf {i j : Fin 3} (hij : i ≠ j) :
    CFSG.LieType.Universal.SpecialLinear.toStd 2 (a2RootOf i j) =
      Pi.single i 1 - Pi.single j 1 := by
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide

theorem a2RootOf_mem {i j : Fin 3} (hij : i ≠ j) : a2RootOf i j ∈ RA2 := by
  rw [CFSG.LieType.Universal.SpecialLinear.roots_eq]
  exact ⟨i, j, hij, toStd_a2RootOf hij⟩

theorem x_a2RootOf {L : Type} [Field L] {i j : Fin 3} (hij : i ≠ j) (c : L) :
    CFSG.LieType.Steinberg.SL.x 2 L (a2RootOf i j) c =
      Matrix.SpecialLinearGroup.transvection hij c :=
  CFSG.LieType.Steinberg.SL.x_eq hij (toStd_a2RootOf hij) c

@[expose] def a2G2 (i j : Fin 3) : Fin Tag.G2.rank → ℤ :=
  g2CommRoot (a2pos (a2RootOf i j 0, a2RootOf i j 1))

abbrev swap01 : Equiv.Perm (Fin 3) := Equiv.swap 0 1

theorem rootReflection_g2v_a2G2
    {i j : Fin 3} (hij : i ≠ j) :
    rootReflection g2v • a2G2 i j = a2G2 (swap01 j) (swap01 i) := by
  rw [rootReflection_smul isRoot_g2v]
  fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | decide +kernel

end Roots

section Phi

variable {L : Type} [Field L]
  (φ : Matrix.SpecialLinearGroup (Fin (2 + 1)) L →* ↥(adjointGroup .G2 L))
  (hφ : ∀ γ ∈ RA2, ∀ c : L, φ (CFSG.LieType.Steinberg.SL.x 2 L γ c) = a2y γ c)

include hφ in
theorem coe_phi_transvection {i j : Fin 3} (hij : i ≠ j) (c : L) :
    ((φ (Matrix.SpecialLinearGroup.transvection hij c) : adjointGroup .G2 L) : ModGL .G2 L) =
      pinnedX .G2 L (a2G2 i j)
        (((rootOperatorFamily .G2).pinnedFamilySign (a2G2 i j) : ℤ) * c) := by
  rw [← x_a2RootOf hij, hφ _ (a2RootOf_mem hij), KS11Lie4Proof.coe_a2y (a2RootOf_mem hij)]
  rfl

include hφ in
theorem exists_twist_transvection (σ : L →+* L) {n : ModGL .G2 L}
    (hn : n ∈ monomialSubgroup .G2 L) (hw : weylQuotientHom .G2 L ⟨n, hn⟩ = rootReflection g2v)
    {i j : Fin 3} (hij : i ≠ j) :
    ∃ b : Lˣ, ∀ c : L, n * baseChangeGL σ
        ((φ (Matrix.SpecialLinearGroup.transvection hij c) : adjointGroup .G2 L) :
          ModGL .G2 L) * n⁻¹ =
      ((φ (Matrix.SpecialLinearGroup.transvection (swap01.injective.ne hij).symm
        ((b : L) * σ c)) : adjointGroup .G2 L) : ModGL .G2 L) := by
  have hα : IsRoot .G2 (a2G2 i j) :=
    KS11Lie4Proof.isRoot_of_long (KS11Lie4Proof.a2_long_roots (a2RootOf_mem hij))
  obtain ⟨μ, hμ⟩ := monomial_conj_pinnedX hn hα
  set s : L := (((rootOperatorFamily .G2).pinnedFamilySign (a2G2 i j) : ℤ) : L) with hsdef
  set s' : L := (((rootOperatorFamily .G2).pinnedFamilySign
    (a2G2 (swap01 j) (swap01 i)) : ℤ) : L) with hs'def
  have hs : s * s = 1 := (rootOperatorFamily .G2).pinnedFamilySign_mul_self L _
  have hs' : s' * s' = 1 := (rootOperatorFamily .G2).pinnedFamilySign_mul_self L _
  have hss : (s' * s) * (s' * s) = 1 := by linear_combination (s' * s') * hs + hs'
  refine ⟨μ * Units.mkOfMulEqOne (s' * s) (s' * s) hss, fun c => ?_⟩
  rw [coe_phi_transvection φ hφ hij, coe_phi_transvection φ hφ _, baseChangeGL_pinnedX, hμ, hw,
    rootReflection_g2v_a2G2 hij, map_mul, map_intCast]
  congr 1
  rw [Units.val_mul, Units.val_mkOfMulEqOne, ← hsdef, ← hs'def]
  linear_combination (-(μ : L) * s * σ c) * hs'

theorem inv_map_transpose_eq_glTwist (σ : L →+* L) (X : SL(3, L)) :
    ((((X : Matrix (Fin 3) (Fin 3) L).map σ)⁻¹)ᵀ : Matrix (Fin 3) (Fin 3) L) =
      (glTwist 3 σ (slToGL X) : Matrix (Fin 3) (Fin 3) L) := by
  rw [coe_glTwist, ← map_inv]
  congr 1
  refine Matrix.inv_eq_left_inv ?_
  change ((X⁻¹ : SL(3, L)) : Matrix (Fin 3) (Fin 3) L).map σ *
    (X : Matrix (Fin 3) (Fin 3) L).map σ = 1
  rw [← Matrix.map_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.map_one _ σ.map_zero σ.map_one]

include hφ in
theorem exists_twist_hom (hφinj : Function.Injective φ) (σ : L →+* L) {n : ModGL .G2 L}
    (hnC : n ∈ adjointGroup .G2 L) (hn : n ∈ monomialSubgroup .G2 L)
    (hw : weylQuotientHom .G2 L ⟨n, hn⟩ = rootReflection g2v) :
    ∃ Ψ : SL(3, L) →* SL(3, L),
      (∀ X, ((φ (Ψ X) : adjointGroup .G2 L) : ModGL .G2 L) =
        n * baseChangeGL σ ((φ X : adjointGroup .G2 L) : ModGL .G2 L) * n⁻¹) ∧
      ∃ W : GL (Fin 3) L, ∀ X, slToGL (Ψ X) = W * glTwist 3 σ (slToGL X) * W⁻¹ := by
  classical
  set sA : adjointGroup .G2 L →* adjointGroup .G2 L :=
    ((baseChangeGL σ).comp (adjointGroup .G2 L).subtype).codRestrict _ fun w =>
      baseChangeGL_mem_adjointGroup σ w.2 with hsA
  set F : adjointGroup .G2 L →* adjointGroup .G2 L :=
    (MulAut.conj (⟨n, hnC⟩ : adjointGroup .G2 L)).toMonoidHom.comp sA with hF
  have hFapp : ∀ w, (F w : ModGL .G2 L) = n * baseChangeGL σ (w : ModGL .G2 L) * n⁻¹ :=
    fun w => rfl
  have hle : (F.comp φ).range ≤ φ.range := by
    rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation,
      MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, j, hij, t, rfl⟩, rfl⟩
    obtain ⟨b, hb⟩ := exists_twist_transvection φ hφ σ hn hw hij
    exact ⟨_, Subtype.ext ((hb t).symm.trans (hFapp _).symm)⟩
  set eφ := MonoidHom.ofInjective hφinj with heφ
  set Ψ : SL(3, L) →* SL(3, L) :=
    eφ.symm.toMonoidHom.comp ((F.comp φ).codRestrict φ.range fun X => hle ⟨X, rfl⟩) with hΨdef
  have hΨ : ∀ X, φ (Ψ X) = F (φ X) := fun X => by
    have h1 := congrArg Subtype.val (eφ.apply_symm_apply
      ((F.comp φ).codRestrict φ.range (fun X => hle ⟨X, rfl⟩) X))
    rw [heφ, MonoidHom.ofInjective_apply] at h1
    exact h1
  refine ⟨Ψ, fun X => by rw [hΨ, hFapp], ?_⟩
  set b : Fin 3 → Fin 3 → Lˣ := fun i j =>
    if hij : i ≠ j then (exists_twist_transvection φ hφ σ hn hw hij).choose else 1 with hbdef
  have hshape : ∀ (i j : Fin 3) (hij : i ≠ j) (t : L),
      ((Ψ (Matrix.SpecialLinearGroup.transvection hij t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) =
        1 + Matrix.single (swap01 j) (swap01 i) ((b i j : L) * σ t) := by
    intro i j hij t
    have hb := (exists_twist_transvection φ hφ σ hn hw hij).choose_spec t
    have hbij : b i j = (exists_twist_transvection φ hφ σ hn hw hij).choose := by
      simp only [hbdef]
      split_ifs
      rfl
    have h1 : Ψ (Matrix.SpecialLinearGroup.transvection hij t) =
        Matrix.SpecialLinearGroup.transvection (swap01.injective.ne hij).symm
          ((b i j : L) * σ t) := by
      apply hφinj
      rw [hΨ, hbij]
      exact Subtype.ext ((hFapp _).trans hb)
    rw [h1, Matrix.SpecialLinearGroup.transvection_coe]
  obtain ⟨W, hW⟩ := CFSG.RankThree.Classical2.exists_conj_map_inv_transpose_of_root_permuting
    (by norm_num) σ swap01 Ψ b hshape
  refine ⟨W, fun X => Units.ext ?_⟩
  rw [Units.val_mul, Units.val_mul, ← inv_map_transpose_eq_glTwist]
  exact hW X

end Phi

end CFSG.RankThree.PartTwo.Sec11.KS11Lie7Proof
