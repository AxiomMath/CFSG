module

public import CFSG.Quasithin.Background.P4InspSpBasic
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherGeneration
public import CFSG.Quasithin.Background.RonanG1015Transport

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace RonanG1015

open CFSG.Quasithin.G11 CFSG.Quasithin.G11.P4InspSp
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag

variable {U : Type} [AddCommGroup U] [Module (ZMod 2) U] {f : LinearMap.BilinForm (ZMod 2) U}

theorem zmodTwo_ringEquiv_apply (σ : ZMod 2 ≃+* ZMod 2) (x : ZMod 2) : σ x = x := by
  have h : ∀ y : ZMod 2, y = 0 ∨ y = 1 := by decide
  rcases h x with rfl | rfl
  · exact map_zero σ
  · exact map_one σ

theorem proj_injective_zmod_two (m : ℕ) : Function.Injective (proj m (ZMod 2)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have h : (proj m (ZMod 2)).ker = (StatedScalars (Fin m ⊕ Fin m) (ZMod 2)).subgroupOf
      (StatedSp m (ZMod 2)) := QuotientGroup.ker_mk' _
  rw [h, CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf]

noncomputable def spProjEquiv {m : ℕ} (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) U)
    (hb : LinearMap.BilinForm.toMatrix b f = Matrix.J (Fin m) (ZMod 2)) :
    ↥(spSub f) ≃* StatedProj (StatedSp m (ZMod 2)) :=
  have hscal : (StatedScalars (Fin m ⊕ Fin m) (ZMod 2)).subgroupOf (StatedSp m (ZMod 2)) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_zmod_two_eq_bot, Subgroup.bot_subgroupOf]
  (MulEquiv.subgroupCongr (p4inspsp_spSub_eq f)).trans
    ((CFSG.ComponentClassification.CatalogueBAlternatingIsometry.isometryMatrixEquiv b f
      hb).trans ((MulEquiv.subgroupCongr
        CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic.symm).trans
          ((QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot).symm))

theorem spProjEquiv_form {m : ℕ} (b : Module.Basis (Fin m ⊕ Fin m) (ZMod 2) U)
    (hb : LinearMap.BilinForm.toMatrix b f = Matrix.J (Fin m) (ZMod 2)) (k : ↥(spSub f)) :
    ∃ x : StatedSp m (ZMod 2), spProjEquiv b hb k = proj m (ZMod 2) x ∧
      (x : GL (Fin m ⊕ Fin m) (ZMod 2)) =
        CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b
          (k : GLV U) :=
  ⟨⟨_, _⟩, rfl, rfl⟩

theorem indAll_spSub [Finite U] (hf : CFSG.Quasithin.G11.IsSymplectic f) (hd : 6 ≤ Module.finrank (ZMod 2) U) :
    IndAll (spSub f) := by
  have : FiniteDimensional (ZMod 2) U := Module.Finite.of_finite
  obtain ⟨m, b, hm, hb⟩ :=
    CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_symplectic_basis f hf.1
      (p4inspsp_nondeg hf)
  have hm3 : 3 ≤ m := by omega
  intro α
  set e := spProjEquiv b hb with he
  obtain ⟨A, σ, hβ⟩ := (automorphism_generation (K := ZMod 2) (r := m) hm3).2 (MulAut.congr e α)
  have hσ : ∀ x, σ x = x := zmodTwo_ringEquiv_apply σ
  set bm := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv b with hbm
  refine ⟨bm.symm (A : GL (Fin m ⊕ Fin m) (ZMod 2)), fun k => ?_⟩
  apply bm.injective
  obtain ⟨x, hx1, hx2⟩ := spProjEquiv_form b hb k
  obtain ⟨x', hx1', hx2'⟩ := spProjEquiv_form b hb (α k)
  have hk : e (α k) = (MulAut.congr e α) (e k) := by
    rw [MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hx1', hx1, hβ] at hk
  have h1 : (conjAut m (ZMod 2) A * fieldAut m (ZMod 2) σ) (proj m (ZMod 2) x) =
      proj m (ZMod 2) (conjSp m (ZMod 2) A (fieldSp m (ZMod 2) σ x)) := rfl
  rw [h1] at hk
  have hxx := proj_injective_zmod_two m hk
  have h2 : ((fieldSp m (ZMod 2) σ x : StatedSp m (ZMod 2)) : GL (Fin m ⊕ Fin m) (ZMod 2)) =
      (x : GL (Fin m ⊕ Fin m) (ZMod 2)) :=
    Units.ext (by rw [coe_fieldSp]; exact Matrix.ext fun i j => hσ _)
  have h3 : (x' : GL (Fin m ⊕ Fin m) (ZMod 2)) =
      (A : GL (Fin m ⊕ Fin m) (ZMod 2)) * (x : GL (Fin m ⊕ Fin m) (ZMod 2)) *
        (A : GL (Fin m ⊕ Fin m) (ZMod 2))⁻¹ := by
    rw [hxx, coe_conjSp, h2]
  rw [← hx2', h3, hx2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end RonanG1015

end CFSG.Quasithin
