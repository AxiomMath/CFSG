module

public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineGap
public import CFSG.LocalAnalysis.WeakClosure81.W18ASNineT
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open scoped commutatorElement

namespace NoSocle185Factor

theorem of_statedProj {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
    (H : Subgroup (GL ι K)) (h : NoSocle185Factor (StatedProj H)) : NoSocle185Factor ↥H := by
  refine of_normal ((StatedScalars ι K).subgroupOf H) (of_commute fun a b => ?_) h
  have hc : StatedScalars ι K = Subgroup.center (GL ι K) := by
    rw [StatedScalars, ← Matrix.GeneralLinearGroup.center_eq_range_scalar]
  have ha : a.1.1 ∈ Subgroup.center (GL ι K) := hc ▸ a.2
  exact Subtype.ext (Subtype.ext (Subgroup.mem_center_iff.mp ha b.1.1).symm)

theorem of_lieModel_two (hO : LieOrderFormulasInput) {Y : Type} [Group Y] [IsSimpleGroup Y]
    {t : StatedLieTag} {n f : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hY : LieModel Y t n 2 f)
    (hne : ¬ ((t = .PSL ∧ n = 2 ∧ f = 2) ∨ (t = .PSL ∧ n = 3 ∧ f = 1) ∨
      (t = .PSU ∧ n = 4 ∧ f = 1))) : NoSocle185Factor Y := by
  refine of_isSimpleGroup fun T _ hT => ⟨fun e => ?_⟩
  obtain ⟨-, hM, -⟩ := hO Y t n 2 f hadm hY
  refine hne (hT.crossChar hO hadm ?_)
  rw [← Nat.card_congr e.toEquiv]
  exact hM

end NoSocle185Factor

section Equivs

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

noncomputable def statedOmegaEquivDerived {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) :
    ↥(StatedOmega Q₀) ≃*
      ↥⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
  ((toLinEquiv ι K).subgroupMap (StatedOmega Q₀)).trans (MulEquiv.subgroupCongr (by
    rw [statedOmega_eq_comap hQ]
    exact Subgroup.map_comap_eq_self_of_surjective (toLinEquiv ι K).surjective _))

noncomputable def statedOmegaEquivCommutator {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}
    (hQ : ⇑Q = Q₀) :
    ↥(StatedOmega Q₀) ≃* ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) :=
  (statedOmegaEquivDerived hQ).trans
    ((MulEquiv.subgroupCongr (Subgroup.map_subtype_commutator _).symm).trans
      (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).symm)

end Equivs

noncomputable def commutatorOrthogonalPlusEquiv (k : ℕ) (F : Type) [Field F] :
    ↥(commutator ↥(CFSG.PGLModel.orthogonalPlus k F)) ≃* ↥(StatedOmega (StatedQuadPlus k F)) :=
  (Subgroup.equivMapOfInjective _ (CFSG.PGLModel.orthogonalPlus k F).subtype
      (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr (by rw [Subgroup.map_subtype_commutator]; rfl))

noncomputable def commutatorOrthogonalMinusEquiv (k : ℕ) (F : Type) [Field F] (b c : F) :
    ↥(commutator ↥(CFSG.PGLModel.orthogonalMinus k F b c)) ≃*
      ↥(StatedOmega (StatedQuadMinus (k + 1) F b c)) :=
  (Subgroup.equivMapOfInjective _ (CFSG.PGLModel.orthogonalMinus k F b c).subtype
      (Subgroup.subtype_injective _)).trans
    (MulEquiv.subgroupCongr (by rw [Subgroup.map_subtype_commutator]; rfl))

theorem noSocle185Factor_orthogonalPlus_of_statedOmega (k : ℕ) {F : Type} [Field F] [Finite F]
    (h : NoSocle185Factor ↥(StatedOmega (StatedQuadPlus k F))) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalPlus k F) := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin k ⊕ Fin k) F) := inferInstance
  exact NoSocle185Factor.of_commutator (h.of_mulEquiv (commutatorOrthogonalPlusEquiv k F).symm)

theorem noSocle185Factor_orthogonalMinus_of_statedOmega (k : ℕ) {F : Type} [Field F] [Finite F]
    (b c : F) (h : NoSocle185Factor ↥(StatedOmega (StatedQuadMinus (k + 1) F b c))) :
    NoSocle185Factor ↥(CFSG.PGLModel.orthogonalMinus k F b c) := by
  haveI : Finite (Matrix.GeneralLinearGroup (Fin k ⊕ Fin k ⊕ Fin 2) F) := inferInstance
  exact NoSocle185Factor.of_commutator
    (h.of_mulEquiv (commutatorOrthogonalMinusEquiv k F b c).symm)

end CFSG.LocalAnalysis.WeakClosure81

end
