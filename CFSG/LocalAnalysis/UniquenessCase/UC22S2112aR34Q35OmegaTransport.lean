module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesOmega
public import CFSG.Open.StatedDefs
import CFSG.ClassicalGroups.Orthogonal.Matrix
import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.BridgeDerived
import CFSG.Blueprint.SourceClassicalTransport
import CFSG.LieType.Steinberg.CentralExt.OrthogonalPerfect
public import CFSG.ClassicalInvolution.Orders.OrthogonalNeg
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Universal.SpinOmega.Range
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.TypesInvol
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Decomposition
import CFSG.LieType.Steinberg.Classical.SpinFrame
import CFSG.LieType.Steinberg.Exceptional.E6E7
import CFSG.LieType.Steinberg.Families
import CFSG.LieType.Steinberg.G2
import CFSG.LieType.Universal.Spin.Generation
import CFSG.LieType.Universal.Spin.OddCT
import CFSG.LieType.Universal.Spin.PlusCT
import CFSG.LieType.Universal.Spin.Structure
import CFSG.LieType.Universal.SpinOmega
import CFSG.LieType.Universal.Unitary
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailModelBorel
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailPolar
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7

open CFSG.OddStandard.SmallF3.Omega CFSG.Open CFSG.LieType.Universal.Spin Matrix

private theorem mem_commutator_iff {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 3) (ι → ZMod 3)) (g : OGroup Q) :
    g ∈ commutator (OGroup Q) ↔
      (g : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [← Subgroup.map_subtype_commutator (TauCeti.QuadraticMap.orthogonalGroup Q)]
  constructor
  · intro h
    simpa using Subgroup.mem_map_of_mem (TauCeti.QuadraticMap.orthogonalGroup Q).subtype h
  · rintro ⟨y, hy, hxy⟩
    have hy' : y = g := Subtype.ext hxy
    rwa [hy'] at hy

noncomputable def statedOmegaMulEquivOmegaGroup {ι : Type} [Fintype ι] [DecidableEq ι]
    (Q : QuadraticForm (ZMod 3) (ι → ZMod 3)) (hQ : Q.Nondegenerate)
    (h2 : 2 ≤ Fintype.card ι) : StatedOmega ⇑Q ≃* omegaGroup hQ := by
  classical
  let e := CFSG.ClassicalGroups.Orthogonal.toLinEquiv ι (ZMod 3)
  have hH : StatedOmega ⇑Q =
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
        TauCeti.QuadraticMap.orthogonalGroup Q⁆.comap e.toMonoidHom :=
    CFSG.ClassicalGroups.Orthogonal.statedOmega_eq_comap (Q := Q) rfl
  have h2' : 2 ≤ Module.finrank (ZMod 3) (ι → ZMod 3) := by
    rwa [Module.finrank_fintype_fun_eq_card]
  let fO : StatedOmega ⇑Q →* OGroup Q :=
    MonoidHom.codRestrict (e.toMonoidHom.comp (StatedOmega ⇑Q).subtype)
      (TauCeti.QuadraticMap.orthogonalGroup Q) fun A =>
        Subgroup.commutator_le_self _
          (show e (A : GL ι (ZMod 3)) ∈
            ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
              TauCeti.QuadraticMap.orthogonalGroup Q⁆ from by
            simpa using (le_of_eq hH) A.2)
  let f : StatedOmega ⇑Q →* omegaGroup hQ :=
    MonoidHom.codRestrict fO (omegaGroup hQ) fun A => by
      have hg : fO A ∈ commutator (OGroup Q) :=
        (mem_commutator_iff Q (fO A)).mpr (by
          simpa [fO] using (show e (A : GL ι (ZMod 3)) ∈
            ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
              TauCeti.QuadraticMap.orthogonalGroup Q⁆ from by
            simpa using (le_of_eq hH) A.2))
      rw [omegaGroup_eq_commutator hQ h2']
      exact hg
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · intro A B hAB
    apply Subtype.ext
    apply e.injective
    have h : ((f A : omegaGroup hQ) :
        (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) =
        ((f B : omegaGroup hQ) :
          (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) :=
      congrArg (fun z : omegaGroup hQ =>
        ((z : OGroup Q) : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))) hAB
    simpa only [f, fO, MonoidHom.codRestrict_apply, Subgroup.coe_subtype,
      Function.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] using h
  · intro g
    have hg : (g : OGroup Q) ∈ commutator (OGroup Q) := by
      rw [← omegaGroup_eq_commutator hQ h2']
      exact g.2
    have hg' : ((g : OGroup Q) : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)) ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
          TauCeti.QuadraticMap.orthogonalGroup Q⁆ :=
      (mem_commutator_iff Q g).mp hg
    refine ⟨⟨e.symm ((g : OGroup Q) :
      (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3)), ?_⟩, ?_⟩
    · exact (le_of_eq hH.symm) (Subgroup.mem_comap.mpr (by simpa using hg'))
    · apply Subtype.ext
      apply Subtype.ext
      show e (e.symm ((g : OGroup Q) :
        (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))) =
        ((g : OGroup Q) : (ι → ZMod 3) ≃ₗ[ZMod 3] (ι → ZMod 3))
      exact e.apply_symm_apply _

theorem nonempty_statedOmega_quadOdd_mulEquiv {K L : Type} [Field K] [Field L] [Finite K]
    [Finite L] (h : Nat.card K = Nat.card L) (n : ℕ) :
    Nonempty (StatedOmega (StatedQuadOdd n K) ≃* StatedOmega (StatedQuadOdd n L)) := by
  classical
  let φ : K ≃+* L := CFSG.Blueprint.EvenSource.ringEquivOfNatCard h
  exact ⟨((CFSG.Adapters.RankTwoModelTransports.glCongr
      (ι := Fin n ⊕ Fin n ⊕ Unit) φ).subgroupMap
        (StatedOmega (StatedQuadOdd n K))).trans
    (MulEquiv.subgroupCongr
      (CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover.map_statedOmega φ
        (CFSG.Blueprint.EvenSource.statedQuadOdd_map φ n)))⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.Q35Omega7
