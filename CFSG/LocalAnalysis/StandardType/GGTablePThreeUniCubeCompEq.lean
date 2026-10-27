module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeBridge
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniCubeSpecial

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

theorem uni_cube_component_eq_eigBlock {K : Type} [Field K] [Finite K] [CharP K 2] {q n : ℕ}
    (hK : Nat.card K = q ^ 2) (hq3 : 3 ∣ q + 1) (hn : 4 ≤ n)
    {d : GL (Fin n) K} (hd : IsHermIsometry q (d : Matrix (Fin n) (Fin n) K)) (hd3 : d ^ 3 = 1)
    {δ' : MulAut (PSUg n K q)} (hδ : IsConjBy d δ') {Q : Subgroup (PSUg n K q)}
    (hQ : IsComponentOf Q (ggAutFixedSubgroup δ')) :
    ∃ μ : K, μ ^ 3 = 1 ∧ Q = eigBlock q d μ := by
  obtain ⟨f, hf1, rfl⟩ :=
    CFSG.AGLEmbedding.ToralCensus.exists_eq_two_pow_of_card_eq_sq hK
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f K :=
    CFSG.AGLEmbedding.ToralCensus.unitaryFieldData_of_card_eq_sq hK hf1
  have hdm : d ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary h
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) :=
    uni_cube_mem_primeFormUnitary h rfl hd
  have H : CFSG.RankThree.PartOne.KCUnitary.UnitaryPrimaryData h.bar
      (CFSG.RankThree.PartOne.KCUnitaryModel.idForm h n)
      (Matrix.GeneralLinearGroup.toLin d) :=
    uni_cube_unitaryPrimaryData h hdm hd3
  have hn1 : 1 ≤ n := by omega
  have hHmap : (ggAutFixedSubgroup δ').map
        (CFSG.StandardType.InndiagSU.projEquiv h hn1).toMonoidHom =
      CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
        (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
          (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) ⟨d, hdm⟩) := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (uni_cube_fixSubgroup_projEquiv h hn1 hδ hdm y).mp hy
    · intro hx
      refine ⟨(CFSG.StandardType.InndiagSU.projEquiv h hn1).symm x, ?_, ?_⟩
      · refine (uni_cube_fixSubgroup_projEquiv h hn1 hδ hdm _).mpr ?_
        rw [MulEquiv.apply_symm_apply]
        exact hx
      · exact MulEquiv.apply_symm_apply _ x
  have hcomp : CFSG.Assembly.IsComponentOf
        (Q.map (CFSG.StandardType.InndiagSU.projEquiv h hn1).toMonoidHom)
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) ⟨d, hdm⟩)) := by
    have h' := isComponentOf_map_mulEquiv'
      (CFSG.StandardType.InndiagSU.projEquiv h hn1) hQ
    rwa [hHmap] at h'
  have hcompOpen : CFSG.Open.IsComponentOf
        (Q.map (CFSG.StandardType.InndiagSU.projEquiv h hn1).toMonoidHom)
        (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup
          (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormConjHom h
            (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K n) ⟨d, hdm⟩)) :=
    isComponentOf_iff_open.mp hcomp
  obtain ⟨μ, hμ, hT⟩ :=
    uni_cube_primeForm_component_eq_specialBlock h ⟨d, hdm⟩ hd3 H
      (Q.map (CFSG.StandardType.InndiagSU.projEquiv h hn1).toMonoidHom) hcompOpen
  have hspec := uni_cube_specialBlock_eq_eigBlock h hn1 hdm hd3 hq3 H hμ
  refine ⟨μ, hμ, ?_⟩
  rw [← hT] at hspec
  exact Subgroup.map_injective
    (CFSG.StandardType.InndiagSU.projEquiv h hn1).injective hspec.symm

end CFSG.StandardType.TablePThreeKG

end
