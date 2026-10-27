module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoClass
import CFSG.LocalAnalysis.ComponentInitial.LinearCoverUnitriangularFour
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.ComponentClassification.SymmetricLocalLinearFourTwo
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3

open CFSG.LocalAnalysis.ComponentInitial.LinearCover
open CFSG.Quasithin.H13.CTK (TwoGroupsClassTwo)
open scoped commutatorElement

theorem exists_class_three_of_isAlt_eight {Q : Type} [Group Q] (h : IsAlt Q 8) :
    ∃ S : Subgroup Q, IsPGroup 2 S ∧ ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, ⁅⁅x, y⁆, z⁆ ≠ 1 := by
  obtain ⟨S, ⟨φ⟩⟩ := exists_sylow_mulEquiv_U4_of_lieModel
    ((CFSG.ComponentClassification.SymmetricLocal.lie_model_linear_four_two_iff Q).2 h)
  have hf : u4f ≠ 1 := by
    intro h1
    have := (u4_def_eq_one false false true (by simpa using h1)).2.2
    exact absurd this (by decide)
  refine ⟨S, S.isPGroup', φ.symm u4a, (φ.symm u4a).2, φ.symm u4b, (φ.symm u4b).2,
    φ.symm u4c, (φ.symm u4c).2, fun h1 => hf ?_⟩
  have h2 : ⁅⁅φ.symm u4a, φ.symm u4b⁆, φ.symm u4c⁆ = 1 :=
    Subtype.ext (by simpa [commutatorElement_def] using h1)
  have h3 := congrArg φ h2
  rw [map_commutatorElement, map_commutatorElement] at h3
  simpa [← u4_commutator_ab, ← u4_commutator_dc] using h3

theorem not_isAlt_bar2_of_twoGroupsClassTwo {L : Type} [Group L] (h : TwoGroupsClassTwo L)
    (K : Subgroup L) : ¬ IsAlt (Bar2 K) 8 := by
  intro hK
  obtain ⟨S, hS, x, hx, y, hy, z, hz, hne⟩ := exists_class_three_of_isAlt_eight hK
  let π : K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hker : IsPGroup 2 π.ker := by
    rw [QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup
  have hP : IsPGroup 2 (S.comap π) := hS.comap_of_ker_isPGroup π hker
  obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
  obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨z', rfl⟩ := QuotientGroup.mk'_surjective _ z
  have key := h ((S.comap π).map K.subtype) (hP.map _) (x' : L) ⟨x', hx, rfl⟩ (y' : L)
    ⟨y', hy, rfl⟩ (z' : L) ⟨z', hz, rfl⟩
  have h1 : ⁅⁅x', y'⁆, z'⁆ = 1 := Subtype.ext (by simpa [commutatorElement_def] using key)
  apply hne
  rw [← map_commutatorElement, ← map_commutatorElement, h1, map_one]

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3
