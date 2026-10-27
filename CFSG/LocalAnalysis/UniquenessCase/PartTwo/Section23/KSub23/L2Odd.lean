module

import CFSG.Quasithin.Vol2.Ch11SecO5F
import CFSG.Adapters.StatedPSLTwo
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo Subgroup

theorem eq_top_or_isAlt_of_isL2Odd {S : Type} [Group S] [Finite S]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : IsL2Odd S p) (Y : Subgroup S) (hY : ⁅Y, Y⁆ = Y)
    (hne : Y ≠ ⊥) : Y = ⊤ ∨ IsAlt ↥Y 5 := by
  obtain ⟨-, K, hF, hFin, hcard, ⟨eS⟩⟩ := hS.statedClassicalModel (by decide)
  letI : Field K := hF
  haveI : Finite K := hFin
  have hK : Nat.card K = p := by simpa using hcard
  let eP : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    eS.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hBperf : ⁅Y.map eP.toMonoidHom, Y.map eP.toMonoidHom⁆ = Y.map eP.toMonoidHom := by
    rw [← Subgroup.map_commutator, hY]
  have hBne : Y.map eP.toMonoidHom ≠ ⊥ := fun h =>
    hne ((Subgroup.map_eq_bot_iff_of_injective _ eP.injective).mp h)
  rcases CFSG.Quasithin.Vol2.Ch11.O5.perfect_cases hp hp2 hK hBperf hBne with hB | hAlt
  · left
    rw [show Y = (Y.map eP.toMonoidHom).comap eP.toMonoidHom from
      (Subgroup.comap_map_eq_self_of_injective eP.injective Y).symm, hB, Subgroup.comap_top]
  · obtain ⟨eB⟩ := hAlt
    exact Or.inr ⟨(Y.equivMapOfInjective eP.toMonoidHom eP.injective).trans eB⟩

theorem eq_bot_or_isSimpleGroup_of_isL2Odd {S : Type} [Group S]
    [Finite S] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hS : IsL2Odd S p) (Y : Subgroup S)
    (hY : ⁅Y, Y⁆ = Y) : Y = ⊥ ∨ IsSimpleGroup ↥Y := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  · right
    rcases eq_top_or_isAlt_of_isL2Odd hp hp2 hS Y hY hbot with htop | hAlt
    · have hSsimple : IsSimpleGroup S := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hS
      exact ((MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv).isSimpleGroup_congr.mpr
        hSsimple
    · obtain ⟨e⟩ := hAlt
      exact e.isSimpleGroup_congr.mpr alternatingGroup.isSimpleGroup_five

end CFSG.LocalAnalysis.UniquenessCase.UC22.KS23

end
