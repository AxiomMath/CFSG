module

public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLRound

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggFixed_of_tableBAction {G : Type} [Group G] {Bs L B₂ : Subgroup G} {x : G}
    (hA : GGTableBAction Bs x L B₂) {b : Bs}
    (hb : ∀ φ ∈ ggAutomizer L Bs, φ b = b) : (b : G) ∈ Subgroup.zpowers x := by
  refine hA.1 (b : G) b.2 ?_
  intro n hn
  have hnN : n ∈ Subgroup.normalizer (Bs : Set G) := hn.2
  have h1 := congrArg Subtype.val (hb (ggConjAut Bs hnN) (ggConjAut_mem_ggAutomizer hn.1 hnN))
  rw [ggConjAut_apply] at h1
  calc n * (b : G) = n * (b : G) * n⁻¹ * n := by group
    _ = (b : G) * n := by rw [h1]

theorem ggTBFixInput_of_tableB (hM : GGTableBModuleInput) (hA : GGTableBActionInput) :
    GGTBFixInput := by
  intro G _ _ p B Bs x L D J hC _ _ _ y K _ _ _ b hb
  obtain ⟨B₂, hB₂⟩ := hM G p B Bs x L D J hC
  exact ggFixed_of_tableBAction (hA G p B Bs x L D J B₂ hC hB₂) hb

section Round12

theorem ggTBFixInput_of_round12 (hSR : TableBExcSmallRanks.GGTwF4ThreeRankInput)
    (hTBM : GGTableBModuleInputOn GGCorFourTwoOpenTableBRound12Label)
    (hTBA : GGTableBActionInputOn GGCorFourTwoOpenTableBRound12Label) : GGTBFixInput :=
  ggTBFixInput_of_tableB
    (ggTableBModuleInput_of_openRest3 hSR
      (ggTableBModuleInputOn_of_not_orthNsVac (S := GGCorFourTwoOpenTableBVacRest3Label)
        (ggTableBModuleInputOn_round11_of_round12 hTBM)))
    (ggTableBActionInput_of_openRest3 hSR
      (ggTableBActionInputOn_of_not_orthNsVac (S := GGCorFourTwoOpenTableBVacRest3Label)
        (ggTableBActionInputOn_round11_of_round12 hTBA)))

end Round12

end CFSG.StandardType
