module

public import CFSG.Quasithin.Background.C134L32CorrM
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ln2

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem exists_isC134CaseW (hC34 : CFSG.Quasithin.C134L32CorrM) {T Y : Subgroup G}
    (hMS : IsMSPair (Y ⊔ T) T) (hY : Y ∈ cComp (Y ⊔ T))
    (hTY : T ≤ Subgroup.normalizer (Y : Set G)) {α : ↥Y →* ↥(StatedSL 3 (ZMod 2))}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥Y) :
    ∃ i : ℕ, CFSG.Quasithin.IsC134CaseM i (Y ⊔ T) T Y :=
  hC34 G (Y ⊔ T) T Y hMS hY (Subgroup.coe_mul_of_right_le_normalizer_left Y T hTY)
    ⟨ZMod 2, inferInstance, inferInstance, α, by simp, hα, hker⟩


end CFSG.Quasithin.H13.Ln2
