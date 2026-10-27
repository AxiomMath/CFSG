module

import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.L32ANotation
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem le_normalizer_L_of (h1332 : Stmt13_3_2) (h : Hyp147 G T L V) {X : Subgroup G}
    (hLTX : L ⊔ T ≤ X) (hX : pCoreOf 2 X ≠ ⊥) : X ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, ⟨-, -, -, huniq⟩, -, -⟩ := h1332 G T L h.hyp.h13 L h.hyp.h13.faithful
  obtain ⟨M', hM'max, hXM'⟩ := exists_inM_of_pCoreOf_ne_bot hX
  rw [← huniq M' hM'max (hLTX.trans hXM')]
  exact hXM'

theorem card_of_lieModel_psl_three_two {X : Type} [Group X] (h : LieModel X .PSL 3 2 1) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two (h.statedClassicalModel (by decide))

end CFSG.Quasithin.H13.L32A.C
