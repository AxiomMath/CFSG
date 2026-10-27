module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.H13.A6Setting134

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem s134_normalizer_le_M (S : A6.Setting134 G T L V) {X : Subgroup G} (hX1 : X ≠ ⊥)
    (hX2 : IsPGroup 2 X) (hLT : L ⊔ T ≤ normalizer (X : Set G)) :
    normalizer (X : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨X, hX1, hX2, rfl⟩ : IsTwoLocal (normalizer (X : Set G)))
  have h := S.uniqueM.2 M' ⟨hM', hLT.trans hM'le⟩
  exact h ▸ hM'le

end CFSG.Quasithin.H13.U3
