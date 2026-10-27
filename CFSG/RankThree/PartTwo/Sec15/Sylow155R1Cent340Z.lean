module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1CentTau
public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340W
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340Q
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Cent340P
import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

variable {G : Type} [Group G] [Finite G]

namespace Res1Tau

variable {Q : ∀ (X : Type) [Group X], Prop} {P : ∀ (Y : Type) [Group Y], Prop}
  {A : Subgroup G} {c : G} {L X K Y M T P' : Subgroup G} {Yc : Subgroup (Res1Q A L)} {z : G}

theorem le_normalizer_of_competing (τ : Res1Tau Q P A c L X K Y M T P' Yc z)
    (hbot : Item145BotS14) (h1444 : Item1444 A (lB A))
    (hN : n155 A K ≤ Subgroup.normalizer (K : Set G)) {M' W : Subgroup G}
    (hC' : Ctx155 A X K Y M' T) (hW2 : IsPGroup 2 W) (hWM : W ≤ M')
    (hBW : A ⊔ Y ≤ Subgroup.normalizer (W : Set G)) : W ≤ Subgroup.normalizer (X : Set G) := by
  have hX4 : X ∈ scriptY4 A (lB A) := τ.ctx.res ▸ τ.ctx.isY.2.1
  have hXY : X ≤ Y := τ.ctx.res ▸ Sec14.oPrimeResidualOf_le_self 3 Y
  have hBM : A ⊔ Y ≤ M := SetLike.coe_subset_coe.mp τ.ctx.mem_m.2
  have hMX : M ≤ Subgroup.normalizer (X : Set G) := τ.m_eq.le
  refine res1340_le_normalizer_of_stable (Sec15.isPerfect_of_mem_scriptY4 hX4) hW2
    (hXY.trans le_sup_right) hBW (hBM.trans hMX) ?_
  intro Z hZW hBZ hZX
  have hZ2 : IsPGroup 2 Z := hW2.to_le hZW
  have hZQ : Z ∈ scriptQ A (lB A) :=
    res1340_mem_scriptQ_of_commutator_eq τ.sec15 hbot h1444 τ.i146 hX4 hZ2
      (le_sup_left.trans hBZ) ((hXY.trans le_sup_right).trans hBZ) hZX
  have hZR : Z ≤ CFSG.Open.pCoreOf 2 Y :=
    τ.le_pCoreOf_of_competing h1444 (hbot _ _ _ _ τ.std) hN hC' hZ2 hZQ
      (le_sup_right.trans hBZ) (hZW.trans hWM)
  exact hZR.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans
    ((le_sup_right.trans hBM).trans hMX))

end Res1Tau

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
