module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5Q2

@[expose] def Q2CentEven : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L 1 F a →
      ∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
        S5.vIm h.le a (S5.jOff h.le L 2 δ (baseB _)) ≤ commutator (MSP.Sp4 F) →
        Zq M L ≤ Subgroup.centralizer (M : Set G)

@[expose] def Q2Cent55 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L 1 F a →
      ∀ δ : Vtx (puAmalgam h.le), (puAmalgam h.le).treeGraph.Adj (baseB _) δ →
        S5.jOff h.le L 2 δ (baseB _) ≠ S5.jOff h.le L 2 (baseA _) (baseB _) →
        Qv _ (baseA _) ≤ S5.jOff h.le L 2 δ (baseB _) →
        (∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
          Qv _ (baseB _) ≤ S5.vPre h.le a (MSP.stab l) ∧
          S5.jOff h.le L 2 (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) →
        ¬ S5.vIm h.le a (S5.jOff h.le L 2 (baseA _) (baseB _)) ≤ commutator (MSP.Sp4 F) →
        S5.vIm h.le a (S5.jOff h.le L 2 δ (baseB _)) ≤ commutator (MSP.Sp4 F) →
        Zq M L ≤ Subgroup.centralizer (M : Set G)

theorem q2Cent55_of_q2CentEven (H : Q2CentEven) : Q2Cent55 := by
  intro G _ _ M T L h hmin hb F _ _ a hd δ hβδ _ _ _ _ hJδ
  exact H G M T L h hmin hb F _ _ a hd δ hβδ hJδ

end S5Q2

end CFSG.Quasithin.MS93
