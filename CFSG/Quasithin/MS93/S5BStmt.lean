module

public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

@[expose] def Q2Cent : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L 1 F a → Zq M L ≤ Subgroup.centralizer (M : Set G)

@[expose] def S58 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        (∃ μ ∈ S5.lamAll h (2 ^ k) a α', IsCritical _ μ (geo _ α' (baseA _) 2)) ∧
          ¬ Vv _ (baseA (puAmalgam h.le)) ≤ Qv _ (geo _ α' (baseA _) 2) ∧
          2 ^ k ≤ (S5.bSub h.le L (baseA _)).relIndex
            (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2))

@[expose] def S59 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        2 ^ k < (S5.bSub h.le L (baseA _)).relIndex
          (S5.uSub h.le L (geo _ (baseA (puAmalgam h.le)) α' 2))

@[expose] def S510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 4 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        ∃ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l

@[expose] def S511 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → critDist (puAmalgam h.le) = 4

@[expose] def S512b4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a → False

theorem s512_of_parts (h511 : S511) (h512 : S512b4) : S512 := by
  intro G _ _ M T L h hmin hb hfull
  obtain ⟨k, F, _, _, a, hd⟩ := S5.isSp4Full_iff.1 hfull
  exact h512 G M T L h hmin (h511 G M T L h hmin hb k F _ _ a hd) k F _ _ a hd

end S5B

end CFSG.Quasithin.MS93
