module

public import CFSG.Quasithin.MS93.S5B512Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

@[expose] def S512One56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      (∃ l, S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) →
      ∀ δ' : Vtx (puAmalgam h.le), IsCritical _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' →
        geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) δ' 2 = α' →
        baseA _ ∈ lamAllAt h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) δ' →
        ∀ μ ∈ S5.lam h (2 ^ k) a α' (geo _ (baseA (puAmalgam h.le)) α' 2),
          S5.zHat _ (baseA (puAmalgam h.le)) α' ≤ Subgroup.normalizer
            (((S5.uSub h.le L μ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)) ⊔
              XM _ (baseA (puAmalgam h.le)) : Subgroup _) : Set _)

@[expose] def ZZ56 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ l : Submodule F (MSP.V4 F),
        S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
        ZM _ (baseA (puAmalgam h.le)) ⊓ ZM _ (geo _ (baseA (puAmalgam h.le)) α' 2) ≤
          Subgroup.centralizer (S5.vPre h.le a (MSP.qLine l) : Set (puAmalgam h.le).Universal)

end S5B

end CFSG.Quasithin.MS93
