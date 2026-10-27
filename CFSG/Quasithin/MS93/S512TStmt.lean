module

public import CFSG.Quasithin.MS93.S5B512Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512T

@[expose] def Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' → geo _ (baseA _) α' 1 = baseB _ →
      ∀ l : Submodule F (MSP.V4 F), S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l →
      ∀ μ : Vtx (puAmalgam h.le),
        (∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ = y • geo _ (baseA (puAmalgam h.le)) α' 2) →
        IsCritical _ μ (geo _ (baseA (puAmalgam h.le)) α' 2) →
        2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ) →
        ⁅ZM (puAmalgam h.le) μ, ZM (puAmalgam h.le) (geo _ (baseA (puAmalgam h.le)) α' 2)⁆ ≤
          stabCenter _ (baseA (puAmalgam h.le)) →
        False

@[expose] def TwoAlt2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂ →
        2 ^ k < (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) →
        (2 ^ k) ^ 2 < (Qv _ μ₁).relIndex (Qv _ (baseA (puAmalgam h.le))) →
        (∀ l : Submodule F (MSP.V4 F),
          ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) →
        (∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) →
        ¬ Xq M = Uq M T L ⊔ Zq M L →
        ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
          S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x →
          (μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
            μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) →
          ¬ puTrans h.le L (baseA _) ≤
            S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
              S5.zHat _ (baseA _) α' →
          False

@[expose] def ThreeAlt2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), S5B.IsChain512 h (2 ^ k) a α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        (∀ l : Submodule F (MSP.V4 F),
          ¬ S5.Case56 h (2 ^ k) a (geo _ (baseA (puAmalgam h.le)) α' 2) l) →
        (∃ l : Submodule F (MSP.V4 F), MSP.IsLine l ∧
          Qv _ (baseB (puAmalgam h.le)) ≤ S5.vPre h.le a (MSP.stab l) ∧
          S5.jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ S5.vPre h.le a (MSP.qLine l)) →
        ¬ Xq M = Uq M T L ⊔ Zq M L →
        ∀ g ∈ stab _ (baseA (puAmalgam h.le)), ∀ x ∈ puTrans h.le L (baseA _),
          S5.Concl55 h (2 ^ k) α' (geo _ (baseA (puAmalgam h.le)) α' 2) g x →
          (μ₁ = g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2 ∨
            μ₁ = x⁻¹ • g⁻¹ • geo _ (baseA (puAmalgam h.le)) α' 2) →
          ¬ puTrans h.le L (baseA _) ≤
            S5.jOff h.le L (2 ^ k) μ₁ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ⊔
              S5.zHat _ (baseA _) α' →
          ¬ Qv _ (geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 1) ≤ Subgroup.normalizer
            ((S5.uSub h.le L μ₁ ⊓ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) : Subgroup _) :
              Set (puAmalgam h.le).Universal) →
          (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k

end S512T

end CFSG.Quasithin.MS93
