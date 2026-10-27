module

public import CFSG.Quasithin.MS93.S5A56EStmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] def Opp56 (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F)) (l : Submodule F (MSP.V4 F)) (g x : (puAmalgam h.le).Universal) :
    Prop :=
  ∀ E₁ E₂ : Subgroup (puAmalgam h.le).Universal, IsPGroup 2 E₁ → IsPGroup 2 E₂ →
    E₁ ≤ rconj (g * x) (vPre h.le a (MSP.qLine l)) → E₂ ≤ vPre h.le a (MSP.qLine l) →
    q ^ 2 < (Qv _ (baseA _)).relIndex E₁ → q ^ 2 < (Qv _ (baseA _)).relIndex E₂ →
    E₁ ⊔ E₂ ⊔ Qv _ (baseA _) = stab _ (baseA _)

@[expose] def Concl56f (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F)) (α' : Vtx (puAmalgam h.le)) (l : Submodule F (MSP.V4 F))
    (g x : (puAmalgam h.le).Universal) : Prop :=
  Concl56e h q a α' l g x ∧ Opp56 h q a l g x

@[expose] def S56f : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → 2 < critDist (puAmalgam h.le) →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      IsSp4Data M T L k F a →
      ∀ α' : Vtx (puAmalgam h.le), IsCritical _ (baseA _) α' →
        geo _ (baseA _) α' 1 = baseB _ →
        ∀ l : Submodule F (MSP.V4 F), MSP.IsLine l →
          Qv _ (baseB _) ≤ vPre h.le a (MSP.stab l) →
          jOff h.le L (2 ^ k) (baseA _) (baseB _) ≤ vPre h.le a (MSP.qLine l) →
          ∃ g ∈ stab _ (baseA _), ∃ x ∈ puTrans h.le L (baseA _),
            Concl56f h (2 ^ k) a α' l g x

end S5

end CFSG.Quasithin.MS93
