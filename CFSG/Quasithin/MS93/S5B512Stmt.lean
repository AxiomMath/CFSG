module

public import CFSG.Quasithin.MS93.S5Stmt

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S5B

section Defs

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

@[expose] def lamAt (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F] (a : ↥M →* ↥(StatedSp 2 F))
    (γ γ' δ : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ g : (puAmalgam h.le).Universal, g • γ = baseA _ ∧ g • geo _ γ γ' 1 = baseB _ ∧
    g • μ ∈ S5.lam h q a (g • γ') (g • δ)}

@[expose] def lamAllAt (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F)) (γ γ' : Vtx (puAmalgam h.le)) : Set (Vtx (puAmalgam h.le)) :=
  {μ | ∃ g : (puAmalgam h.le).Universal, g • γ = baseA _ ∧ g • geo _ γ γ' 1 = baseB _ ∧
    g • μ ∈ S5.lamAll h q a (g • γ')}

@[expose] def IsLamStep (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F)) (γ γ' μ : Vtx (puAmalgam h.le)) : Prop :=
  IsCritical _ γ γ' ∧ μ ∈ lamAt h q a γ γ' (geo _ γ γ' 2) ∧ IsCritical _ μ (geo _ γ γ' 2)

@[expose] def IsChain512 (h : PUHyp M T L) (q : ℕ) {F : Type} [Field F]
    (a : ↥M →* ↥(StatedSp 2 F)) (α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)) : Prop :=
  geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _ ∧
    IsLamStep h q a (geo _ (baseA (puAmalgam h.le)) α' 2) ν (baseA _) ∧
    geo _ (geo _ (baseA (puAmalgam h.le)) α' 2) ν 2 = α' ∧
    IsCritical _ (baseA (puAmalgam h.le)) α' ∧
    μ₁ ∈ S5.lam h q a α' (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
    IsCritical _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
    IsLamStep h q a μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) μ₂

end Defs

@[expose] def S512Nat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
    PUMin M T L → critDist (puAmalgam h.le) = 4 →
    ∀ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (a : ↥M →* ↥(StatedSp 2 F)),
      S5.IsSp4Data M T L k F a →
      ∀ α' ν μ₁ μ₂ : Vtx (puAmalgam h.le), IsChain512 h (2 ^ k) a α' ν μ₁ μ₂ →
        (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k →
        (Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2)).relIndex (ZM _ μ₁) = 2 ^ k →
        (S5.bSub h.le L (baseA _)).relIndex (ZM _ μ₁) = 2 ^ k →
        (S5.bSub h.le L μ₁).relIndex (ZM _ μ₂) = 2 ^ k →
        ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
          (a' : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F')),
          Fintype.card F' = 2 ^ k ∧ Function.Surjective a' ∧
          IsSumOfNaturalModulesVia (stab _ (baseA _)) (S5.nclStab _ (baseA _) (ZM _ μ₁))
            (S5.nclStab _ (baseA _) (ZM _ μ₁) ⊓ S5.bSub h.le L (baseA _)) a' false 1 ∧
          ⁅⁅S5.nclStab _ (baseA _) (ZM _ μ₁), puTrans h.le L (baseA _)⁆,
              ⁅S5.nclStab _ (baseA _) (ZM _ μ₁), puTrans h.le L (baseA _)⁆⁆ ≤
            S5.dSub h.le L (baseA _)

end S5B

end CFSG.Quasithin.MS93
