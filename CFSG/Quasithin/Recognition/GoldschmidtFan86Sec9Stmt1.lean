module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Pres1
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan91star (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ (α : V) (D : D10Set L α), ∃ w : G, IsW1Star D w

@[expose] def Fan92 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    (Nat.card ↥(MulAction.stabilizer G S.α) = 5 * 2 ^ 11 →
      P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1 ∧
      Subgroup.closure (({S.D.x, S.w, L.z S.α} : Set G) ∪ Set.range S.yEta ∪
        Set.range S.zMu1) = MulAction.stabilizer G S.α) ∧
    (Nat.card ↥(MulAction.stabilizer G S.α) = 5 * 2 ^ 12 →
      P1Rel S.D.x S.w (L.z S.α) S.yEta S.zMu1 ∧ P1cRel S.D.x (L.z S.α) S.c S.yEta S.zMu1 ∧
      (fcomm S.w S.c = 1 ∨ S.w⁻¹ * S.c * S.w = S.c⁻¹) ∧
      Subgroup.closure (({S.D.x, S.w, L.z S.α, S.c} : Set G) ∪ Set.range S.yEta ∪
        Set.range S.zMu1) = MulAction.stabilizer G S.α)

@[expose] def Fan93 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, fcomm S.xβ S.ub = 1 ∧ fcomm S.xβ S.ubs = 1

@[expose] def Fan94a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    nbrStab Γ G S.beta = Subgroup.closure (({S.w, S.wA 1, S.c, S.ub} : Set G) ∪
      Set.range S.zMu ∪ Set.range S.yMu ∪ Set.range S.zNb) ∧
    MulAction.stabilizer G S.beta = Subgroup.closure ({S.xβ, S.t} : Set G) ⊔ nbrStab Γ G S.beta

@[expose] def Fan94b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    nbrStab Γ G S.beta =
      Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta ∧
    ballStab Γ G 2 S.beta =
      Subgroup.closure (insert S.ubs (Set.range S.yMu)) ⊔ ballStab Γ G 3 S.beta ∧
    ballStab Γ G 3 S.beta = Subgroup.closure (insert S.ub (Set.range S.zNb))

@[expose] def Fan94c (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    (Nat.card ↥S.D.calpha = 2 →
      ∃ φ : ↥(nbrStab Γ G S.beta) →* (Multiplicative (ZMod 4) × Multiplicative (ZMod 4)),
        Function.Surjective φ ∧
          φ.ker = (ballStab Γ G 2 S.beta).subgroupOf (nbrStab Γ G S.beta)) ∧
    (Nat.card ↥S.D.calpha = 4 →
      ∃ φ : ↥(nbrStab Γ G S.beta) →*
          (Multiplicative (ZMod 4) × Multiplicative (ZMod 4) × Multiplicative (ZMod 2)),
        Function.Surjective φ ∧
          φ.ker = (ballStab Γ G 2 S.beta).subgroupOf (nbrStab Γ G S.beta)) ∧
    (∃ φ : ↥(ballStab Γ G 2 S.beta) →* (Fin 3 → Multiplicative (ZMod 2)),
        Function.Surjective φ ∧
          φ.ker = (ballStab Γ G 3 S.beta).subgroupOf (ballStab Γ G 2 S.beta)) ∧
    (∃ φ : ↥(ballStab Γ G 3 S.beta) →* (Fin 3 → Multiplicative (ZMod 2)),
        Function.Surjective φ ∧
          φ.ker = (ballStab Γ G 4 S.beta).subgroupOf (ballStab Γ G 3 S.beta))

@[expose] def Fan94 (F : FanTree Γ G) (L : ZLab Γ G) : Prop := Fan94a F L ∧ Fan94b F L ∧ Fan94c F L

end CFSG.Quasithin.Fan86
