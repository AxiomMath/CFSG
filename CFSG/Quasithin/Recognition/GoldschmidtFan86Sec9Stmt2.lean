module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Defs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def Fan95a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    (S.w * S.w = S.zEta13 * L.z S.α → ∃ e₁ e₂ e₃ e₄ : Fin 2,
      S.wA 1 = S.yEta 3 * S.yEta 4 * S.zMu1 3 * S.zMu1 0 ^ (e₁ : ℕ) * S.zMu1 1 ^ (e₂ : ℕ) *
        S.zMu1 2 ^ (e₃ : ℕ) * L.z S.α ^ (e₄ : ℕ)) ∧
    (S.w * S.w = S.zEta13 → Nat.card ↥S.D.calpha = 4 ∧ ∃ e₁ e₂ e₃ e₄ : Fin 2,
      S.wA 1 = S.yEta 1 * S.yEta 4 * S.c * S.zMu1 0 ^ (e₁ : ℕ) * S.zMu1 2 ^ (e₂ : ℕ) *
        S.zMu1 3 ^ (e₃ : ℕ) * L.z S.α ^ (e₄ : ℕ))

@[expose] def Fan95b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, Nat.card ↥S.D.calpha = 4 → ∃ d₁ d₂ d₃ d₄ : Fin 2,
    S.cA 1 = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.c * S.zMu1 0 ^ (d₁ : ℕ) * S.zMu1 2 ^ (d₂ : ℕ) *
      S.zMu1 4 ^ (d₃ : ℕ) * L.z S.α ^ (d₄ : ℕ)

@[expose] def Fan95c (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, S.yMu 0 * S.yMu 1 * S.yMu 2 = 1

@[expose] def Fan95d (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    S.zMu 0 = S.zMu1 0 ∧ S.zMu 2 = S.zEta13 ∧ S.zMu 1 = S.t⁻¹ * S.zMu 2 * S.t ∧
    S.zNb 0 = L.z S.α ∧ S.zNb 1 = S.zMu1 2 * L.z S.α ∧ S.zNb 2 = S.zMu1 2 ∧
    S.yMu 1 = S.yMu 0 * S.yMu 2 ∧
    (S.w * S.w = S.zEta13 * L.z S.α → S.yMu 2 = S.yEta 2 * S.zNb 2) ∧
    (S.w * S.w = S.zEta13 → S.yMu 2 = S.yEta 2 * S.ub * S.zNb 2) ∧
    S.ub = S.zMu1 0 * S.zMu1 4 * S.zNb 1

@[expose] def Fan95 (F : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  Fan95a F L ∧ Fan95b F L ∧ Fan95c F L ∧ Fan95d F L

@[expose] def Fan96a (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, S.w⁻¹ * S.yMu 0 * S.w = S.yMu 0 * S.ub * S.zNb 0 ∧
    (S.w * S.w = S.zEta13 * L.z S.α → S.w⁻¹ * S.yMu 2 * S.w = S.yMu 2) ∧
    (S.w * S.w = S.zEta13 → S.w⁻¹ * S.yMu 2 * S.w = S.yMu 2 * S.zNb 2)

@[expose] def Fan96b (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, Nat.card ↥S.D.calpha = 4 →
    S.c⁻¹ * S.yMu 0 * S.c = S.yMu 0 ∧
      ∀ i : Fin 3, i ≠ 0 → S.c⁻¹ * S.yMu i * S.c = S.yMu i * S.zNb 2

@[expose] def Fan96 (F : FanTree Γ G) (L : ZLab Γ G) : Prop := Fan96a F L ∧ Fan96b F L

@[expose] def Fan97 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    (S.w * S.w = S.zEta13 * L.z S.α → ∃ e₁ e₂ e₃ : Fin 2,
      S.wA 1 = S.yEta 3 * S.yEta 4 * S.zMu1 3 * S.zMu1 0 ^ (e₁ : ℕ) * S.zMu1 1 ^ (e₁ : ℕ) *
        S.zMu1 2 ^ (e₂ : ℕ) * L.z S.α ^ (e₃ : ℕ)) ∧
    (S.w * S.w = S.zEta13 → Nat.card ↥S.D.calpha = 4 ∧ ∃ e₁ e₂ e₃ : Fin 2,
      S.wA 1 = S.yEta 1 * S.yEta 4 * S.c * S.zMu1 0 ^ (e₁ : ℕ) * S.zMu1 3 ^ (e₁ : ℕ) *
        S.zMu1 2 ^ (e₂ : ℕ) * L.z S.α ^ (e₃ : ℕ))

@[expose] def Fan98 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L,
    (S.w * S.w = S.zEta13 * L.z S.α → ∃ e₁ e₂ : Fin 2,
      S.wA 1 = S.yEta 3 * S.yEta 4 * S.zMu1 3 * S.zNb 2 ^ (e₁ : ℕ) * S.zNb 0 ^ (e₂ : ℕ)) ∧
    (S.w * S.w = S.zEta13 → Nat.card ↥S.D.calpha = 4 ∧ ∃ e₁ e₂ : Fin 2,
      S.wA 1 = S.yEta 1 * S.yEta 4 * S.c * S.zNb 2 ^ (e₁ : ℕ) * S.zNb 0 ^ (e₂ : ℕ))

@[expose] def Fan99 (_ : FanTree Γ G) (L : ZLab Γ G) : Prop :=
  ∀ S : Sec9Cfg L, Nat.card ↥S.D.calpha = 4 →
    (S.w * S.w = S.zEta13 * L.z S.α → ∃ d₁ d₂ : Fin 2,
      S.cA 1 = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.zMu1 4 * S.c * S.zNb 2 ^ (d₁ : ℕ) *
        S.zNb 0 ^ (d₂ : ℕ)) ∧
    (S.w * S.w = S.zEta13 → ∃ d₁ d₂ : Fin 2,
      S.cA 1 = S.yEta 1 * S.yEta 3 * S.zMu1 3 * S.zMu1 0 * S.c * S.zNb 2 ^ (d₁ : ℕ) *
        S.zNb 0 ^ (d₂ : ℕ)) ∧
    fcomm (S.wA 1) (S.cA 1) = 1

end CFSG.Quasithin.Fan86
