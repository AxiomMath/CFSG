module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Defs
public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3TSlide
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Base

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V} (D : D10Set L α)

@[expose] def bv (xβ : G) (i m : ℕ) : V :=
  (xβ ^ i)⁻¹ • (if m = 0 then D.beta 2 else (D.P 0).vert (m - 1))

end D10Set

structure IsBetaSet {L : ZLab Γ G} {α : V} (D : D10Set L α) (xβ : G) (η' : V) : Prop where
  fixβ : xβ • D.beta 2 = D.beta 2
  order3 : orderOf xβ = 3
  pair : D.IsYPair η'
  inverts : (D.y η' 0)⁻¹ * xβ * D.y η' 0 = xβ⁻¹
  collar : ∀ m, m ≤ 3 → D.bv xβ 2 m = (D.P 2).vert (m + 1)

structure IsW1 {L : ZLab Γ G} {α : V} (D : D10Set L α) (w : G) : Prop where
  fixes : w ∈ (D.P 2).stab G
  conj : w⁻¹ * D.x * w = D.x ^ 2
  sq : w * w = L.z (D.delta 2) * L.z α ∨ w * w = L.z (D.delta 2)

@[expose] def IsW1Star {L : ZLab Γ G} {α : V} (D : D10Set L α) (w : G) : Prop :=
  IsW1 D w ∧ (w * w = L.z (D.delta 2) →
    ¬ ∃ w' : G, IsW1 D w' ∧ w' * w' = L.z (D.delta 2) * L.z α)

structure Sec9Cfg (L : ZLab Γ G) where
  α : V
  D : D10Set L α
  xβ : G
  η' : V
  w : G
  c : G
  isBeta : IsBetaSet D xβ η'
  isW1 : IsW1 D w
  commutes : fcomm w (D.y η' 2) = 1
  gen : D.calpha = Subgroup.zpowers c

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

@[expose] def Star : Prop := IsW1Star S.D S.w

@[expose] def beta : V := S.D.beta 2

@[expose] def t : G := S.D.y S.η' 0

@[expose] def yEta (j : Fin 5) : G := S.D.y S.η' j

@[expose] def zMu1 (j : Fin 5) : G := L.z (S.D.alpha j)

@[expose] def zEta13 : G := L.z (S.D.delta 2)

@[expose] def zNb (i : Fin 3) : G := L.z (S.D.bv S.xβ i 1)

@[expose] def zMu (i : Fin 3) : G := L.z (S.D.bv S.xβ i 3)

@[expose] def zMuij (i : Fin 3) (j : Fin 5) : G := L.z ((S.xβ ^ (i : ℕ))⁻¹ • S.D.alpha j)

@[expose] def yMu (i : Fin 3) : G := S.zMuij i 0 * S.zMuij i 1

@[expose] def ub : G := S.zMuij 0 1 * S.zMuij 0 3 * L.z S.α

@[expose] def ubs : G := S.zMu 0 * S.zMu 1 * S.zMu 2 * S.zNb 1

@[expose] def wA (i : Fin 3) : G := (S.xβ ^ (i : ℕ))⁻¹ * S.w * S.xβ ^ (i : ℕ)

@[expose] def cA (i : Fin 3) : G := (S.xβ ^ (i : ℕ))⁻¹ * S.c * S.xβ ^ (i : ℕ)

end Sec9Cfg

end CFSG.Quasithin.Fan86
