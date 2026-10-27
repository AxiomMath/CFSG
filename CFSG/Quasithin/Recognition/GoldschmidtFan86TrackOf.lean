module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Track

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

@[expose] def lineOfArc (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {a₀ a₁ a₂ : V} (h01 : Γ.Adj a₀ a₁) (h12 : Γ.Adj a₁ a₂) (h02 : a₀ ≠ a₂) (τ : G)
    (hτ0 : τ • a₀ = a₂) (hτ1 : τ • a₁ ≠ a₁) : Line Γ where
  vert i := τ ^ (i / 2) • (if i % 2 = 0 then a₀ else a₁)
  adj i := by
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · have e1 : (i + 1) / 2 = i / 2 := by omega
      have e2 : (i + 1) % 2 = 1 := by omega
      simp only [h, e1, e2, ite_true, one_ne_zero, ite_false]
      exact (hadj _ _ _).2 h01
    · have e1 : (i + 1) / 2 = i / 2 + 1 := by omega
      have e2 : (i + 1) % 2 = 0 := by omega
      simp only [h, e1, e2, one_ne_zero, ite_false, ite_true]
      rw [zpow_add_one, mul_smul, hτ0]
      exact (hadj _ _ _).2 h12
  nb i := by
    rcases Int.emod_two_eq_zero_or_one i with h | h
    · have e1 : (i + 2) / 2 = i / 2 + 1 := by omega
      have e2 : (i + 2) % 2 = 0 := by omega
      simp only [h, e1, e2, ite_true]
      rw [zpow_add_one, mul_smul, hτ0]
      exact fun he => h02 (MulAction.injective _ he)
    · have e1 : (i + 2) / 2 = i / 2 + 1 := by omega
      have e2 : (i + 2) % 2 = 1 := by omega
      simp only [h, e1, e2, one_ne_zero, ite_false]
      rw [zpow_add_one, mul_smul]
      exact fun he => hτ1 (MulAction.injective _ he).symm

theorem lineOfArc_translate (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {a₀ a₁ a₂ : V} (h01 : Γ.Adj a₀ a₁) (h12 : Γ.Adj a₁ a₂) (h02 : a₀ ≠ a₂) (τ : G)
    (hτ0 : τ • a₀ = a₂) (hτ1 : τ • a₁ ≠ a₁) (i : ℤ) :
    τ • (lineOfArc hadj h01 h12 h02 τ hτ0 hτ1).vert i =
      (lineOfArc hadj h01 h12 h02 τ hτ0 hτ1).vert (i + 2) := by
  have e1 : (i + 2) / 2 = i / 2 + 1 := by omega
  have e2 : (i + 2) % 2 = i % 2 := by omega
  simp only [lineOfArc, e1, e2]
  rw [← mul_smul, ← zpow_one_add, add_comm 1 (i / 2)]

theorem lineOfArc_vert_zero (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {a₀ a₁ a₂ : V} (h01 : Γ.Adj a₀ a₁) (h12 : Γ.Adj a₁ a₂) (h02 : a₀ ≠ a₂) (τ : G)
    (hτ0 : τ • a₀ = a₂) (hτ1 : τ • a₁ ≠ a₁) :
    (lineOfArc hadj h01 h12 h02 τ hτ0 hτ1).vert 0 = a₀ := by
  simp [lineOfArc]

theorem lineOfArc_vert_one (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {a₀ a₁ a₂ : V} (h01 : Γ.Adj a₀ a₁) (h12 : Γ.Adj a₁ a₂) (h02 : a₀ ≠ a₂) (τ : G)
    (hτ0 : τ • a₀ = a₂) (hτ1 : τ • a₁ ≠ a₁) :
    (lineOfArc hadj h01 h12 h02 τ hτ0 hτ1).vert 1 = a₁ := by
  simp [lineOfArc]

theorem lineOfArc_vert_two (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {a₀ a₁ a₂ : V} (h01 : Γ.Adj a₀ a₁) (h12 : Γ.Adj a₁ a₂) (h02 : a₀ ≠ a₂) (τ : G)
    (hτ0 : τ • a₀ = a₂) (hτ1 : τ • a₁ ≠ a₁) :
    (lineOfArc hadj h01 h12 h02 τ hτ0 hτ1).vert 2 = a₂ := by
  have := lineOfArc_translate hadj h01 h12 h02 τ hτ0 hτ1 0
  rw [lineOfArc_vert_zero, hτ0] at this
  simpa using this.symm

structure CrossPair (α β : V) (x y : G) : Prop where
  x_fix : x • α = α
  x_move : x • β ≠ β
  y_fix : y • β = β
  y_move : y • α ≠ α

namespace CrossPair

variable {α β : V} {x y : G}

theorem adj_left (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    (hαβ : Γ.Adj α β) (h : CrossPair α β x y) : Γ.Adj (x⁻¹ • β) α := by
  have := (hadj x⁻¹ β α).2 hαβ.symm
  rwa [inv_smul_eq_iff.2 h.x_fix.symm] at this

theorem ne_left (h : CrossPair α β x y) : x⁻¹ • β ≠ β :=
  fun he => h.x_move (inv_smul_eq_iff.1 he).symm

theorem trans_left (h : CrossPair α β x y) : (y * x) • (x⁻¹ • β) = β := by
  rw [mul_smul, smul_inv_smul, h.y_fix]

theorem trans_mid (h : CrossPair α β x y) : (y * x) • α ≠ α := by
  rw [mul_smul, h.x_fix]
  exact h.y_move

end CrossPair

@[expose] def trackOfPair (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {α β : V} {x y : G} (hαβ : Γ.Adj α β) (h : CrossPair α β x y) : Track Γ G where
  line := lineOfArc hadj (h.adj_left hadj hαβ) hαβ h.ne_left (y * x) h.trans_left h.trans_mid
  τ := y * x
  trans := lineOfArc_translate hadj (h.adj_left hadj hαβ) hαβ h.ne_left (y * x) h.trans_left
    h.trans_mid

section Pair

variable (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v) {α β : V} {x y : G}
  (hαβ : Γ.Adj α β) (h : CrossPair α β x y)

theorem trackOfPair_τ : (trackOfPair hadj hαβ h).τ = y * x := rfl

theorem trackOfPair_vert_one : (trackOfPair hadj hαβ h).line.vert 1 = α :=
  lineOfArc_vert_one hadj (h.adj_left hadj hαβ) hαβ h.ne_left (y * x) h.trans_left h.trans_mid

theorem trackOfPair_vert_two : (trackOfPair hadj hαβ h).line.vert 2 = β :=
  lineOfArc_vert_two hadj (h.adj_left hadj hαβ) hαβ h.ne_left (y * x) h.trans_left h.trans_mid

theorem trackOfPair_vert_zero : (trackOfPair hadj hαβ h).line.vert 0 = x⁻¹ • β :=
  lineOfArc_vert_zero hadj (h.adj_left hadj hαβ) hαβ h.ne_left (y * x) h.trans_left h.trans_mid

end Pair

end CFSG.Quasithin.Fan86
