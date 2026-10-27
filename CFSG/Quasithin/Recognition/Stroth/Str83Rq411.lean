module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArcRadius
import CFSG.Quasithin.Recognition.Stroth.Str83Rq410a

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem IsMaxArc.two_mul_add_le_of_commutator_ne_bot {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {ε : ℤ} {n b₁ bh : ℕ} (h : t.IsMaxArc ε n)
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hh : t.IsFixRadius (ε + 1 + b₁) bh)
    (hle : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁))
    (hne : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≠ ⊥) : 2 * b₁ + bh ≤ n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hlt
  push_neg at hlt
  have hRw : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Gw (ε + 1 - b₁) (ε + 1 + b₁ + bh) := by
    intro y hy
    have h1 := h₁.le_Gw (mem_inf.mp (hle hy)).1
    have h2 := hh.le_Gw (mem_inf.mp (hle hy)).2
    refine mem_win_iff.mpr fun i hi1 hi2 => ?_
    by_cases hi : i ≤ ε + 1 + b₁
    · exact mem_win_iff.mp h1 i hi1 hi
    · exact mem_win_iff.mp h2 i (by omega) hi2
  have hRp : IsPGroup 2 ↥⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ :=
    (t.isPGroup_Zv (ε + 1)).to_le (hle.trans inf_le_left)
  have h3 := t.le_pCoreOf_Gw hfr (by omega) hRp hRw
  rw [h.pCoreOf_eq_bot _ _ (by push_cast; omega)] at h3
  exact hne (le_bot_iff.mp h3)

theorem IsMaxArc.eq_two_of_even_of_commutator_ne_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {m b₁ : ℕ}
    (h : t.IsMaxArc ε (2 * m)) (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Even b₁)
    (hle : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁))
    (hne : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≠ ⊥) : b₁ = 2 ∧ m = 3 := by
  obtain ⟨k, hk⟩ := hb₁
  have hh : t.IsFixRadius (ε + 1 + b₁) b₁ := by
    have := Track.IsFixRadius.shift t h₁ (k : ℤ)
    rwa [show ε + 1 + 2 * (k : ℤ) = ε + 1 + (b₁ : ℤ) by omega] at this
  have h1 := Track.IsMaxArc.two_mul_add_le_of_commutator_ne_bot t hfr h h₁ hh hle hne
  have h2 := Track.IsMaxArc.fixRadius_add_one t hfr h h₁
  have h3 := Track.IsFixRadius.one_le t hfr h₁
  omega

theorem IsMaxArc.of_odd_of_commutator_ne_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) {ε : ℤ} {m b₀ b₁ : ℕ}
    (h : t.IsMaxArc ε (2 * m)) (h₀ : t.IsFixRadius ε b₀) (h₁ : t.IsFixRadius (ε + 1) b₁)
    (hb₁ : Odd b₁)
    (hle : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁))
    (hne : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≠ ⊥) :
    b₁ + 1 = m ∧ 1 ≤ b₀ ∧ b₀ ≤ 2 ∧ (m = 2 ∨ (m = 4 ∧ b₀ = 2)) := by
  obtain ⟨k, hk⟩ := hb₁
  have hh : t.IsFixRadius (ε + 1 + b₁) b₀ := by
    have := Track.IsFixRadius.shift t h₀ ((k : ℤ) + 1)
    rwa [show ε + 2 * ((k : ℤ) + 1) = ε + 1 + (b₁ : ℤ) by omega] at this
  have h1 := Track.IsMaxArc.two_mul_add_le_of_commutator_ne_bot t hfr h h₁ hh hle hne
  have h2 := Track.IsMaxArc.fixRadius_add_one t hfr h h₁
  have h3 := Track.IsMaxArc.fixRadius_self t hfr h h₀
  have h4 := Track.IsFixRadius.one_le t hfr h₀
  omega

theorem IsFixRadius.commutator_eq_bot_of_even {a f : ℕ}
    (hfr : Frame L1 L2 S a f) {v : ℤ} {b : ℕ} (h : t.IsFixRadius v b) (hv : Even v)
    (hb : Even b) : ⁅t.Zv v, t.Zv (v + b)⁆ = ⊥ := by
  obtain ⟨k, rfl⟩ := hv
  obtain ⟨c, hc⟩ := hb
  have h0 : t.IsFixRadius 0 b := by
    have := Track.IsFixRadius.shift t h (-k)
    rwa [show k + k + 2 * -k = 0 by ring] at this
  have hb' : t.IsFixRadius (b : ℤ) b := by
    have := Track.IsFixRadius.shift t h0 (c : ℤ)
    rwa [show (0 : ℤ) + 2 * (c : ℤ) = b by omega] at this
  have hZb : t.Zv b ≤ t.Gv 0 := by
    have := hb'.le_Gw
    exact this.trans (win_le_qv (by omega) (by omega))
  have hZ0 : t.Zv 0 ≤ t.Gw (-(b : ℤ)) b := by
    have := h0.le_Gw
    rwa [zero_sub, zero_add] at this
  have hZ0' : ¬ t.Zv 0 ≤ t.Gv (b + 1) := by
    have := h0.not_le_Gv
    rwa [zero_add] at this
  have h1 := t.commutator_Zv_zero_eq_bot_of_even hfr ⟨c, hc⟩ hZ0 hZ0' hZb
  have h2 := congrArg (Subgroup.map (MulAut.conj ((t.x₂ * t.x₁) ^ k)).toMonoidHom) h1
  rw [Subgroup.map_commutator, Subgroup.map_bot] at h2
  rw [map_qv_tau_pow, map_qv_tau_pow] at h2
  rwa [show (0 : ℤ) + 2 * k = k + k by ring, show (b : ℤ) + 2 * k = k + k + b by ring] at h2

end Track

end CFSG.Quasithin.Stroth.Rq
