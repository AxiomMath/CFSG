module

public import CFSG.Quasithin.EmptyFaithful.S146yA6Mod
public import CFSG.Quasithin.EmptyFaithful.S146zNFinH

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

@[expose] def x0A6 : A6 := ⟨x0P, mem_alternatingGroup.mpr sign_x0P⟩

@[expose] def y0A6 : A6 := ⟨y0P, mem_alternatingGroup.mpr sign_y0P⟩

theorem x0A6_ne_one : x0A6 ≠ 1 := by
  intro h
  have := congrArg Subtype.val h
  revert this
  unfold x0A6 x0P
  decide

section Setup

variable {W : Type} [CommGroup W] [Finite W]

structure Setup (ρ : A6 →* MulAut W) : Prop where
  sq : ∀ w : W, w * w = 1
  card : Nat.card W = 16
  inj : Function.Injective ρ

theorem fc_modEq_prime_pow (ρ : A6 →* MulAut W) (p n : ℕ) [Fact p.Prime] {g : A6}
    (hg : g ^ (p ^ n) = 1) : Nat.card W ≡ fc ρ g [MOD p] := by
  classical
  let H : Subgroup (MulAut W) := Subgroup.zpowers (ρ g)
  have hpow : ρ g ^ (p ^ n) = 1 := by rw [← map_pow, hg, map_one]
  have hH : IsPGroup p H := by
    intro x
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine ⟨n, ?_⟩
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hpow, one_zpow]
  have h1 := hH.card_modEq_card_fixedPoints W
  have h2 : Nat.card (MulAction.fixedPoints H W) = fc ρ g := by
    unfold fc
    refine Nat.card_congr (Equiv.subtypeEquivRight fun m => ?_)
    rw [mem_fixSub, MulAction.mem_fixedPoints]
    constructor
    · intro h
      exact h ⟨ρ g, Subgroup.mem_zpowers _⟩
    · intro h x
      have hst : ρ g ∈ MulAction.stabilizer (MulAut W) m := by
        rw [MulAction.mem_stabilizer_iff]
        exact h
      have := Subgroup.zpowers_le.mpr hst x.2
      exact (MulAction.mem_stabilizer_iff.mp this)
  rw [h2] at h1
  exact h1

omit [Finite W] in
theorem Setup.nontrivial {ρ : A6 →* MulAut W} (h : Setup ρ) : ∃ g, ρ g ≠ 1 := by
  refine ⟨x0A6, fun h1 => ?_⟩
  have := h.inj (h1.trans (map_one ρ).symm)
  exact x0A6_ne_one this

theorem Setup.fc_five {ρ : A6 →* MulAut W} (h : Setup ρ) {g : A6} (hg1 : g ≠ 1) (hg5 : g ^ 5 = 1) :
    fc ρ g = 1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hd := fc_dvd ρ g
  have hm := fc_modEq_prime_pow ρ 5 1 (g := g) (by simpa using hg5)
  have hlt := fc_lt h.nontrivial hg1
  rw [h.card] at hd hm hlt
  have hle : fc ρ g ≤ 16 := Nat.le_of_dvd (by norm_num) hd
  generalize fc ρ g = f at *
  unfold Nat.ModEq at hm
  interval_cases f <;> simp_all

end Setup

end CFSG.Quasithin.A6Fin
