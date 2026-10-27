module

public import CFSG.RankThree.PartTwo.Sec21.FF81SL32FixMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import TauCeti.GroupTheory.Sylow

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix

abbrev GL3 : Type := GL (Fin 3) (ZMod 2)

abbrev Mat3 : Type := Matrix (Fin 3) (Fin 3) (ZMod 2)

def adj3 (m : Mat3) : Mat3 :=
  !![m 1 1 * m 2 2 + m 1 2 * m 2 1, m 0 2 * m 2 1 + m 0 1 * m 2 2, m 0 1 * m 1 2 + m 0 2 * m 1 1;
     m 1 2 * m 2 0 + m 1 0 * m 2 2, m 0 0 * m 2 2 + m 0 2 * m 2 0, m 0 2 * m 1 0 + m 0 0 * m 1 2;
     m 1 0 * m 2 1 + m 1 1 * m 2 0, m 0 1 * m 2 0 + m 0 0 * m 2 1, m 0 0 * m 1 1 + m 0 1 * m 1 0]

def toGL (m : Mat3) : GL3 :=
  if h : m * adj3 m = 1 ∧ adj3 m * m = 1 then ⟨m, adj3 m, h.1, h.2⟩ else 1

def encM (m : Mat3) : ℕ :=
  (m 0 0).val + 2 * (m 0 1).val + 4 * (m 0 2).val + 8 * (m 1 0).val + 16 * (m 1 1).val +
    32 * (m 1 2).val + 64 * (m 2 0).val + 128 * (m 2 1).val + 256 * (m 2 2).val

def enc (g : GL3) : ℕ := encM (g : Mat3)

theorem encM_injective : Function.Injective encM := by
  intro a b h
  obtain ⟨a00, b00⟩ : (a 0 0).val < 2 ∧ (b 0 0).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a01, b01⟩ : (a 0 1).val < 2 ∧ (b 0 1).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a02, b02⟩ : (a 0 2).val < 2 ∧ (b 0 2).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a10, b10⟩ : (a 1 0).val < 2 ∧ (b 1 0).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a11, b11⟩ : (a 1 1).val < 2 ∧ (b 1 1).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a12, b12⟩ : (a 1 2).val < 2 ∧ (b 1 2).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a20, b20⟩ : (a 2 0).val < 2 ∧ (b 2 0).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a21, b21⟩ : (a 2 1).val < 2 ∧ (b 2 1).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  obtain ⟨a22, b22⟩ : (a 2 2).val < 2 ∧ (b 2 2).val < 2 := ⟨ZMod.val_lt _, ZMod.val_lt _⟩
  unfold encM at h
  have e00 : (a 0 0).val = (b 0 0).val := by omega
  have e01 : (a 0 1).val = (b 0 1).val := by omega
  have e02 : (a 0 2).val = (b 0 2).val := by omega
  have e10 : (a 1 0).val = (b 1 0).val := by omega
  have e11 : (a 1 1).val = (b 1 1).val := by omega
  have e12 : (a 1 2).val = (b 1 2).val := by omega
  have e20 : (a 2 0).val = (b 2 0).val := by omega
  have e21 : (a 2 1).val = (b 2 1).val := by omega
  have e22 : (a 2 2).val = (b 2 2).val := by omega
  ext i j
  apply ZMod.val_injective 2
  fin_cases i <;> fin_cases j <;> assumption

theorem enc_injective : Function.Injective enc := fun _ _ h => Units.ext (encM_injective h)

def h0 : List GL3 :=
  [
    toGL !![0,0,1;0,1,0;1,0,0], toGL !![0,0,1;0,1,1;1,0,1], toGL !![0,0,1;0,1,1;1,1,1],
    toGL !![0,0,1;1,0,0;0,1,1], toGL !![0,0,1;1,0,0;1,1,1], toGL !![0,0,1;1,0,1;0,1,1],
    toGL !![0,0,1;1,1,0;0,1,1], toGL !![0,0,1;1,1,0;1,0,0], toGL !![0,0,1;1,1,0;1,0,1],
    toGL !![0,0,1;1,1,1;1,0,1], toGL !![0,1,0;0,0,1;1,0,0], toGL !![0,1,0;0,0,1;1,1,1],
    toGL !![0,1,0;0,1,1;1,0,0], toGL !![0,1,0;0,1,1;1,1,0], toGL !![0,1,0;0,1,1;1,1,1],
    toGL !![0,1,0;1,0,1;1,0,0], toGL !![0,1,0;1,0,1;1,1,0], toGL !![0,1,0;1,1,0;1,1,1],
    toGL !![0,1,1;0,0,1;1,1,1], toGL !![0,1,1;0,1,0;1,1,0], toGL !![0,1,1;0,1,0;1,1,1],
    toGL !![0,1,1;1,0,1;1,1,1], toGL !![0,1,1;1,1,0;1,1,1], toGL !![0,1,1;1,1,1;1,0,1],
    toGL !![0,1,1;1,1,1;1,1,0]
  ]

def h1 : List GL3 :=
  [
    toGL !![0,0,1;0,1,0;1,1,0], toGL !![0,0,1;0,1,0;1,1,1], toGL !![0,0,1;0,1,1;1,0,0],
    toGL !![0,0,1;0,1,1;1,0,1], toGL !![0,0,1;0,1,1;1,1,0], toGL !![0,0,1;0,1,1;1,1,1],
    toGL !![0,0,1;1,0,0;0,1,0], toGL !![0,0,1;1,0,0;0,1,1], toGL !![0,0,1;1,0,0;1,1,1],
    toGL !![0,0,1;1,0,1;0,1,1], toGL !![0,0,1;1,0,1;1,1,0], toGL !![0,0,1;1,1,0;0,1,1],
    toGL !![0,0,1;1,1,1;0,1,0], toGL !![0,1,0;0,0,1;1,1,0], toGL !![0,1,0;0,1,1;1,0,0],
    toGL !![0,1,0;0,1,1;1,0,1], toGL !![0,1,0;1,0,0;1,0,1], toGL !![0,1,0;1,0,0;1,1,1],
    toGL !![0,1,0;1,0,1;1,0,0], toGL !![0,1,0;1,1,0;1,0,1], toGL !![0,1,0;1,1,0;1,1,1],
    toGL !![0,1,0;1,1,1;1,0,0], toGL !![0,1,1;0,1,0;1,0,0]
  ]

def h2 : List GL3 :=
  [
    toGL !![0,0,1;0,1,0;1,0,1], toGL !![0,0,1;0,1,0;1,1,1], toGL !![0,0,1;0,1,1;1,1,0],
    toGL !![0,0,1;1,0,0;0,1,0], toGL !![0,0,1;1,0,1;1,1,0], toGL !![0,0,1;1,1,0;1,0,0],
    toGL !![0,0,1;1,1,1;0,1,0], toGL !![0,0,1;1,1,1;0,1,1], toGL !![0,1,0;0,0,1;1,0,0],
    toGL !![0,1,0;0,0,1;1,1,1], toGL !![0,1,0;0,1,1;1,0,1], toGL !![0,1,0;0,1,1;1,1,1],
    toGL !![0,1,0;1,0,0;1,1,1], toGL !![0,1,0;1,0,1;1,0,0], toGL !![0,1,0;1,1,0;1,0,1],
    toGL !![0,1,0;1,1,0;1,1,1], toGL !![0,1,1;0,0,1;1,1,0], toGL !![0,1,1;0,0,1;1,1,1],
    toGL !![0,1,1;0,1,0;1,0,0]
  ]

def h3 : List GL3 :=
  [
    toGL !![0,0,1;0,1,0;1,0,0], toGL !![0,0,1;0,1,0;1,1,1], toGL !![0,0,1;0,1,1;1,0,1],
    toGL !![0,0,1;0,1,1;1,1,1], toGL !![0,0,1;1,0,0;0,1,0], toGL !![0,0,1;1,0,0;0,1,1],
    toGL !![0,0,1;1,0,0;1,1,0], toGL !![0,0,1;1,0,0;1,1,1], toGL !![0,0,1;1,0,1;0,1,0],
    toGL !![0,1,0;0,0,1;1,0,0], toGL !![0,1,0;0,0,1;1,1,0], toGL !![0,1,0;0,1,1;1,0,0],
    toGL !![0,1,0;0,1,1;1,0,1], toGL !![0,1,0;0,1,1;1,1,0]
  ]

def g0 : GL3 := toGL !![1,0,0;0,1,0;0,0,1]

def g1 : GL3 := toGL !![1,1,0;0,1,0;0,0,1]

def g2 : GL3 := toGL !![0,0,1;0,1,1;1,1,1]

def g3 : GL3 := toGL !![1,0,1;0,0,1;1,1,1]

def y0 : GL3 := toGL !![0,0,1;0,1,0;1,0,1]

theorem parity_data : ParityCert enc (prodList y0 g0 g1 g2 g3 h0 h1 h2 h3) := by
  unfold ParityCert
  refine ⟨?_, ?_⟩ <;> decide +kernel

theorem y0_cube : y0 * y0 * y0 = 1 := by decide +kernel

theorem y0_ne_one : y0 ≠ 1 := by decide +kernel

def s0 : GL3 := toGL !![0,0,1;0,1,0;1,0,0]

theorem s0_sq : s0 * s0 = 1 := by decide +kernel

theorem s0_conj : s0 * y0 * s0 = y0 * y0 := by decide +kernel

theorem orderOf_y0 : orderOf y0 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (by rw [pow_three']; exact y0_cube) y0_ne_one

theorem card_GL3 : Nat.card GL3 = 168 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  show Nat.card (GL (Fin 3) (ZMod 2)) = 168
  rw [Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
  norm_num

theorem card_le_pow_four_GL {V : Type*} [Group V] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hV : ∀ v : V, v * v = 1) (ρ : GL3 →* MulAut V) :
    Nat.card V ≤ Nat.card {v : V // ρ y0 v = v} ^ 4 :=
  card_le_pow_four hcomm hV ρ y0_cube g0 g1 g2 g3 h0 h1 h2 h3 enc enc_injective parity_data

theorem exists_conj_y0 {z : GL3} (hz : orderOf z = 3) : ∃ c : GL3, c * y0 * c⁻¹ = z := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : ¬ 3 ^ 2 ∣ Nat.card GL3 := by rw [card_GL3]; norm_num
  obtain ⟨c, hc⟩ := TauCeti.exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd h9 hz orderOf_y0
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hz3 : z * z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz, pow_three'] at h
    exact h
  have hr : z ^ m = z ^ (m % 3) := by
    have := zpow_mod_orderOf z m
    rw [hz] at this
    push_cast at this
    exact this.symm
  have hs0 : s0⁻¹ = s0 := inv_eq_of_mul_eq_one_right s0_sq
  have hr3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hr3 with h0 | h1 | h2
  · exfalso
    rw [h0, zpow_zero] at hr
    rw [hr] at hm
    have : y0 = 1 := by
      calc y0 = c⁻¹ * (c * y0 * c⁻¹) * c := by group
        _ = c⁻¹ * 1 * c := by rw [← hm]
        _ = 1 := by group
    exact y0_ne_one this
  · refine ⟨c, ?_⟩
    rw [hr, h1, zpow_one] at hm
    exact hm.symm
  · refine ⟨c * s0, ?_⟩
    rw [hr, h2, zpow_two] at hm
    have e : c * s0 * y0 * (c * s0)⁻¹ = (c * y0 * c⁻¹) * (c * y0 * c⁻¹) := by
      rw [mul_inv_rev, hs0]
      calc c * s0 * y0 * (s0 * c⁻¹) = c * (s0 * y0 * s0) * c⁻¹ := by group
        _ = c * (y0 * y0) * c⁻¹ := by rw [s0_conj]
        _ = (c * y0 * c⁻¹) * (c * y0 * c⁻¹) := by group
    rw [mul_assoc c s0 y0, ← mul_assoc c s0 y0] at e
    rw [e, ← hm]
    calc z * z * (z * z) = z * (z * z * z) := by group
      _ = z := by rw [hz3, mul_one]

end CFSG.RankThree.PartTwo.Sec21.FF81.SL32Fix
