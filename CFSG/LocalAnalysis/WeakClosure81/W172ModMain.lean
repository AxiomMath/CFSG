module

public import CFSG.LocalAnalysis.WeakClosure81.W172ModAb
public import CFSG.LocalAnalysis.WeakClosure81.W172ModCls
public import CFSG.SignalizerFunctorTheorem.Quadratic.Offenders

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup
open scoped commutatorElement

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

private theorem w172_comm_of_commutator_eq_bot {Y : Subgroup (LGL 2 W)}
    (h : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) = ⊥) : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a := by
  intro a ha b hb
  have h1 : ⁅a, b⁆ ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)) := Subgroup.commutator_mem_commutator ha hb
  rw [h, Subgroup.mem_bot] at h1
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem w172_mod_exists_moving {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup (LGL 2 W)} (hexp : ∀ y ∈ Y, y ^ p = 1)
    (hcl : (⁅⁅Y, Y⁆, Y⁆ : Subgroup (LGL 2 W)) = ⊥)
    (hZ : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≠ ⊥ → ∀ z ∈ Y, (∀ y ∈ Y, y * z = z * y) →
      z ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W))) {a : ℕ}
    (hcard : Nat.card Y = p ^ a * Nat.card (⁅Y, Y⁆ : Subgroup (LGL 2 W))) (ha : 2 ≤ a) :
    ∃ y ∈ Y, y ∉ (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ∧
      ∀ y' ∈ Y, y⁻¹ * y' ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)) →
      (a = 2 → 2 * orderOf (2 : ZMod p) ≤
        Module.finrank (ZMod 2) ↥(commSub (zpowers y'))) ∧
      (3 ≤ a → 16 * a * orderOf (2 : ZMod p) ≤
        27 * Module.finrank (ZMod 2) ↥(commSub (zpowers y'))) := by
  by_cases hb : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) = ⊥
  · have hcard' : Nat.card Y = p ^ a := by
      rw [hb, Subgroup.card_bot, mul_one] at hcard
      exact hcard
    obtain ⟨y, hyY, hy1, h2, h3⟩ :=
      w172_ab_exists_moving hp hp2 (w172_comm_of_commutator_eq_bot hb) hexp hcard' ha
    refine ⟨y, hyY, ?_, ?_⟩
    · rw [hb, Subgroup.mem_bot]
      exact hy1
    · intro y' _ hyy'
      rw [hb, Subgroup.mem_bot, inv_mul_eq_one] at hyy'
      subst hyy'
      exact ⟨h2, h3⟩
  · exact w172_cls_exists_moving hp hp2 hexp hcl hb (hZ hb) hcard ha

theorem w172_finrank_commSub_le_add {d y : LGL 2 W} {n : ℕ} (hd : d ^ 2 = 1) (hn : Odd n)
    (hy : y ^ n = 1) (hdy : d * y * d⁻¹ = y⁻¹) :
    Module.finrank (ZMod 2) ↥(commSub (zpowers y)) ≤
      Module.finrank (ZMod 2) ↥(commSub (zpowers d)) +
      Module.finrank (ZMod 2) ↥(commSub (zpowers (y⁻¹ * d * y))) := by
  haveI : FiniteDimensional (ZMod 2) W := Module.Finite.of_finite
  have hdd : d * d = 1 := by rw [← pow_two]; exact hd
  have hz : d * (y⁻¹ * d * y) = y ^ 2 := by
    calc d * (y⁻¹ * d * y) = d * ((d * y * d⁻¹) * d * y) := by rw [hdy]
      _ = (d * d) * y * y := by group
      _ = y ^ 2 := by rw [hdd, one_mul, pow_two]
  have hyz : y ∈ zpowers (y ^ 2) := by
    obtain ⟨m, rfl⟩ := hn
    refine ⟨((m + 1 : ℕ) : ℤ), ?_⟩
    show (y ^ 2) ^ ((m + 1 : ℕ) : ℤ) = y
    rw [zpow_natCast, ← pow_mul]
    calc y ^ (2 * (m + 1)) = y ^ (2 * m + 1) * y := by rw [← pow_succ]; ring_nf
      _ = y := by rw [hy, one_mul]
  have hsup : ∀ A B : Subgroup (LGL 2 W), commSub (A ⊔ B) ≤ commSub A ⊔ commSub B := by
    intro A B
    rw [commSub_le_iff]
    have hA : A ≤ stabQuot (commSub A ⊔ commSub B) := fun a ha v =>
      Submodule.mem_sup_left (sub_mem_commSub A ha v)
    have hB : B ≤ stabQuot (commSub A ⊔ commSub B) := fun a ha v =>
      Submodule.mem_sup_right (sub_mem_commSub B ha v)
    exact fun g hg v => (sup_le hA hB) hg v
  have hle : commSub (zpowers y) ≤
      commSub (zpowers d) ⊔ commSub (zpowers (y⁻¹ * d * y)) := by
    have h1 : zpowers y ≤ zpowers d ⊔ zpowers (y⁻¹ * d * y) := by
      rw [zpowers_le]
      have h2 : y ∈ zpowers (y ^ 2) := hyz
      refine (zpowers_le.mpr ?_) h2
      rw [← hz]
      exact Subgroup.mul_mem_sup (mem_zpowers d) (mem_zpowers _)
    exact (commSub_mono _ _ h1).trans (hsup _ _)
  calc Module.finrank (ZMod 2) ↥(commSub (zpowers y))
      ≤ Module.finrank (ZMod 2) ↥(commSub (zpowers d) ⊔ commSub (zpowers (y⁻¹ * d * y))) :=
        Submodule.finrank_mono hle
    _ ≤ _ := Submodule.finrank_add_le_finrank_add_finrank _ _

end CFSG.LocalAnalysis.WeakClosure81

end
