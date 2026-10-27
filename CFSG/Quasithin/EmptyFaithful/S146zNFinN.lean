module

public import CFSG.Quasithin.EmptyFaithful.S146zNFinDef
public import CFSG.Quasithin.EmptyFaithful.S146yA6Mod
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.ReduceModChar

public section

namespace CFSG.Quasithin.A6Fin

open Equiv Equiv.Perm CFSG.Quasithin CFSG.Quasithin.A6Mod

theorem card_modEq_perm {α : Type} [Fintype α] [DecidableEq α] (π : Perm α) (p : ℕ) [Fact p.Prime]
    (hπ : π ^ p = 1) : Fintype.card α ≡ Fintype.card {a // π a = a} [MOD p] := by
  have h : (show Function.End α from ⇑π) ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext x
    have := congrFun (congrArg DFunLike.coe hπ) x
    simp only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, id_eq] at this
    exact this
  exact Equiv.Perm.card_fixedPoints_modEq (p := p) (n := 1) h

theorem card_modEq_perm_inv {α : Type} [Fintype α] [DecidableEq α] (π : Perm α) (p : ℕ) [Fact p.Prime]
    (hπ : π ^ p = 1) (P : α → Prop) [DecidablePred P] (hP : ∀ x, P (π x) ↔ P x) :
    Fintype.card {a // P a} ≡ Fintype.card {a // P a ∧ π a = a} [MOD p] := by
  have h1 := card_modEq_perm (π.subtypePerm hP) p (by
    rw [Equiv.Perm.subtypePerm_pow]
    ext x
    have := congrArg (fun f : Perm α => f x) hπ
    simpa [Equiv.Perm.subtypePerm_apply] using this)
  have h2 : Fintype.card {b : {a // P a} // π.subtypePerm hP b = b} =
      Fintype.card {a // P a ∧ π a = a} := by
    refine Fintype.card_congr ⟨fun b => ⟨b.1.1, b.1.2, ?_⟩, fun a => ⟨⟨a.1, a.2.1⟩, ?_⟩, ?_, ?_⟩
    · have := congrArg Subtype.val b.2
      simpa using this
    · apply Subtype.ext
      exact a.2.2
    · intro b; rfl
    · intro a; rfl
  rwa [h2] at h1

section Mod

variable {W : Type} [CommGroup W] [Finite W]

theorem card_fixSub_modEq_three (ρ : A6 →* MulAut W) {g : A6} (hg : g ^ 3 = 1) (hfc : fc ρ g = 1)
    (γ : MulAut W) (hcomm : ρ g * γ = γ * ρ g) : Nat.card (fixSub γ) ≡ 1 [MOD 3] := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype W := Fintype.ofFinite W
  let π : Perm W := (ρ g).toEquiv
  have hπ : π ^ 3 = 1 := by
    ext x
    have h3 : ρ g ^ 3 = 1 := by rw [← map_pow, hg, map_one]
    have := congrArg (fun f : MulAut W => f x) h3
    simpa [π, pow_succ, Perm.mul_apply] using this
  have hP : ∀ x : W, (fun w : W => γ w = w) (π x) ↔ (fun w : W => γ w = w) x := by
    intro x
    have h : γ (ρ g x) = ρ g (γ x) := by
      have := congrArg (fun f : MulAut W => f x) hcomm
      simpa using this.symm
    show γ (ρ g x) = ρ g x ↔ γ x = x
    rw [h]
    exact ⟨fun h' => (ρ g).injective h', fun h' => by rw [h']⟩
  have h1 := card_modEq_perm_inv π 3 hπ (fun w : W => γ w = w) hP
  have h2 : Fintype.card {a : W // γ a = a} = Nat.card (fixSub γ) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  have h3 : Fintype.card {a : W // γ a = a ∧ π a = a} = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, map_one γ, (map_one (ρ g) : ρ g 1 = 1)⟩, fun ⟨a, ha1, ha2⟩ => ?_⟩
    apply Subtype.ext
    have hbot : fixSub (ρ g) = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      exact hfc
    have : a ∈ fixSub (ρ g) := ha2
    rw [hbot] at this
    exact (Subgroup.mem_bot.mp this)
  rw [h2, h3] at h1
  exact h1

omit [Finite W] in
theorem le_card_fixSub_sq [Finite W] (hsq : ∀ w : W, w * w = 1) (γ : MulAut W) (hγ : γ * γ = 1) :
    Nat.card W ≤ Nat.card (fixSub γ) * Nat.card (fixSub γ) := by
  let φ : W →* W := MonoidHom.mk' (fun w => γ w * w⁻¹) (fun a b => by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm b⁻¹ a⁻¹]
    simp only [mul_assoc, mul_comm, mul_left_comm])
  have hker : φ.ker = fixSub γ := by
    ext w
    rw [MonoidHom.mem_ker, mem_fixSub]
    show γ w * w⁻¹ = 1 ↔ γ w = w
    exact mul_inv_eq_one
  have hrange : φ.range ≤ fixSub γ := by
    rintro _ ⟨w, rfl⟩
    rw [mem_fixSub]
    show γ (γ w * w⁻¹) = γ w * w⁻¹
    have h2 : γ (γ w) = w := by
      have := congrArg (fun f : MulAut W => f w) hγ
      simpa using this
    rw [map_mul, h2, map_inv]
    have hinv : ∀ x : W, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (hsq x)
    rw [hinv (γ w), hinv w]
    exact mul_comm _ _
  have hc := Subgroup.card_ker_mul_card_range φ
  rw [hker] at hc
  rw [← hc]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hrange)

omit [Finite W] in
theorem rank_spec (hW : Nat.card W = 16) (γ : MulAut W) :
    Nat.card (fixSub γ) * 2 ^ A6Rank γ = 16 := by
  have hfix : fixV (Subgroup.zpowers γ) = fixSub γ := by
    ext w
    rw [mem_fixV, mem_fixSub]
    constructor
    · intro h
      exact h γ (Subgroup.mem_zpowers γ)
    · intro h x hx
      have hst : γ ∈ MulAction.stabilizer (MulAut W) w := by
        rw [MulAction.mem_stabilizer_iff]
        exact h
      exact MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr hst hx)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  unfold A6Rank
  rw [hfix]
  have hcard := (fixSub γ).card_mul_index
  rw [hW] at hcard
  have hdvd : (fixSub γ).index ∣ 2 ^ 4 := ⟨Nat.card (fixSub γ), by rw [mul_comm]; omega⟩
  obtain ⟨m, -, hidx⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  unfold rkIdx
  rw [hidx, padicValNat.prime_pow]
  rw [hidx] at hcard
  exact hcard

end Mod

end CFSG.Quasithin.A6Fin
