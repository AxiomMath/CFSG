module

public import CFSG.Quasithin.Background.B1NaturalL2
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

public section

namespace CFSG.Quasithin.H.SL2Nat

open Matrix

@[expose] def FixOne (m : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Prop :=
  ∃ w : Fin 2 → ZMod 2, w ≠ 0 ∧ (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ w = w ∧
    ∀ v : Fin 2 → ZMod 2, (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ v = v → v = 0 ∨ v = w

instance (m : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) : Decidable (FixOne m) := by
  unfold FixOne
  infer_instance

theorem sl2_involution_fix : ∀ m : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2), m ≠ 1 → m * m = 1 →
    FixOne m := by
  decide +kernel

theorem card_sl2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  have h2 : (∏ i : Fin 2, (Fintype.card (ZMod 2) ^ 2 - Fintype.card (ZMod 2) ^ (i : ℕ))) /
      (Fintype.card (ZMod 2) - 1) = 6 := by
    rw [Fin.prod_univ_two, ZMod.card]
    norm_num
  exact (Matrix.card_SL_field (𝔽 := ZMod 2) 2).trans h2

theorem card_vec2 : Nat.card (Multiplicative (Fin 2 → ZMod 2)) = 4 := by
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod 2) ≃ _),
    Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
  norm_num

variable {V : Type*} [CommGroup V]

theorem card_of_actsAsNaturalL2 {H : Subgroup (MulAut V)} {U : Subgroup V}
    (h : ActsAsNaturalL2 H U) : Nat.card H = 6 ∧ Nat.card U = 4 := by
  obtain ⟨e, φ, -⟩ := h
  exact ⟨(Nat.card_congr e.toEquiv).trans card_sl2, (Nat.card_congr φ.toEquiv).trans card_vec2⟩

theorem exists_fix_of_actsAsNaturalL2 {H : Subgroup (MulAut V)} {U : Subgroup V}
    (h : ActsAsNaturalL2 H U) (hU : ∀ x ∈ H, ∀ u ∈ U, x u ∈ U) {s : MulAut V} (hs : s ∈ H)
    (hs1 : s ≠ 1) (hs2 : s * s = 1) :
    ∃ w ∈ U, w ≠ 1 ∧ s w = w ∧ ∀ v ∈ U, s v = v → v = 1 ∨ v = w := by
  obtain ⟨e, φ, hφ⟩ := h
  set m := e ⟨s, hs⟩ with hm
  have hm1 : m ≠ 1 := by
    intro h1
    apply hs1
    have : (⟨s, hs⟩ : ↥H) = 1 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val this
  have hm2 : m * m = 1 := by
    rw [hm, ← map_mul]
    have : (⟨s, hs⟩ : ↥H) * ⟨s, hs⟩ = 1 := Subtype.ext hs2
    rw [this, map_one]
  obtain ⟨w₀, hw₀, hmw₀, huniq⟩ := sl2_involution_fix m hm1 hm2
  set w : ↥U := φ.symm (Multiplicative.ofAdd w₀) with hw
  have hact : ∀ u : ↥U, φ ⟨s u, hU s hs u u.2⟩ =
      Multiplicative.ofAdd ((m : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ
        Multiplicative.toAdd (φ u)) := fun u => hφ ⟨s, hs⟩ u (hU s hs u u.2)
  have hfix : ∀ u : ↥U, s u = u ↔
      (m : Matrix (Fin 2) (Fin 2) (ZMod 2)) *ᵥ Multiplicative.toAdd (φ u) =
        Multiplicative.toAdd (φ u) := by
    intro u
    constructor
    · intro h1
      have h2 := hact u
      have h3 : (⟨s u, hU s hs u u.2⟩ : ↥U) = u := Subtype.ext h1
      rw [h3] at h2
      have := congrArg Multiplicative.toAdd h2
      exact this.symm
    · intro h1
      have h2 := hact u
      rw [h1] at h2
      have h3 : (⟨s u, hU s hs u u.2⟩ : ↥U) = u := φ.injective (h2.trans (by simp))
      exact congrArg Subtype.val h3
  refine ⟨w, w.2, ?_, ?_, ?_⟩
  · intro h1
    apply hw₀
    have : w = 1 := Subtype.ext h1
    rw [hw, MulEquiv.symm_apply_eq, map_one] at this
    exact Multiplicative.ofAdd.injective (this.trans ofAdd_zero.symm)
  · rw [hfix w, hw, MulEquiv.apply_symm_apply]
    exact hmw₀
  · intro v hv hsv
    have h1 := (hfix ⟨v, hv⟩).mp hsv
    rcases huniq _ h1 with h2 | h2
    · left
      have : φ ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective (h2.trans toAdd_one.symm)
      have h3 : (⟨v, hv⟩ : ↥U) = 1 := φ.injective (this.trans (map_one φ).symm)
      exact congrArg Subtype.val h3
    · right
      have : φ ⟨v, hv⟩ = Multiplicative.ofAdd w₀ := Multiplicative.toAdd.injective h2
      have h3 : (⟨v, hv⟩ : ↥U) = w := by
        rw [hw, MulEquiv.eq_symm_apply]
        exact this
      exact congrArg Subtype.val h3

end CFSG.Quasithin.H.SL2Nat
