module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

theorem index_ge_card_of_orbit {G : Type} [Group G] [Finite G] (P C A Z : Subgroup G) (β : G)
    (hCP : C ≤ P) (hZA : Z ≤ A) (hZn : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ ∈ Z)
    (hA : ∀ y ∈ P, ⁅β, y⁆ ∈ A)
    (hmul : ∀ y ∈ P, ∀ c ∈ P, ∃ z ∈ Z, ⁅β, y * c⁆ = ⁅β, y⁆ * ⁅β, c⁆ * z)
    (hC : ∀ c ∈ C, ⁅β, c⁆ ∈ Z)
    (hsurj : ∀ a ∈ A, ∃ y ∈ P, ∃ z ∈ Z, a = ⁅β, y⁆ * z) :
    Nat.card (A ⧸ Z.subgroupOf A) ≤ C.relIndex P := by
  have hMul : ∀ a b : G, (a ∈ P ∧ ⁅β, a⁆ ∈ Z) → (b ∈ P ∧ ⁅β, b⁆ ∈ Z) →
      (a * b ∈ P ∧ ⁅β, a * b⁆ ∈ Z) := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    obtain ⟨z, hz, hab⟩ := hmul a ha1 b hb1
    refine ⟨P.mul_mem ha1 hb1, ?_⟩
    rw [hab]
    exact Z.mul_mem (Z.mul_mem ha2 hb2) hz
  have hOne : (1 : G) ∈ P ∧ ⁅β, (1 : G)⁆ ∈ Z := by
    refine ⟨P.one_mem, ?_⟩
    rw [commutatorElement_one_right]
    exact Z.one_mem
  have hInv : ∀ a : G, (a ∈ P ∧ ⁅β, a⁆ ∈ Z) → (a⁻¹ ∈ P ∧ ⁅β, a⁻¹⁆ ∈ Z) := by
    rintro a ⟨ha1, ha2⟩
    obtain ⟨z, hz, h⟩ := hmul a ha1 a⁻¹ (P.inv_mem ha1)
    rw [mul_inv_cancel, commutatorElement_one_right] at h
    have hinv : ⁅β, a⁻¹⁆ = ⁅β, a⁆⁻¹ * z⁻¹ := by
      calc ⁅β, a⁻¹⁆ = ⁅β, a⁆⁻¹ * (⁅β, a⁆ * ⁅β, a⁻¹⁆ * z) * z⁻¹ := by group
        _ = ⁅β, a⁆⁻¹ * 1 * z⁻¹ := by rw [← h]
        _ = ⁅β, a⁆⁻¹ * z⁻¹ := by group
    refine ⟨P.inv_mem ha1, ?_⟩
    rw [hinv]
    exact Z.mul_mem (Z.inv_mem ha2) (Z.inv_mem hz)
  obtain ⟨H, hH⟩ : ∃ H : Subgroup G, ∀ c : G, c ∈ H ↔ c ∈ P ∧ ⁅β, c⁆ ∈ Z :=
    ⟨{ carrier := {c | c ∈ P ∧ ⁅β, c⁆ ∈ Z},
       mul_mem' := fun {a b} ha hb => hMul a b ha hb,
       one_mem' := hOne,
       inv_mem' := fun {a} ha => hInv a ha }, fun c => Iff.rfl⟩
  have hCH : C ≤ H := by
    intro c hc
    exact (hH c).2 ⟨hCP hc, hC c hc⟩
  have hne : C.relIndex P ≠ 0 := by
    show (C.subgroupOf P).index ≠ 0
    exact Subgroup.index_ne_zero_of_finite
  have key : ∀ y ∈ P, ∀ y' : G, y⁻¹ * y' ∈ H → ⁅β, y⁆⁻¹ * ⁅β, y'⁆ ∈ Z := by
    intro y hy y' hyy'
    obtain ⟨hc1, hc2⟩ := (hH _).1 hyy'
    obtain ⟨z, hz, h⟩ := hmul y hy (y⁻¹ * y') hc1
    rw [mul_inv_cancel_left] at h
    have e : ⁅β, y⁆⁻¹ * ⁅β, y'⁆ = ⁅β, y⁻¹ * y'⁆ * z := by
      rw [h]
      group
    rw [e]
    exact Z.mul_mem hc2 hz
  have hwd : ∀ a b : P, QuotientGroup.leftRel (H.subgroupOf P) a b →
      (QuotientGroup.mk ⟨⁅β, (a : G)⁆, hA (a : G) a.2⟩ : A ⧸ Z.subgroupOf A) =
        QuotientGroup.mk ⟨⁅β, (b : G)⁆, hA (b : G) b.2⟩ := by
    intro a b hab
    have hab' : (a : G)⁻¹ * (b : G) ∈ H := by
      have h1 := QuotientGroup.leftRel_apply.mp hab
      rw [Subgroup.mem_subgroupOf] at h1
      exact h1
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    exact key (a : G) a.2 (b : G) hab'
  obtain ⟨f, hf⟩ : ∃ f : P ⧸ H.subgroupOf P → A ⧸ Z.subgroupOf A,
      ∀ y : P, f (QuotientGroup.mk y) = QuotientGroup.mk ⟨⁅β, (y : G)⁆, hA (y : G) y.2⟩ :=
    ⟨Quotient.lift (fun y : P => (QuotientGroup.mk ⟨⁅β, (y : G)⁆, hA (y : G) y.2⟩ :
      A ⧸ Z.subgroupOf A)) hwd, fun y => rfl⟩
  have hsurjf : Function.Surjective f := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, z, hz, hae⟩ := hsurj (a : G) a.2
    refine ⟨QuotientGroup.mk ⟨y, hy⟩, ?_⟩
    rw [hf ⟨y, hy⟩]
    refine QuotientGroup.eq.mpr ?_
    rw [Subgroup.mem_subgroupOf]
    show ⁅β, y⁆⁻¹ * (a : G) ∈ Z
    rw [hae, inv_mul_cancel_left]
    exact hz
  have hcard : Nat.card (A ⧸ Z.subgroupOf A) ≤ Nat.card (P ⧸ H.subgroupOf P) :=
    Nat.card_le_card_of_surjective f hsurjf
  have hrel : H.relIndex P ≤ C.relIndex P := Subgroup.relIndex_le_of_le_left hCH hne
  have hidx : Nat.card (P ⧸ H.subgroupOf P) = H.relIndex P := rfl
  rw [hidx] at hcard
  exact le_trans hcard hrel

theorem relIndex_inf_le_stroth80 {G : Type} [Group G] [Finite G] (P N Cx : Subgroup G)
    (hPN : P ≤ N) : (P ⊓ Cx).relIndex P ≤ (N ⊓ Cx).relIndex N := by
  have hne : Cx.relIndex N ≠ 0 := by
    intro h0
    have hm := Subgroup.relIndex_mul_card (H := Cx) (K := N)
    rw [h0, zero_mul] at hm
    have hpos : 0 < Nat.card ↥N := Nat.card_pos
    omega
  rw [Subgroup.inf_relIndex_left, Subgroup.inf_relIndex_left]
  exact Subgroup.relIndex_le_of_le_right hPN hne

theorem relIndex_lt_of_card_lt {G : Type} [Group G] [Finite G] (N Cx : Subgroup G) (q : ℕ)
    (h : Nat.card N < q * Nat.card ↥(N ⊓ Cx)) : (N ⊓ Cx).relIndex N < q := by
  have hinf : (N ⊓ Cx) ⊓ N = N ⊓ Cx := inf_eq_left.mpr inf_le_left
  have hm := Subgroup.relIndex_mul_card (H := N ⊓ Cx) (K := N)
  rw [hinf] at hm
  rw [← hm] at h
  exact Nat.lt_of_mul_lt_mul_right h

end CFSG.RankThree.GF2n.Stroth80
