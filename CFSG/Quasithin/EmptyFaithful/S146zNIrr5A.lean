module

public import CFSG.Quasithin.Background.D2Basic

public section

namespace CFSG.Quasithin.A6Irr5

variable {V : Type*} [CommGroup V]

theorem closure_invariant (L : Subgroup (MulAut V)) {T : Set V}
    (hT : ∀ l ∈ L, ∀ t ∈ T, l t ∈ T) :
    ∀ l ∈ L, ∀ w ∈ Subgroup.closure T, l w ∈ Subgroup.closure T := by
  intro l hl w hw
  induction hw using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (hT l hl x hx)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem card_closure_le [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (s : Finset V) :
    Nat.card (Subgroup.closure (s : Set V)) ≤ 2 ^ s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have h1 : Subgroup.closure ((insert a s : Finset V) : Set V) =
        Subgroup.zpowers a ⊔ Subgroup.closure (s : Set V) := by
      rw [Finset.coe_insert, Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure]
    have h2 : Nat.card (Subgroup.zpowers a) ≤ 2 := by
      rw [Nat.card_zpowers]
      exact orderOf_le_of_pow_eq_one (by norm_num) (hV a)
    have h3 := card_sup_mul_card_inf (Subgroup.zpowers a) (Subgroup.closure (s : Set V))
    have h4 : 0 < Nat.card ↥(Subgroup.zpowers a ⊓ Subgroup.closure (s : Set V)) := Nat.card_pos
    have h5 : Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.closure (s : Set V)) ≤
        Nat.card (Subgroup.zpowers a) * Nat.card (Subgroup.closure (s : Set V)) := by
      rw [← h3]; exact Nat.le_mul_of_pos_right _ h4
    rw [h1, Finset.card_insert_of_notMem ha, pow_succ]
    calc Nat.card ↥(Subgroup.zpowers a ⊔ Subgroup.closure (s : Set V))
        ≤ Nat.card (Subgroup.zpowers a) * Nat.card (Subgroup.closure (s : Set V)) := h5
      _ ≤ 2 * 2 ^ s.card := Nat.mul_le_mul h2 ih
      _ = 2 ^ s.card * 2 := by ring

theorem eq_bot_of_card_le (hcard : Nat.card V = 32) {L : Subgroup (MulAut V)}
    (hirr : ∀ S : Subgroup V, (∀ l ∈ L, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = ⊤)
    {E : Subgroup V} (hE : ∀ l ∈ L, ∀ w ∈ E, l w ∈ E) (hle : Nat.card E ≤ 16) : E = ⊥ := by
  rcases hirr E hE with h | h
  · exact h
  · subst h
    rw [Subgroup.card_top, hcard] at hle
    omega

theorem eq_one_of_invariant_finset [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (hcard : Nat.card V = 32)
    {L : Subgroup (MulAut V)}
    (hirr : ∀ S : Subgroup V, (∀ l ∈ L, ∀ w ∈ S, l w ∈ S) → S = ⊥ ∨ S = ⊤)
    {T : Finset V} (hT : ∀ l ∈ L, ∀ t ∈ T, l t ∈ T) (h4 : T.card ≤ 4) : ∀ t ∈ T, t = 1 := by
  have hbot : Subgroup.closure (T : Set V) = ⊥ := by
    refine eq_bot_of_card_le hcard hirr (closure_invariant L fun l hl t ht => hT l hl t ht) ?_
    calc Nat.card (Subgroup.closure (T : Set V)) ≤ 2 ^ T.card := card_closure_le hV T
      _ ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) h4
      _ = 16 := by norm_num
  intro t ht
  have : t ∈ Subgroup.closure (T : Set V) := Subgroup.subset_closure ht
  rwa [hbot, Subgroup.mem_bot] at this

end CFSG.Quasithin.A6Irr5
