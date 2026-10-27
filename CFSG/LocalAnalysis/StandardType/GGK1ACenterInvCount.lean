module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.StandardType

def involutiveInvSubgroup (G : Type*) [CommGroup G] {α : Type*} (σ : α → α) :
    Subgroup (α → G) where
  carrier := {c | ∀ a, c (σ a) * c a = 1}
  mul_mem' {c d} hc hd a := by
    simp only [Pi.mul_apply]
    rw [mul_mul_mul_comm, hc a, hd a, one_mul]
  one_mem' a := by simp
  inv_mem' {c} hc a := by
    simp only [Pi.inv_apply]
    rw [← mul_inv, hc a, inv_one]

theorem mem_involutiveInvSubgroup {G : Type*} [CommGroup G] {α : Type*} {σ : α → α}
    {c : α → G} : c ∈ involutiveInvSubgroup G σ ↔ ∀ a, c (σ a) * c a = 1 := Iff.rfl

section Counting

variable {G : Type*} [CommGroup G] {α : Type*} {σ : α → α}

private lemma invCount_eq_one_of_fixed [Finite G] (hG : Odd (Nat.card G)) {c : α → G}
    (hc : ∀ a, c (σ a) * c a = 1) {a : α} (ha : σ a = a) : c a = 1 := by
  have h2 : c a ^ 2 = 1 := by
    rw [pow_two]
    simpa [ha] using hc a
  have hdvd : orderOf (c a) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h2
  have hcop : Nat.Coprime 2 (Nat.card G) := Nat.coprime_two_left.mpr hG
  have h1 : orderOf (c a) ∣ Nat.gcd 2 (Nat.card G) :=
    Nat.dvd_gcd hdvd (orderOf_dvd_natCard (c a))
  rw [hcop] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

private lemma invCount_card_lt_eq_card_gt [LinearOrder α] (hσ : Function.Involutive σ) :
    Nat.card {a : α // a < σ a} = Nat.card {a : α // σ a < a} := by
  refine Nat.card_congr ⟨fun a => ⟨σ a.1, ?_⟩, fun a => ⟨σ a.1, ?_⟩, fun a => ?_, fun a => ?_⟩
  · show σ (σ a.1) < σ a.1
    rw [hσ a.1]
    exact a.2
  · show σ a.1 < σ (σ a.1)
    rw [hσ a.1]
    exact a.2
  · exact Subtype.ext (hσ a.1)
  · exact Subtype.ext (hσ a.1)

private lemma invCount_card_moved [Finite α] [LinearOrder α] :
    Nat.card {a : α // σ a ≠ a}
      = Nat.card {a : α // a < σ a} + Nat.card {a : α // σ a < a} := by
  classical
  let : Fintype α := Fintype.ofFinite α
  have hdisj : Disjoint (Finset.univ.filter fun a => a < σ a)
      (Finset.univ.filter fun a => σ a < a) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    exact absurd ha (not_lt.mpr (le_of_lt hb))
  have hunion : (Finset.univ.filter fun a => a < σ a) ∪ (Finset.univ.filter fun a => σ a < a)
      = Finset.univ.filter fun a => σ a ≠ a := by
    ext a
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, ne_eq]
    constructor
    · rintro (h | h)
      · exact h.ne'
      · exact h.ne
    · intro h
      rcases lt_or_gt_of_ne h with h' | h'
      · exact Or.inr h'
      · exact Or.inl h'
  have hM : Nat.card {a : α // σ a ≠ a} = (Finset.univ.filter fun a => σ a ≠ a).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hR : Nat.card {a : α // a < σ a} = (Finset.univ.filter fun a => a < σ a).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hR' : Nat.card {a : α // σ a < a} = (Finset.univ.filter fun a => σ a < a).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [hM, hR, hR', ← hunion, Finset.card_union_of_disjoint hdisj]

private noncomputable def invCountFun [LinearOrder α] (hσ : Function.Involutive σ)
    (d : {a : α // a < σ a} → G) (a : α) : G :=
  if ha : a < σ a then d ⟨a, ha⟩
  else if hb : σ a < a then (d ⟨σ a, by rw [hσ a]; exact hb⟩)⁻¹
  else 1

private lemma invCountFun_of_lt [LinearOrder α] (hσ : Function.Involutive σ)
    (d : {a : α // a < σ a} → G) {a : α} (h : a < σ a) :
    invCountFun hσ d a = d ⟨a, h⟩ := by
  unfold invCountFun
  rw [dif_pos h]

private lemma invCountFun_of_gt [LinearOrder α] (hσ : Function.Involutive σ)
    (d : {a : α // a < σ a} → G) {a : α} (h : σ a < a) :
    invCountFun hσ d a = (d ⟨σ a, by rw [hσ a]; exact h⟩)⁻¹ := by
  unfold invCountFun
  rw [dif_neg (not_lt.mpr (le_of_lt h)), dif_pos h]

private lemma invCountFun_of_fixed [LinearOrder α] (hσ : Function.Involutive σ)
    (d : {a : α // a < σ a} → G) {a : α} (h : σ a = a) : invCountFun hσ d a = 1 := by
  unfold invCountFun
  rw [dif_neg (show ¬ a < σ a by rw [h]; exact lt_irrefl a),
    dif_neg (show ¬ σ a < a by rw [h]; exact lt_irrefl a)]

private lemma invCountFun_apply_inv [LinearOrder α] (hσ : Function.Involutive σ)
    (d : {a : α // a < σ a} → G) (a : α) :
    invCountFun hσ d (σ a) = (invCountFun hσ d a)⁻¹ := by
  by_cases ha : a < σ a
  · rw [invCountFun_of_lt hσ d ha]
    have h3 : σ (σ a) < σ a := by rw [hσ a]; exact ha
    rw [invCountFun_of_gt hσ d h3]
    have hsub : (⟨σ (σ a), by rw [hσ (σ a)]; exact h3⟩ : {a : α // a < σ a}) = ⟨a, ha⟩ :=
      Subtype.ext (hσ a)
    rw [hsub]
  · by_cases hb : σ a < a
    · rw [invCountFun_of_gt hσ d hb]
      have h3 : σ a < σ (σ a) := by rw [hσ a]; exact hb
      rw [invCountFun_of_lt hσ d h3, inv_inv]
    · have hfix : σ a = a := (le_antisymm (not_lt.mp hb) (not_lt.mp ha)).symm
      rw [hfix, invCountFun_of_fixed hσ d hfix, inv_one]

private lemma invCountFun_mem [LinearOrder α] (hσ : Function.Involutive σ)
    (d : {a : α // a < σ a} → G) :
    ∀ a, invCountFun hσ d (σ a) * invCountFun hσ d a = 1 := by
  intro a
  rw [invCountFun_apply_inv hσ d a, inv_mul_cancel]

private lemma invCountFun_restrict [LinearOrder α] [Finite G] (hG : Odd (Nat.card G))
    (hσ : Function.Involutive σ) {c : α → G} (hc : ∀ a, c (σ a) * c a = 1) (a : α) :
    invCountFun hσ (fun r => c r.1) a = c a := by
  by_cases ha : a < σ a
  · rw [invCountFun_of_lt hσ _ ha]
  · by_cases hb : σ a < a
    · rw [invCountFun_of_gt hσ _ hb]
      exact (eq_inv_of_mul_eq_one_right (hc a)).symm
    · have hfix : σ a = a := (le_antisymm (not_lt.mp hb) (not_lt.mp ha)).symm
      rw [invCountFun_of_fixed hσ _ hfix]
      exact (invCount_eq_one_of_fixed hG hc hfix).symm

private noncomputable def invCountEquiv [LinearOrder α] [Finite G] (hG : Odd (Nat.card G))
    (hσ : Function.Involutive σ) :
    involutiveInvSubgroup G σ ≃ ({a : α // a < σ a} → G) where
  toFun c r := c.1 r.1
  invFun d := ⟨invCountFun hσ d, invCountFun_mem hσ d⟩
  left_inv c := by
    refine Subtype.ext (funext fun a => ?_)
    exact invCountFun_restrict hG hσ c.2 a
  right_inv d := by
    funext r
    exact invCountFun_of_lt hσ d r.2

end Counting

theorem card_involutiveInvSubgroup {G : Type*} [CommGroup G] [Finite G] {α : Type*} [Finite α]
    (hG : Odd (Nat.card G)) {σ : α → α} (hσ : Function.Involutive σ) :
    Nat.card (involutiveInvSubgroup G σ) = Nat.card G ^ (Nat.card {a // σ a ≠ a} / 2) := by
  classical
  let : Fintype α := Fintype.ofFinite α
  let : LinearOrder α :=
    LinearOrder.lift' (Fintype.equivFin α) (Fintype.equivFin α).injective
  have hcard : Nat.card {a : α // σ a ≠ a} = Nat.card {a : α // a < σ a} * 2 := by
    rw [invCount_card_moved (σ := σ), invCount_card_lt_eq_card_gt (σ := σ) hσ, Nat.mul_two]
  have hdiv : Nat.card {a : α // σ a ≠ a} / 2 = Nat.card {a : α // a < σ a} := by
    rw [hcard, Nat.mul_div_left _ Nat.zero_lt_two]
  rw [hdiv, ← Nat.card_fun]
  exact Nat.card_congr (invCountEquiv hG hσ)

end CFSG.StandardType

end
