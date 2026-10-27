module

public import Mathlib.GroupTheory.Nilpotent

public section

namespace CFSG.Quasithin

namespace E217R3

variable {X : Type*} [Group X]

theorem klein_closure {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set X), x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  have hba : b * a = a * b := hab.symm
  have h2 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
  have h4 : b * (a * b) = a := by rw [← mul_assoc, hba, mul_assoc, hb, mul_one]
  have h5 : (a * b) * a = b := by rw [mul_assoc, hba, ← mul_assoc, ha, one_mul]
  have h6 : (a * b) * b = a := by rw [mul_assoc, hb, mul_one]
  have h7 : (a * b) * (a * b) = 1 := by rw [← mul_assoc, h5, hb]
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;> rw [hx, hy] <;>
      simp [ha, hb, hba, h2, h4, h5, h6, h7]
  | inv x _ hx =>
    rcases hx with hx | hx | hx | hx <;> rw [hx]
    · simp
    · simp [hai]
    · simp [hbi]
    · simp [mul_inv_rev, hai, hbi, hba]

theorem commute_closure {a b c : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a)
    (hca : c * a = a * c) (hcb : c * b = b * c) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set X), c * x = x * c := by
  intro x hx
  rcases klein_closure ha hb hab x hx with h | h | h | h <;> rw [h]
  · simp
  · exact hca
  · exact hcb
  · calc c * (a * b) = (c * a) * b := by group
      _ = (a * c) * b := by rw [hca]
      _ = a * (c * b) := by group
      _ = a * (b * c) := by rw [hcb]
      _ = (a * b) * c := by group

theorem closure_sq {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set X), x * x = 1 := by
  intro x hx
  rcases klein_closure ha hb hab x hx with h | h | h | h <;> rw [h]
  · simp
  · exact ha
  · exact hb
  · calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [← hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, one_mul]

theorem closure_comm {a b : X} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b = b * a) :
    ∀ x ∈ Subgroup.closure ({a, b} : Set X), ∀ y ∈ Subgroup.closure ({a, b} : Set X),
      x * y = y * x := by
  intro x hx y hy
  have hba : b * a = a * b := hab.symm
  rcases klein_closure ha hb hab y hy with h | h | h | h <;> rw [h]
  · simp
  · exact (commute_closure ha hb hab rfl hab x hx).symm
  · exact (commute_closure ha hb hab hba rfl x hx).symm
  · have h1 := commute_closure ha hb hab (c := a) rfl hab x hx
    have h2 := commute_closure ha hb hab (c := b) hba rfl x hx
    calc x * (a * b) = (x * a) * b := by group
      _ = (a * x) * b := by rw [← h1]
      _ = a * (x * b) := by group
      _ = a * (b * x) := by rw [← h2]
      _ = (a * b) * x := by group

theorem four_le_card_closure [Finite X] {a b : X} (ha : a * a = 1) (hb : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hne : a ≠ b) :
    4 ≤ Nat.card (Subgroup.closure ({a, b} : Set X)) := by
  set V := Subgroup.closure ({a, b} : Set X) with hV
  have haV : a ∈ V := Subgroup.subset_closure (Set.mem_insert _ _)
  have hbV : b ∈ V := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hab1 : a * b ≠ 1 := fun h => hne (by
    have := eq_inv_of_mul_eq_one_left h
    rw [this, hbi])
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hsub : ({1, a, b, a * b} : Set X) ⊆ (V : Set X) := by
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact V.one_mem
    · exact haV
    · exact hbV
    · exact V.mul_mem haV hbV
  have hcard : ({1, a, b, a * b} : Set X).ncard = 4 := by
    have n1 : (1 : X) ∉ ({a, b, a * b} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    have n2 : a ∉ ({b, a * b} : Set X) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨hne, hab2.symm⟩
    rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2, Set.ncard_pair hab3.symm]
  have := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [hcard] at this
  rwa [← Nat.card_coe_set_eq] at this

theorem exists_involution_mem_center_of_normal [Finite X] {T Y : Subgroup X}
    (hT : IsPGroup 2 T) (hYT : Y ≤ T) (hYn : ∀ t ∈ T, ∀ y ∈ Y, t * y * t⁻¹ ∈ Y) (hY : Y ≠ ⊥) :
    ∃ z ∈ Y, orderOf z = 2 ∧ ∀ t ∈ T, t * z = z * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥T := hT.isNilpotent
  let Y' : Subgroup ↥T := Y.subgroupOf T
  have hY'n : Y'.Normal := ⟨fun y hy t => by
    show ((t * y * t⁻¹ : ↥T) : X) ∈ Y
    have : ((t * y * t⁻¹ : ↥T) : X) = (t : X) * (y : X) * (t : X)⁻¹ := rfl
    rw [this]
    exact hYn t t.2 y hy⟩
  have hY'ne : Y' ≠ ⊥ := by
    intro h
    apply hY
    rw [eq_bot_iff]
    intro y hy
    have : (⟨y, hYT hy⟩ : ↥T) ∈ Y' := hy
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (congrArg Subtype.val this)
  have hne := Group.IsNilpotent.inf_center_ne_bot_of_normal hY'ne
  obtain ⟨c, hc1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have hcY : ((c : ↥T) : X) ∈ Y := (Subgroup.mem_inf.1 c.2).1
  have hcc := Subgroup.mem_center_iff.1 (Subgroup.mem_inf.1 c.2).2
  set g : X := ((c : ↥T) : X) with hg
  have hg1 : g ≠ 1 := fun h => hc1 (Subtype.ext (Subtype.ext h))
  have hgc : ∀ t ∈ T, t * g = g * t := fun t ht => congrArg Subtype.val (hcc ⟨t, ht⟩)
  obtain ⟨k, hk⟩ := hT (c : ↥T)
  have hgk : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hord : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hgk
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hi0 : i ≠ 0 := by
    rintro rfl
    exact hg1 (orderOf_eq_one_iff.1 (by simpa using hi))
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi0
  refine ⟨g ^ 2 ^ j, Y.pow_mem hcY _, ?_, fun t ht => ?_⟩
  · rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (by rw [hi]; exact pow_dvd_pow 2 (by omega)),
      hi, pow_succ, Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  · have hc : Commute t g := hgc t ht
    exact (hc.pow_right _).eq

end E217R3

end CFSG.Quasithin
