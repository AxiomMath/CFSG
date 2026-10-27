module

public import CFSG.Quasithin.Background.B4L3Syl

public section

namespace CFSG.Quasithin

namespace L3

@[expose] def bsSub (S : Finset Vec) : Subgroup Γ where
  carrier := {g | ∀ v ∈ S, act g v = v}
  one_mem' := fun v _ => act_one v
  mul_mem' := fun {a b} ha hb v hv => by rw [act_mul, hb v hv, ha v hv]
  inv_mem' := fun {a} ha v hv => by
    have := ha v hv
    calc act a⁻¹ v = act a⁻¹ (act a v) := by rw [this]
      _ = v := act_inv_act a v

@[expose] def stabSub (S : Finset Vec) : Subgroup Γ where
  carrier := {g | ∀ v, v ∈ S ↔ act g v ∈ S}
  one_mem' := fun v => by rw [act_one]
  mul_mem' := fun {a b} ha hb v => by rw [act_mul, ← ha, ← hb]
  inv_mem' := fun {a} ha v => by
    rw [ha (act a⁻¹ v), act_act_inv]

@[expose] def ptSub (x : Vec) : Subgroup Γ where
  carrier := {g | act g x = x}
  one_mem' := act_one x
  mul_mem' := fun {a b} ha hb => by
    show act (a * b) x = x
    rw [act_mul]
    show act a (act b x) = x
    rw [show act b x = x from hb, show act a x = x from ha]
  inv_mem' := fun {a} ha => by
    show act a⁻¹ x = x
    have h : act a x = x := ha
    calc act a⁻¹ x = act a⁻¹ (act a x) := by rw [h]
      _ = x := act_inv_act a x

theorem mem_bsSub {S : Finset Vec} {g : Γ} : g ∈ bsSub S ↔ ∀ v ∈ S, act g v = v := Iff.rfl

theorem mem_stabSub {S : Finset Vec} {g : Γ} : g ∈ stabSub S ↔ ∀ v, v ∈ S ↔ act g v ∈ S := Iff.rfl

theorem mem_ptSub {x : Vec} {g : Γ} : g ∈ ptSub x ↔ act g x = x := Iff.rfl

set_option maxRecDepth 100000 in
theorem card_stabSub_filter : ∀ S : Finset Vec, IsPlane S →
    (Finset.univ.filter fun g : Γ => ∀ v, v ∈ S ↔ act g v ∈ S).card = 24 := by decide +kernel

set_option maxRecDepth 100000 in
theorem exists_ptSub_not_stabSub : ∀ (x : Vec) (S : Finset Vec), x ≠ 0 → IsPlane S →
    ∃ g : Γ, act g x = x ∧ ¬ ∀ v, v ∈ S ↔ act g v ∈ S := by decide +kernel

set_option maxRecDepth 100000 in
theorem stab_of_normalizes_filter : ∀ S : Finset Vec, IsPlane S → ∀ g : Γ,
    (∀ k ∈ BS S, g * k * g⁻¹ ∈ BS S) → ∀ v, v ∈ S ↔ act g v ∈ S := by decide +kernel

theorem card_stabSub {S : Finset Vec} (hS : IsPlane S) : Nat.card (stabSub S) = 24 := by
  rw [← card_stabSub_filter S hS, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [mem_stabSub])

theorem card_bsSub {S : Finset Vec} (hS : IsPlane S) : Nat.card (bsSub S) = 4 := by
  rw [← BS_card S hS, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => by simp [mem_bsSub, BS])

theorem not_ptSub_le_stabSub {x : Vec} {S : Finset Vec} (hx : x ≠ 0) (hS : IsPlane S) :
    ¬ ptSub x ≤ stabSub S := by
  intro h
  obtain ⟨g, hg, hg'⟩ := exists_ptSub_not_stabSub x S hx hS
  exact hg' (mem_stabSub.mp (h hg))

theorem eq_stabSub_or_eq_top {S : Finset Vec} (hS : IsPlane S) {K : Subgroup Γ} (h : stabSub S ≤ K) :
    K = stabSub S ∨ K = ⊤ := by
  have h1 : Nat.card (stabSub S) ∣ Nat.card K := Subgroup.card_dvd_of_le h
  have h2 : Nat.card K ∣ Nat.card Γ := Subgroup.card_subgroup_dvd_card K
  rw [card_stabSub hS] at h1
  rw [card_L3Γ] at h2
  obtain ⟨m, hm⟩ := h1
  have hm7 : m ∣ 7 := by
    rw [hm] at h2
    have : 24 * m ∣ 24 * 7 := by simpa using h2
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hm7 with h7 | h7
  · left
    refine (Subgroup.eq_of_le_of_card_ge h ?_).symm
    rw [hm, h7, card_stabSub hS]
  · right
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [hm, h7, card_L3Γ]

theorem ptSub_sup_stabSub_eq_top {x : Vec} {S : Finset Vec} (hx : x ≠ 0) (hS : IsPlane S) :
    ptSub x ⊔ stabSub S = ⊤ := by
  rcases eq_stabSub_or_eq_top hS (le_sup_right : stabSub S ≤ ptSub x ⊔ stabSub S) with h | h
  · exact absurd (le_sup_left.trans h.le) (not_ptSub_le_stabSub hx hS)
  · exact h

theorem mem_stabSub_of_normalizes {S : Finset Vec} (hS : IsPlane S) {g : Γ}
    (hg : ∀ k ∈ bsSub S, g * k * g⁻¹ ∈ bsSub S) : g ∈ stabSub S := by
  refine stab_of_normalizes_filter S hS g (fun k hk => ?_)
  have hk' : k ∈ bsSub S := by simpa [bsSub, BS] using hk
  have := hg k hk'
  simpa [bsSub, BS] using this

end L3

end CFSG.Quasithin
