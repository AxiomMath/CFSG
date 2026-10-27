module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.H13

namespace S126T2

open Equiv

@[expose] def six : Finset (Fin 8) := {2, 3, 4, 5, 6, 7}

@[expose] def A6s : Subgroup (Perm (Fin 8)) :=
  (alternatingGroup ↥six).map (Perm.ofSubtype : Perm ↥six →* Perm (Fin 8))

theorem mem_six_iff : ∀ x : Fin 8, x ∈ six ↔ x ≠ 0 ∧ x ≠ 1 := by
  decide

theorem card_six : Nat.card ↥six = 6 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  rfl

theorem mem_A6s {σ : Perm (Fin 8)} :
    σ ∈ A6s ↔ σ 0 = 0 ∧ σ 1 = 1 ∧ σ ∈ alternatingGroup (Fin 8) := by
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨Perm.ofSubtype_apply_of_not_mem a (by decide),
      Perm.ofSubtype_apply_of_not_mem a (by decide), ?_⟩
    rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
    exact ha
  · rintro ⟨h0, h1, hA⟩
    have hne0 : ∀ x, σ x = 0 ↔ x = 0 := fun x =>
      ⟨fun e => σ.injective (e.trans h0.symm), fun e => e ▸ h0⟩
    have hne1 : ∀ x, σ x = 1 ↔ x = 1 := fun x =>
      ⟨fun e => σ.injective (e.trans h1.symm), fun e => e ▸ h1⟩
    have hp : ∀ x, σ x ∈ six ↔ x ∈ six := fun x => by
      rw [mem_six_iff, mem_six_iff, Ne, Ne, Ne, Ne, hne0, hne1]
    have hs : ∀ x, σ x ≠ x → x ∈ six := fun x hx => by
      rw [mem_six_iff]
      refine ⟨fun e => hx (e ▸ h0), fun e => hx (e ▸ h1)⟩
    refine ⟨σ.subtypePerm hp, Perm.mem_alternatingGroup.2 ?_, Perm.ofSubtype_subtypePerm hp hs⟩
    rw [← Perm.sign_ofSubtype, Perm.ofSubtype_subtypePerm hp hs]
    exact Perm.mem_alternatingGroup.1 hA

theorem A6s_perfect : ⁅A6s, A6s⁆ = A6s := by
  rw [A6s, ← Subgroup.map_commutator,
    commutator_alternatingGroup_eq_self (by rw [card_six]; norm_num)]

@[expose] def cy (a b d : Fin 8) : Perm (Fin 8) := swap a b * swap a d

theorem sign_cy {a b d : Fin 8} (hab : a ≠ b) (had : a ≠ d) : Perm.sign (cy a b d) = 1 := by
  rw [cy, Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap had]
  rfl

theorem cy_mem {a b d : Fin 8} (hab : a ≠ b) (had : a ≠ d) (ha : a ∈ six) (hb : b ∈ six)
    (hd : d ∈ six) : cy a b d ∈ A6s := by
  refine mem_A6s.2 ⟨?_, ?_, Perm.mem_alternatingGroup.2 (sign_cy hab had)⟩
  · rw [cy, Perm.mul_apply, swap_apply_of_ne_of_ne ((mem_six_iff a).1 ha).1.symm
      ((mem_six_iff d).1 hd).1.symm, swap_apply_of_ne_of_ne ((mem_six_iff a).1 ha).1.symm
      ((mem_six_iff b).1 hb).1.symm]
  · rw [cy, Perm.mul_apply, swap_apply_of_ne_of_ne ((mem_six_iff a).1 ha).2.symm
      ((mem_six_iff d).1 hd).2.symm, swap_apply_of_ne_of_ne ((mem_six_iff a).1 ha).2.symm
      ((mem_six_iff b).1 hb).2.symm]

theorem cyc_three : cy 2 3 4 ^ 3 = 1 ∧ cy 2 3 4 ≠ 1 := by
  decide

theorem sep2 : ∀ y : Fin 8, cy 2 3 4 y ≠ y → cy 2 5 6 y ≠ y → y = 2 := by decide
theorem sep3 : ∀ y : Fin 8, cy 2 3 4 y ≠ y → cy 3 5 7 y ≠ y → y = 3 := by decide
theorem sep4 : ∀ y : Fin 8, cy 2 3 4 y ≠ y → cy 4 6 7 y ≠ y → y = 4 := by decide
theorem sep5 : ∀ y : Fin 8, cy 2 5 6 y ≠ y → cy 3 5 7 y ≠ y → y = 5 := by decide
theorem sep6 : ∀ y : Fin 8, cy 2 5 6 y ≠ y → cy 4 6 7 y ≠ y → y = 6 := by decide
theorem sep7 : ∀ y : Fin 8, cy 3 5 7 y ≠ y → cy 4 6 7 y ≠ y → y = 7 := by decide

theorem eq_bot_or_eq_of_normal {N : Subgroup (Perm (Fin 8))} (hNA : N ≤ A6s)
    (hN : ∀ a ∈ A6s, ∀ n ∈ N, a * n * a⁻¹ ∈ N) : N = ⊥ ∨ N = A6s := by
  let e : ↥(alternatingGroup ↥six) →* Perm (Fin 8) :=
    (Perm.ofSubtype : Perm ↥six →* Perm (Fin 8)).comp (alternatingGroup ↥six).subtype
  have he : e.range = A6s := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hemem : ∀ a, e a ∈ A6s := fun a => he ▸ ⟨a, rfl⟩
  let N' : Subgroup ↥(alternatingGroup ↥six) := N.comap e
  have hN' : N'.Normal := ⟨fun n hn g => by
    change e (g * n * g⁻¹) ∈ N
    rw [map_mul, map_mul, map_inv]
    exact hN _ (hemem g) _ hn⟩
  have : IsSimpleGroup ↥(alternatingGroup ↥six) :=
    alternatingGroup.isSimpleGroup (by rw [card_six]; norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N' with h | h
  · left
    rw [eq_bot_iff]
    intro n hn
    obtain ⟨a, rfl⟩ := he.symm ▸ hNA hn
    have ha : a ∈ N' := hn
    rw [h, Subgroup.mem_bot] at ha
    rw [ha, map_one]
    exact Subgroup.one_mem _
  · right
    refine le_antisymm hNA fun x hx => ?_
    obtain ⟨a, rfl⟩ := he.symm ▸ hx
    exact (h ▸ Subgroup.mem_top a : a ∈ N')

theorem eq_bot_of_normal {N : Subgroup (Perm (Fin 8))} (hNA : N ≤ A6s)
    (hN : ∀ a ∈ A6s, ∀ n ∈ N, a * n * a⁻¹ ∈ N) (h2 : IsPGroup 2 N) : N = ⊥ := by
  refine (eq_bot_or_eq_of_normal hNA hN).resolve_right fun h => ?_
  set c : Perm (Fin 8) := cy 2 3 4 with hc
  have hcN : c ∈ N := h ▸ cy_mem (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k, hk⟩ := h2 ⟨c, hcN⟩
  have hk' : c ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨h3, h1⟩ := cyc_three
  have hcop : Nat.Coprime (2 ^ k) 3 := Nat.Coprime.pow_left k (by norm_num)
  have hd := orderOf_dvd_of_pow_eq_one hk'
  have hd3 := orderOf_dvd_of_pow_eq_one h3
  have ho : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd hcop) hd3
  exact h1 (orderOf_eq_one_iff.1 ho)

theorem moved_of_comm {τ c : Perm (Fin 8)} (h : τ * c = c * τ) {x : Fin 8} (hx : c x ≠ x) :
    c (τ x) ≠ τ x := by
  intro e
  apply hx
  apply τ.injective
  have := congrArg (fun f : Perm (Fin 8) => f x) h
  simp only [Perm.mul_apply] at this
  rw [this, e]

theorem eq_of_comm {τ : Perm (Fin 8)} (h : ∀ a ∈ A6s, τ * a = a * τ) :
    τ = 1 ∨ τ = swap 0 1 := by
  have key : ∀ {a b d a' b' d' i : Fin 8}, a ≠ b → a ≠ d → a ∈ six → b ∈ six → d ∈ six →
      a' ≠ b' → a' ≠ d' → a' ∈ six → b' ∈ six → d' ∈ six → cy a b d i ≠ i → cy a' b' d' i ≠ i →
      (∀ y : Fin 8, cy a b d y ≠ y → cy a' b' d' y ≠ y → y = i) → τ i = i := by
    intro a b d a' b' d' i h1 h2 h3 h4 h5 h1' h2' h3' h4' h5' hm hm' hsep
    exact hsep _ (moved_of_comm (h _ (cy_mem h1 h2 h3 h4 h5)) hm)
      (moved_of_comm (h _ (cy_mem h1' h2' h3' h4' h5')) hm')
  have hfix : ∀ i : Fin 8, i ∈ six → τ i = i := by
    intro i hi
    have hi' : i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by
      revert i
      decide
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
    · exact key (a := 2) (b := 3) (d := 4) (a' := 2) (b' := 5) (d' := 6) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) sep2
    · exact key (a := 2) (b := 3) (d := 4) (a' := 3) (b' := 5) (d' := 7) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) sep3
    · exact key (a := 2) (b := 3) (d := 4) (a' := 4) (b' := 6) (d' := 7) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) sep4
    · exact key (a := 2) (b := 5) (d := 6) (a' := 3) (b' := 5) (d' := 7) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) sep5
    · exact key (a := 2) (b := 5) (d := 6) (a' := 4) (b' := 6) (d' := 7) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) sep6
    · exact key (a := 3) (b := 5) (d := 7) (a' := 4) (b' := 6) (d' := 7) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) sep7
  have hlow : ∀ x : Fin 8, x ∉ six → τ x ∉ six := by
    intro x hx hτx
    have := hfix _ hτx
    rw [τ.injective this] at hτx
    exact hx hτx
  have h0 := hlow 0 (by decide)
  have h1 := hlow 1 (by decide)
  rw [mem_six_iff, not_and_or, not_not, not_not] at h0 h1
  have hne : τ 0 ≠ τ 1 := fun e => absurd (τ.injective e) (by decide)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1
  · exact absurd (h0.trans h1.symm) hne
  · left
    ext x
    by_cases hx : x ∈ six
    · rw [hfix x hx, Perm.one_apply]
    · rw [mem_six_iff, not_and_or, not_not, not_not] at hx
      rcases hx with rfl | rfl
      · rw [h0]; rfl
      · rw [h1]; rfl
  · right
    ext x
    by_cases hx : x ∈ six
    · rw [hfix x hx, swap_apply_of_ne_of_ne ((mem_six_iff x).1 hx).1 ((mem_six_iff x).1 hx).2]
    · rw [mem_six_iff, not_and_or, not_not, not_not] at hx
      rcases hx with rfl | rfl
      · rw [h0, swap_apply_left]
      · rw [h1, swap_apply_right]
  · exact absurd (h0.trans h1.symm) hne

end S126T2

end CFSG.Quasithin.H13
