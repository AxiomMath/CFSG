module

public import CFSG.Quasithin.EmptyFaithful.SzF53MTab

public section

namespace CFSG.Quasithin.F53Push

open CFSG.Quasithin.F53Mod Equiv

@[expose] def pu4Els : Fin 5 → Perm (Fin 5) :=
  ![swap 0 2, swap 1 3, swap 0 2 * swap 1 3, swap 0 1 * swap 2 3, swap 0 3 * swap 1 2]

@[expose] def pu4Fix (p : Fin 5 → Bool) : ℕ :=
  (Finset.univ.filter fun w : orth.W => ∀ i, p i = true → orth.act (pu4Els i) w = w).card

theorem pu4Els_injective : Function.Injective pu4Els := by decide +kernel

theorem pu4Els_ne_one : ∀ i, pu4Els i ≠ 1 := by decide +kernel

theorem sq_cases : ∀ σ : Perm (Fin 5), σ ∈ S5SylF → σ * σ = 1 → σ = 1 ∨ ∃ i, σ = pu4Els i := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 1024 in
theorem adm_flags : ∀ p : Fin 5 → Bool,
    (∀ i j, p i = true → p j = true →
      pu4Els i * pu4Els j = 1 ∨ ∃ k, p k = true ∧ pu4Els i * pu4Els j = pu4Els k) →
    (∃ i, p i = true) →
    16 ≤ (1 + (Finset.univ.filter fun i => p i = true).card) * pu4Fix p →
    p 3 = false ∧ p 4 = false ∧ (p 0 = true ∨ p 1 = true) ∧
      (1 + (Finset.univ.filter fun i => p i = true).card) * pu4Fix p = 16 := by
  decide +kernel

theorem exists_flags (B : Subgroup (Perm (Fin 5))) (hB : B ≤ S5Syl) (hsq : ∀ x ∈ B, x * x = 1) :
    ∃ p : Fin 5 → Bool, ∀ x : Perm (Fin 5), x ∈ B ↔ x = 1 ∨ ∃ i, p i = true ∧ x = pu4Els i := by
  classical
  refine ⟨fun i => decide (pu4Els i ∈ B), fun x => ⟨fun hx => ?_, ?_⟩⟩
  · rcases sq_cases x ((mem_S5Syl_iff x).mp (hB hx)) (hsq x hx) with rfl | ⟨i, rfl⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, by simpa using hx, rfl⟩
  · rintro (rfl | ⟨i, hi, rfl⟩)
    · exact B.one_mem
    · simpa using hi

theorem card_eq_of_flags {B : Subgroup (Perm (Fin 5))} {p : Fin 5 → Bool}
    (h : ∀ x : Perm (Fin 5), x ∈ B ↔ x = 1 ∨ ∃ i, p i = true ∧ x = pu4Els i) :
    Nat.card B = 1 + (Finset.univ.filter fun i => p i = true).card := by
  classical
  set T : Finset (Perm (Fin 5)) := insert 1 ((Finset.univ.filter fun i => p i = true).image pu4Els)
    with hT
  have h1 : Nat.card B = T.card := by
    rw [← Nat.card_eq_finsetCard]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    rw [h x, hT, Finset.mem_insert, Finset.mem_image]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | ⟨i, hi, h⟩) <;> [exact Or.inl h; exact Or.inr ⟨i, hi, h.symm⟩]
    · rintro (h | ⟨i, hi, h⟩) <;> [exact Or.inl h; exact Or.inr ⟨i, hi, h.symm⟩]
  rw [h1, hT, Finset.card_insert_of_notMem, Finset.card_image_of_injective _ pu4Els_injective,
    add_comm]
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists, not_and]
  exact fun i _ => pu4Els_ne_one i

theorem card_fixW_of_flags {B : Subgroup (Perm (Fin 5))} {p : Fin 5 → Bool}
    (h : ∀ x : Perm (Fin 5), x ∈ B ↔ x = 1 ∨ ∃ i, p i = true ∧ x = pu4Els i) :
    Nat.card (fixW orth B) = pu4Fix p := by
  classical
  unfold pu4Fix
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [mem_fixW]
  constructor
  · intro hw i hi
    exact hw _ ((h _).mpr (Or.inr ⟨i, hi, rfl⟩))
  · intro hw b hb
    rcases (h b).mp hb with rfl | ⟨i, hi, rfl⟩
    · rw [map_one]; rfl
    · exact hw i hi

theorem pu4Els_mem_That : ∀ i : Fin 5, i ≠ 3 → i ≠ 4 → pu4Els i ∈ S5ThatF := by decide +kernel

theorem adm_subgroup (B : Subgroup (Perm (Fin 5))) (hB : B ≤ S5Syl) (hsq : ∀ x ∈ B, x * x = 1)
    (hne : B ≠ ⊥) (hadm : 16 ≤ Nat.card B * Nat.card (fixW orth B)) :
    B ≤ S5That ∧ (swap 0 2 ∈ B ∨ swap 1 3 ∈ B) ∧ Nat.card B * Nat.card (fixW orth B) = 16 := by
  obtain ⟨p, hp⟩ := exists_flags B hB hsq
  have hclos : ∀ i j, p i = true → p j = true →
      pu4Els i * pu4Els j = 1 ∨ ∃ k, p k = true ∧ pu4Els i * pu4Els j = pu4Els k := by
    intro i j hi hj
    have hmem : pu4Els i * pu4Els j ∈ B :=
      B.mul_mem ((hp _).mpr (Or.inr ⟨i, hi, rfl⟩)) ((hp _).mpr (Or.inr ⟨j, hj, rfl⟩))
    rcases (hp _).mp hmem with h | ⟨k, hk, h⟩
    · exact Or.inl h
    · exact Or.inr ⟨k, hk, h⟩
  have hex : ∃ i, p i = true := by
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
    rcases (hp x).mp hx with h | ⟨i, hi, -⟩
    · exact absurd (Subtype.ext h) hx1
    · exact ⟨i, hi⟩
  rw [card_eq_of_flags hp, card_fixW_of_flags hp] at hadm ⊢
  obtain ⟨h3, h4, h01, heq⟩ := adm_flags p hclos hex hadm
  refine ⟨fun x hx => ?_, ?_, heq⟩
  swap
  · rcases h01 with h0 | h1
    · exact Or.inl ((hp _).mpr (Or.inr ⟨0, h0, rfl⟩))
    · exact Or.inr ((hp _).mpr (Or.inr ⟨1, h1, rfl⟩))
  rw [mem_S5That_iff]
  rcases (hp x).mp hx with rfl | ⟨i, hi, rfl⟩
  · decide +kernel
  · have hi5 : i ≠ 3 ∧ i ≠ 4 := by
      constructor <;> rintro rfl <;> simp_all
    exact pu4Els_mem_That i hi5.1 hi5.2

theorem card_fixW_That : Nat.card (fixW orth S5That) = 4 := by
  have := congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) profile_orth.2.2.1
  simpa [profile] using this

theorem index_fixW_That : (fixW orth S5That).index = 4 := by
  have h := Subgroup.index_mul_card (fixW orth S5That)
  rw [card_fixW_That, card_orth] at h
  omega

@[expose] def pu4Fix3 (σ : Perm (Fin 5)) : ℕ :=
  (Finset.univ.filter fun w : orth.W =>
    orth.act (swap 0 2) w = w ∧ orth.act (swap 1 3) w = w ∧ orth.act σ w = w).card

set_option maxRecDepth 100000 in
theorem pu4Fix3_le : ∀ σ ∈ S5SylF, σ ∉ S5ThatF → pu4Fix3 σ ≤ 2 := by
  decide +kernel

theorem card_fixW_le_two {B : Subgroup (Perm (Fin 5))} (h02 : swap 0 2 ∈ B) (h13 : swap 1 3 ∈ B)
    {σ : Perm (Fin 5)} (hσD : σ ∈ S5Syl) (hσT : σ ∉ S5That) (hσB : σ ∈ B) :
    Nat.card (fixW orth B) ≤ 2 := by
  classical
  refine le_trans ?_ (pu4Fix3_le σ ((mem_S5Syl_iff σ).mp hσD) (fun h => hσT ((mem_S5That_iff σ).mpr h)))
  unfold pu4Fix3
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_le_card_of_injective (fun w => ⟨w.1, ?_, ?_, ?_⟩) (fun a b h => ?_)
  · exact w.2 _ h02
  · exact w.2 _ h13
  · exact w.2 _ hσB
  · have := congrArg Subtype.val h
    exact Subtype.ext this

theorem swap_mem_trans {α : Type*} [DecidableEq α] (H : Subgroup (Perm α)) {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (h1 : swap a b ∈ H) (h2 : swap b c ∈ H) : swap a c ∈ H := by
  have e := Equiv.swap_mul_swap_mul_swap (x := a) (y := b) (z := c) hab hac
  rw [swap_comm c a] at e
  rw [← e]
  exact H.mul_mem (H.mul_mem h2 h1) h2

theorem top_of_swaps (H : Subgroup (Perm (Fin 5))) (h02 : swap (0 : Fin 5) 2 ∈ H)
    (h13 : swap (1 : Fin 5) 3 ∈ H) (h04 : swap (0 : Fin 5) 4 ∈ H) (h23 : swap (2 : Fin 5) 3 ∈ H) :
    H = ⊤ := by
  have h03 : swap (0 : Fin 5) 3 ∈ H := swap_mem_trans H (by decide) (by decide) h02 h23
  have h01 : swap (1 : Fin 5) 0 ∈ H := swap_mem_trans H (by decide) (by decide) h13
    (by rw [swap_comm]; exact h03)
  have h12 : swap (1 : Fin 5) 2 ∈ H := swap_mem_trans H (by decide) (by decide) h13
    (by rw [swap_comm]; exact h23)
  have h14 : swap (1 : Fin 5) 4 ∈ H := swap_mem_trans H (by decide) (by decide) h01 h04
  have h24 : swap (2 : Fin 5) 4 ∈ H := swap_mem_trans H (by decide) (by decide)
    (by rw [swap_comm]; exact h02) h04
  have h34 : swap (3 : Fin 5) 4 ∈ H := swap_mem_trans H (by decide) (by decide)
    (by rw [swap_comm]; exact h03) h04
  rw [eq_top_iff, ← Perm.closure_isSwap, Subgroup.closure_le]
  rintro σ ⟨x, y, hxy, rfl⟩
  have hs : ∀ a b : Fin 5, swap a b ∈ H → swap b a ∈ H := fun a b h => by rwa [swap_comm]
  fin_cases x <;> fin_cases y <;> first | exact absurd rfl hxy | assumption | exact hs _ _ ‹_›

@[expose] def pu4G : Perm (Fin 5) := swap 1 2 * swap 2 4

theorem pu4G_pow_three : pu4G ^ 3 = 1 := by unfold pu4G; decide +kernel

theorem pu4G_conj_02 : pu4G * swap 0 2 * pu4G⁻¹ = swap 0 4 := by unfold pu4G; decide +kernel

theorem pu4G_conj_13 : pu4G * swap 1 3 * pu4G⁻¹ = swap 2 3 := by unfold pu4G; decide +kernel

theorem top_of_conj_swaps (H : Subgroup (Perm (Fin 5))) (h02 : swap (0 : Fin 5) 2 ∈ H)
    (h13 : swap (1 : Fin 5) 3 ∈ H) (h04 : pu4G * swap 0 2 * pu4G⁻¹ ∈ H)
    (h23 : pu4G * swap 1 3 * pu4G⁻¹ ∈ H) : H = ⊤ := by
  rw [pu4G_conj_02] at h04
  rw [pu4G_conj_13] at h23
  exact top_of_swaps H h02 h13 h04 h23

@[expose] def pu4C : Perm (Fin 5) := swap 1 3 * swap 3 4

theorem pu4C_pow_three : pu4C ^ 3 = 1 := by unfold pu4C; decide +kernel

theorem pu4C_ne_one : pu4C ≠ 1 := by unfold pu4C; decide +kernel

theorem pu4C_conj_13 : pu4C * swap 1 3 * pu4C⁻¹ = swap 3 4 := by unfold pu4C; decide +kernel

theorem S5g_conj_34 : S5g * swap 3 4 * S5g⁻¹ = swap 0 4 := by unfold S5g; decide +kernel

theorem top_of_C_and_D (H : Subgroup (Perm (Fin 5))) (h02 : swap (0 : Fin 5) 2 ∈ H)
    (h13 : swap (1 : Fin 5) 3 ∈ H) (hC : pu4C ∈ H) (hD : S5Syl ≤ H) : H = ⊤ := by
  have hg : S5g ∈ H := hD (Subgroup.subset_closure (by simp [S5g]))
  have h34 : swap (3 : Fin 5) 4 ∈ H := by
    have := H.mul_mem (H.mul_mem hC h13) (H.inv_mem hC)
    rwa [pu4C_conj_13] at this
  have h04 : swap (0 : Fin 5) 4 ∈ H := by
    have := H.mul_mem (H.mul_mem hg h34) (H.inv_mem hg)
    rwa [S5g_conj_34] at this
  have h24 : swap (2 : Fin 5) 4 ∈ H := swap_mem_trans H (by decide) (by decide)
    (by rw [swap_comm]; exact h02) h04
  have h23 : swap (2 : Fin 5) 3 ∈ H := swap_mem_trans H (by decide) (by decide) h24
    (by rw [swap_comm]; exact h34)
  exact top_of_swaps H h02 h13 h04 h23

@[expose] def pu4F : Perm (Fin 5) := swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4

theorem pu4F_pow_five : pu4F ^ 5 = 1 := by unfold pu4F; decide +kernel

theorem idx_orth_pu4F : idx orth pu4F = 16 := by
  rw [idx_orth]
  unfold pu4F
  decide +kernel

@[expose] def pu4A3 : Subgroup (Perm (Fin 5)) := Subgroup.zpowers pu4C

theorem mem_pu4A3_iff (σ : Perm (Fin 5)) :
    σ ∈ pu4A3 ↔ σ = 1 ∨ σ = pu4C ∨ σ = pu4C ^ 2 := by
  unfold pu4A3
  rw [mem_zpowers_iff_of_pow_eq_one (m := 3) pu4C_pow_three (by norm_num)]
  constructor
  · rintro ⟨k, hk, rfl⟩
    interval_cases k <;> simp
  · rintro (rfl | rfl | rfl)
    · exact ⟨0, by norm_num, by simp⟩
    · exact ⟨1, by norm_num, by simp⟩
    · exact ⟨2, by norm_num, rfl⟩

theorem card_pu4A3 : Nat.card pu4A3 = 3 := by
  unfold pu4A3
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime pu4C_pow_three pu4C_ne_one

theorem centralizer_cases : ∀ σ : Perm (Fin 5), σ * swap 0 2 = swap 0 2 * σ →
    σ ^ 6 = 1 ∧ (σ = 1 ∨ σ = pu4C ∨ σ = pu4C ^ 2 ∨ σ ^ 3 ≠ 1) := by
  unfold pu4C
  decide +kernel

theorem mem_pu4A3_of_odd {σ : Perm (Fin 5)} (hc : σ * swap 0 2 = swap 0 2 * σ) {m : ℕ}
    (hm : Odd m) (hσ : σ ^ m = 1) : σ ∈ pu4A3 := by
  obtain ⟨h6, h⟩ := centralizer_cases σ hc
  rw [mem_pu4A3_iff]
  rcases h with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · exfalso
    apply h
    have h1 : σ ^ Nat.gcd m 6 = 1 := pow_gcd_eq_one.mpr ⟨hσ, h6⟩
    have h2 : Nat.gcd m 6 ∣ 3 := by
      have hg : Nat.Coprime (Nat.gcd m 6) 2 :=
        (Nat.coprime_two_right.mpr hm).coprime_dvd_left (Nat.gcd_dvd_left m 6)
      exact hg.dvd_of_dvd_mul_right (show Nat.gcd m 6 ∣ 3 * 2 from Nat.gcd_dvd_right m 6)
    obtain ⟨k, hk⟩ := h2
    calc σ ^ 3 = σ ^ (Nat.gcd m 6 * k) := by rw [← hk]
      _ = 1 := by rw [pow_mul, h1, one_pow]

theorem pu4A3_inf_That : ∀ σ : Perm (Fin 5), σ ∈ pu4A3 → σ ∈ S5That → σ = 1 := by
  intro σ h1 h2
  rw [mem_pu4A3_iff] at h1
  rw [mem_S5That_iff] at h2
  revert h1 h2
  revert σ
  unfold pu4C
  decide +kernel

end CFSG.Quasithin.F53Push
