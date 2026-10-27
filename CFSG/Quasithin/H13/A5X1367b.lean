module

public import CFSG.Quasithin.H13.A5S136f

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

section FourGroup

variable {U : Type} [Group U]

theorem eq_of_card_four {E : Subgroup U} (hE : Nat.card E = 4) {a b c d : U}
    (ha : a ∈ E) (hb : b ∈ E) (hc : c ∈ E) (hd : d ∈ E)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    {e : U} (he : e ∈ E) : e = a ∨ e = b ∨ e = c ∨ e = d := by
  by_contra h
  push Not at h
  obtain ⟨hea, heb, hec, hed⟩ := h
  have hfin : (E : Set U).Finite := by
    have : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
    exact Set.toFinite _
  have h5 : ({e, a, b, c, d} : Set U).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [hea, heb, hec, hed]),
      Set.ncard_insert_of_notMem (by simp [hab, hac, had]),
      Set.ncard_insert_of_notMem (by simp [hbc, hbd]), Set.ncard_pair hcd]
  have hle : ({e, a, b, c, d} : Set U).ncard ≤ (E : Set U).ncard := by
    refine Set.ncard_le_ncard ?_ hfin
    intro x hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact he
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hEn : (E : Set U).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hE
  rw [h5, hEn] at hle
  omega

theorem pow_apply_mod_three {E : Subgroup U} {β : MulAut U}
    (h3 : ∀ e ∈ E, (β ^ 3) e = e) (n : ℕ) {e : U} (he : e ∈ E) : (β ^ n) e = (β ^ (n % 3)) e := by
  induction n using Nat.strong_induction_on generalizing e with
  | _ n ih =>
    rcases Nat.lt_or_ge n 3 with hn | hn
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rw [pow_add, MulAut.mul_apply, h3 e he, ih m (by omega) he]
      congr 2
      omega

theorem four_cases {E : Subgroup U} (hE : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    {x y : U} (hx : x ∈ E) (hy : y ∈ E) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x ≠ y) :
    x * y ≠ 1 ∧ x * y ≠ x ∧ x * y ≠ y ∧ ∀ t ∈ E, t = 1 ∨ t = x ∨ t = y ∨ t = x * y := by
  have hinvE : ∀ t ∈ E, t⁻¹ = t := fun t ht => inv_eq_of_mul_eq_one_right (hE2 t ht)
  have h1 : x * y ≠ 1 := by
    intro h
    apply hxy
    calc x = x * y * y⁻¹ := by group
      _ = y := by rw [h, one_mul, hinvE y hy]
  have h2 : x * y ≠ x := by
    intro h
    apply hy1
    calc y = x⁻¹ * (x * y) := by group
      _ = 1 := by rw [h, inv_mul_cancel]
  have h3 : x * y ≠ y := by
    intro h
    apply hx1
    calc x = x * y * y⁻¹ := by group
      _ = 1 := by rw [h, mul_inv_cancel]
  exact ⟨h1, h2, h3, fun t ht => eq_of_card_four hE E.one_mem hx hy (E.mul_mem hx hy) hx1.symm
    hy1.symm h1.symm hxy h2.symm h3.symm ht⟩

theorem four_comm {E : Subgroup U} (hE2 : ∀ e ∈ E, e * e = 1) {x y : U} (hx : x ∈ E)
    (hy : y ∈ E) : x * y = y * x := by
  have hinvE : ∀ t ∈ E, t⁻¹ = t := fun t ht => inv_eq_of_mul_eq_one_right (hE2 t ht)
  calc x * y = (x * y)⁻¹ := (hinvE _ (E.mul_mem hx hy)).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hinvE y hy, hinvE x hx]

theorem eq_of_swap_of_odd {α : MulAut U} (hα : Odd (orderOf α)) {x y : U} (hxy : α x = y)
    (hyx : α y = x) : x = y := by
  obtain ⟨m, hm⟩ := hα
  have hp : ∀ j : ℕ, (α ^ (2 * j + 1)) x = y := by
    intro j
    induction j with
    | zero => simpa using hxy
    | succ j ih =>
      rw [show 2 * (j + 1) + 1 = 2 + (2 * j + 1) by ring, pow_add, MulAut.mul_apply, ih,
        pow_two, MulAut.mul_apply, hyx, hxy]
  have := hp m
  rw [← hm, pow_orderOf_eq_one, MulAut.one_apply] at this
  exact this

theorem four_two_aut {E : Subgroup U} (hE : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    {β : MulAut U} (hβE : ∀ e ∈ E, β e ∈ E) (hβ : ∃ k : ℕ, β ^ 2 ^ k = 1)
    (hβ1 : ∃ e ∈ E, β e ≠ e) :
    ∃ a ∈ E, a ≠ 1 ∧ β a ≠ a ∧ β (β a) = a ∧ β (a * β a) = a * β a := by
  obtain ⟨a, haE, hβa⟩ := hβ1
  have hbE : β a ∈ E := hβE a haE
  have ha1 : a ≠ 1 := by rintro rfl; exact hβa (map_one β)
  have hb1 : β a ≠ 1 := fun h => ha1 (β.injective (h.trans (map_one β).symm))
  have hab : a ≠ β a := fun h => hβa h.symm
  obtain ⟨hc1, hca, hcb, hmem⟩ := four_cases hE hE2 haE hbE ha1 hb1 hab
  refine ⟨a, haE, ha1, hβa, ?_, ?_⟩
  · rcases hmem _ (hβE _ hbE) with h | h | h | h
    · exact absurd (β.injective (h.trans (map_one β).symm)) hb1
    · exact h
    · exact absurd (β.injective h) hab.symm
    · exfalso
      have hβc : β (a * β a) = a := by
        rw [map_mul, h, ← mul_assoc, four_comm hE2 hbE haE, mul_assoc, hE2 _ hbE, mul_one]
      have h3 : ∀ e ∈ E, (β ^ 3) e = e := by
        intro e he
        have e3 : (β ^ 3) e = β (β (β e)) := by
          rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
        rcases hmem e he with rfl | rfl | rfl | rfl
        · simp
        · rw [e3, h, hβc]
        · rw [e3, h, hβc]
        · rw [e3, hβc, h]
      obtain ⟨k, hk⟩ := hβ
      have hk' := pow_apply_mod_three h3 (2 ^ k) haE
      rw [hk, MulAut.one_apply] at hk'
      have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
        have : 2 ^ k % 3 ≠ 0 := by
          intro h0
          have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
          have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
            (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
          omega
        omega
      rcases hmod with hm | hm
      · rw [hm, pow_one] at hk'
        exact hβa hk'.symm
      · rw [hm, pow_two, MulAut.mul_apply, h] at hk'
        exact hca hk'.symm
  · have hβb : β (β a) = a := by
      rcases hmem _ (hβE _ hbE) with h | h | h | h
      · exact absurd (β.injective (h.trans (map_one β).symm)) hb1
      · exact h
      · exact absurd (β.injective h) hab.symm
      · exfalso
        have hβc : β (a * β a) = a := by
          rw [map_mul, h, ← mul_assoc, four_comm hE2 hbE haE, mul_assoc, hE2 _ hbE, mul_one]
        have h3 : ∀ e ∈ E, (β ^ 3) e = e := by
          intro e he
          have e3 : (β ^ 3) e = β (β (β e)) := by
            rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
          rcases hmem e he with rfl | rfl | rfl | rfl
          · simp
          · rw [e3, h, hβc]
          · rw [e3, h, hβc]
          · rw [e3, hβc, h]
        obtain ⟨k, hk⟩ := hβ
        have hk' := pow_apply_mod_three h3 (2 ^ k) haE
        rw [hk, MulAut.one_apply] at hk'
        have hmod : 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
          have : 2 ^ k % 3 ≠ 0 := by
            intro h0
            have h3 : 3 ∣ 2 ^ k := Nat.dvd_of_mod_eq_zero h0
            have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
              (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
            omega
          omega
        rcases hmod with hm | hm
        · rw [hm, pow_one] at hk'
          exact hβa hk'.symm
        · rw [hm, pow_two, MulAut.mul_apply, h] at hk'
          exact hca hk'.symm
    rw [map_mul, hβb, four_comm hE2 hbE haE]

theorem exists_ne_of_card_four {E : Subgroup U} (hE : Nat.card E = 4) (x : U) :
    ∃ y ∈ E, y ≠ 1 ∧ y ≠ x := by
  by_contra h
  push Not at h
  have hfin : (E : Set U).Finite := by
    have : Finite ↥E := Nat.finite_of_card_ne_zero (by rw [hE]; norm_num)
    exact Set.toFinite _
  have hsub : (E : Set U) ⊆ {1, x} := fun y hy => by
    by_cases h1 : y = 1
    · exact Or.inl h1
    · exact Or.inr (h y hy h1)
  have hle : (E : Set U).ncard ≤ ({1, x} : Set U).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h2 : ({1, x} : Set U).ncard ≤ 2 := Set.ncard_insert_le _ _ |>.trans (by simp)
  have hEn : (E : Set U).ncard = 4 := by rw [← Nat.card_coe_set_eq]; exact hE
  omega

theorem four_odd_nofix {E : Subgroup U} (hE : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    {α : MulAut U} (hαE : ∀ e ∈ E, α e ∈ E) (hα : Odd (orderOf α))
    (hα1 : ∃ e ∈ E, α e ≠ e) {x : U} (hx : x ∈ E) (hx1 : x ≠ 1) : α x ≠ x := by
  intro hαx
  have hαinj : ∀ x y : U, α x = α y → x = y := fun x y h => α.injective h
  obtain ⟨y, hy, hy1, hyx⟩ := exists_ne_of_card_four hE x
  obtain ⟨hw1, hwx, hwy, hall⟩ := four_cases hE hE2 hx hy hx1 hy1 (fun h => hyx h.symm)
  have hαy : α y = y := by
    rcases hall _ (hαE y hy) with h | h | h | h
    · exact absurd (hαinj _ _ (h.trans (map_one α).symm)) hy1
    · exact absurd (hαinj _ _ (h.trans hαx.symm)) hyx
    · exact h
    · exfalso
      have hαw : α (x * y) = y := by
        rw [map_mul, hαx, h, ← mul_assoc, hE2 x hx, one_mul]
      exact hwy (eq_of_swap_of_odd hα h hαw).symm
  obtain ⟨e, heE, hαe⟩ := hα1
  apply hαe
  rcases hall e heE with rfl | rfl | rfl | rfl
  · exact map_one α
  · exact hαx
  · exact hαy
  · rw [map_mul, hαx, hαy]

theorem four_odd_aut {E : Subgroup U} (hE : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    {α : MulAut U} (hαE : ∀ e ∈ E, α e ∈ E) (hα : Odd (orderOf α))
    (hα1 : ∃ e ∈ E, α e ≠ e) {a b : U} (ha : a ∈ E) (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1)
    (hab : a ≠ b) :
    (α a = b ∧ α b = a * b ∧ α (a * b) = a) ∨ (α a = a * b ∧ α (a * b) = b ∧ α b = a) := by
  obtain ⟨hc1, hca, hcb, hmem⟩ := four_cases hE hE2 ha hb ha1 hb1 hab
  have hαinj : ∀ x y : U, α x = α y → x = y := fun x y h => α.injective h
  have hnofix : ∀ x ∈ E, x ≠ 1 → α x ≠ x := by
    intro x hx hx1 hαx
    obtain ⟨y, hy, hy1, hyx⟩ : ∃ y ∈ E, y ≠ 1 ∧ y ≠ x := by
      by_cases hxa : x = a
      · exact ⟨b, hb, hb1, by rw [hxa]; exact hab.symm⟩
      · exact ⟨a, ha, ha1, fun h => hxa h.symm⟩
    obtain ⟨hw1, hwx, hwy, hall⟩ := four_cases hE hE2 hx hy hx1 hy1 (fun h => hyx h.symm)
    have hαy : α y = y := by
      rcases hall _ (hαE y hy) with h | h | h | h
      · exact absurd (hαinj _ _ (h.trans (map_one α).symm)) hy1
      · exact absurd (hαinj _ _ (h.trans hαx.symm)) hyx
      · exact h
      · exfalso
        have hαw : α (x * y) = y := by
          rw [map_mul, hαx, h, ← mul_assoc, hE2 x hx, one_mul]
        exact hwy (eq_of_swap_of_odd hα h hαw).symm
    obtain ⟨e, heE, hαe⟩ := hα1
    apply hαe
    rcases hall e heE with rfl | rfl | rfl | rfl
    · exact map_one α
    · exact hαx
    · exact hαy
    · rw [map_mul, hαx, hαy]
  rcases hmem _ (hαE a ha) with h | h | h | h
  · exact absurd (hαinj _ _ (h.trans (map_one α).symm)) ha1
  · exact absurd h (hnofix a ha ha1)
  · left
    have hαb : α b = a * b := by
      rcases hmem _ (hαE b hb) with h' | h' | h' | h'
      · exact absurd (hαinj _ _ (h'.trans (map_one α).symm)) hb1
      · exact absurd (eq_of_swap_of_odd hα h h') hab
      · exact absurd h' (hnofix b hb hb1)
      · exact h'
    refine ⟨h, hαb, ?_⟩
    rw [map_mul, h, hαb, ← mul_assoc, four_comm hE2 hb ha, mul_assoc, hE2 b hb, mul_one]
  · right
    have hαc : α (a * b) = b := by
      rcases hmem _ (hαE _ (E.mul_mem ha hb)) with h' | h' | h' | h'
      · exact absurd (hαinj _ _ (h'.trans (map_one α).symm)) hc1
      · exact absurd (eq_of_swap_of_odd hα h h') hca.symm
      · exact h'
      · exact absurd h' (hnofix _ (E.mul_mem ha hb) hc1)
    refine ⟨h, hαc, ?_⟩
    have hb' : b = a * (a * b) := by rw [← mul_assoc, hE2 a ha, one_mul]
    rw [hb', map_mul, h, hαc, mul_assoc, hE2 b hb, mul_one]

theorem four_aut {E : Subgroup U} (hE : Nat.card E = 4) (hE2 : ∀ e ∈ E, e * e = 1)
    {α β : MulAut U} (hαE : ∀ e ∈ E, α e ∈ E) (hβE : ∀ e ∈ E, β e ∈ E)
    (hα : Odd (orderOf α)) (hβ : ∃ k : ℕ, β ^ 2 ^ k = 1)
    (hα1 : ∃ e ∈ E, α e ≠ e) (hβ1 : ∃ e ∈ E, β e ≠ e) :
    (∀ e ∈ E, β⁻¹ (α (β e)) = α⁻¹ e) ∧ ∀ e ∈ E, (α ^ 3) e = e := by
  obtain ⟨a, haE, ha1, hβa, hβb, hβc⟩ := four_two_aut hE hE2 hβE hβ hβ1
  have hbE : β a ∈ E := hβE a haE
  have hb1 : β a ≠ 1 := fun h => ha1 (β.injective (h.trans (map_one β).symm))
  have hab : a ≠ β a := fun h => hβa h.symm
  obtain ⟨-, -, -, hmem⟩ := four_cases hE hE2 haE hbE ha1 hb1 hab
  have hinvβ : ∀ x y : U, β x = y → β⁻¹ y = x := fun x y h => by
    rw [← h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have hinvα : ∀ x y : U, α x = y → α⁻¹ y = x := fun x y h => by
    rw [← h, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
  have e3 : ∀ x : U, (α ^ 3) x = α (α (α x)) := fun x => by
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply]
  rcases four_odd_aut hE hE2 hαE hα hα1 haE hbE ha1 hb1 hab with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rcases hmem e he with rfl | rfl | rfl | rfl
      · simp
      · rw [h2, hinvβ _ _ hβc, hinvα _ _ h3]
      · rw [hβb, h1, hinvβ _ _ rfl, hinvα _ _ h1]
      · rw [hβc, h3, hinvβ _ _ hβb, hinvα _ _ h2]
    · rcases hmem e he with rfl | rfl | rfl | rfl
      · simp
      · rw [e3, h1, h2, h3]
      · rw [e3, h2, h3, h1]
      · rw [e3, h3, h1, h2]
  · refine ⟨fun e he => ?_, fun e he => ?_⟩
    · rcases hmem e he with rfl | rfl | rfl | rfl
      · simp
      · rw [h3, hinvβ _ _ hβb, hinvα _ _ h3]
      · rw [hβb, h1, hinvβ _ _ hβc, hinvα _ _ h2]
      · rw [hβc, h2, hinvβ _ _ rfl, hinvα _ _ h1]
    · rcases hmem e he with rfl | rfl | rfl | rfl
      · simp
      · rw [e3, h1, h2, h3]
      · rw [e3, h3, h1, h2]
      · rw [e3, h2, h3, h1]

end FourGroup

@[expose] def E23 : W5 := Multiplicative.ofAdd (e2 2 3)

@[expose] def E24 : W5 := Multiplicative.ofAdd (e2 2 4)

@[expose] def E34 : W5 := Multiplicative.ofAdd (e2 3 4)

theorem c01_ker_comm_c234 : ∀ c ∈ [c234, c234⁻¹], ∀ x : W5, c01 x = 1 →
    ∃ y : W5, c01 y = 1 ∧ (x = pact c y * y⁻¹ ∨ x = E12 * (pact c y * y⁻¹)) := by
  decide +kernel

theorem comm_c234_mem : ∀ c ∈ [c234, c234⁻¹], ∀ y : W5, c01 y = 1 →
    pact c y * y⁻¹ ∈ [1, E23, E24, E34] := by
  decide +kernel

theorem comm_c234_surj : ∀ c ∈ [c234, c234⁻¹], ∀ x ∈ [1, E23, E24, E34],
    ∃ y : W5, c01 y = 1 ∧ pact c y * y⁻¹ = x := by
  decide +kernel

theorem E23_facts : (1 : W5) ≠ E23 ∧ (1 : W5) ≠ E24 ∧ (1 : W5) ≠ E34 ∧ E23 ≠ E24 ∧ E23 ≠ E34 ∧
    E24 ≠ E34 := by
  decide +kernel

theorem stab_E12_cases : ∀ σ : Equiv.Perm (Fin 5), σ.sign = 1 → pact σ E12 = E12 →
    σ = 1 ∨ σ = c234 ∨ σ = c234⁻¹ ∨ σ ^ 2 = 1 := by
  decide +kernel

theorem odd_mem_c234 {σ : Equiv.Perm (Fin 5)} (hs : σ.sign = 1) (hE : pact σ E12 = E12)
    {m : ℕ} (hm : Odd m) (hσm : σ ^ m = 1) : σ = 1 ∨ σ = c234 ∨ σ = c234⁻¹ := by
  rcases stab_E12_cases σ hs hE with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)
  · left
    obtain ⟨j, rfl⟩ := hm
    rw [pow_succ, pow_mul, h, one_pow, one_mul] at hσm
    exact hσm

theorem conj_c234_of_D : ∀ σ : Equiv.Perm (Fin 5), InD σ → pact σ E12 = E12 →
    σ⁻¹ * c234 * σ = c234 ∨ σ⁻¹ * c234 * σ = c234⁻¹ := by
  decide +kernel

end CFSG.Quasithin.H13.A5
