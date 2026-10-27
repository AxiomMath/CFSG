module

public import Mathlib.GroupTheory.SpecificGroups.Alternating

public section

namespace CFSG.Quasithin.LRed10

open Equiv Equiv.Perm

theorem swap_conj_swap : ∀ x y z : Fin 5, x ≠ y → y ≠ z → x ≠ z →
    swap x y * swap y z * swap x y = swap x z := by decide

theorem cover_five : ∀ a b c d e x : Fin 5, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d →
    b ≠ e → c ≠ d → c ≠ e → d ≠ e → x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := by decide

theorem closure_path_four (a b c d e : Fin 5) (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hae : a ≠ e) (hbc : b ≠ c) (hbd : b ≠ d) (hbe : b ≠ e) (hcd : c ≠ d) (hce : c ≠ e)
    (hde : d ≠ e) :
    Subgroup.closure {swap a b, swap c d, swap b c, swap d e} = (⊤ : Subgroup (Perm (Fin 5))) := by
  set C := Subgroup.closure {swap a b, swap c d, swap b c, swap d e} with hC
  have hab' : swap a b ∈ C := Subgroup.subset_closure (by simp)
  have hcd' : swap c d ∈ C := Subgroup.subset_closure (by simp)
  have hbc' : swap b c ∈ C := Subgroup.subset_closure (by simp)
  have hde' : swap d e ∈ C := Subgroup.subset_closure (by simp)
  have trans : ∀ x y z : Fin 5, x ≠ y → y ≠ z → x ≠ z → swap x y ∈ C → swap y z ∈ C →
      swap x z ∈ C := by
    intro x y z hxy hyz hxz h1 h2
    rw [← swap_conj_swap x y z hxy hyz hxz]
    exact C.mul_mem (C.mul_mem h1 h2) h1
  have symm : ∀ x y : Fin 5, swap x y ∈ C → swap y x ∈ C := fun x y h => by rwa [swap_comm]
  have hac' : swap a c ∈ C := trans a b c hab hbc hac hab' hbc'
  have hbd' : swap b d ∈ C := trans b c d hbc hcd hbd hbc' hcd'
  have hce' : swap c e ∈ C := trans c d e hcd hde hce hcd' hde'
  have had' : swap a d ∈ C := trans a b d hab hbd had hab' hbd'
  have hbe' : swap b e ∈ C := trans b c e hbc hce hbe hbc' hce'
  have hae' : swap a e ∈ C := trans a b e hab hbe hae hab' hbe'
  have hcov : ∀ x : Fin 5, x = a ∨ x = b ∨ x = c ∨ x = d ∨ x = e := fun x =>
    cover_five a b c d e x hab hac had hae hbc hbd hbe hcd hce hde
  have hall : ∀ x y : Fin 5, x ≠ y → swap x y ∈ C := by
    intro x y hxy
    rcases hcov x with rfl | rfl | rfl | rfl | rfl <;>
      rcases hcov y with rfl | rfl | rfl | rfl | rfl <;>
      first
      | exact absurd rfl hxy
      | assumption
      | exact symm _ _ ‹_›
  refine eq_top_iff.2 ?_
  rw [← Equiv.Perm.closure_isSwap]
  refine (Subgroup.closure_le _).2 ?_
  rintro σ ⟨x, y, hxy, rfl⟩
  exact hall x y hxy

theorem involution_ne_one_isSwap_or_sq : ∀ ρ : Perm (Fin 5), ρ * ρ = 1 → ρ ≠ 1 →
    (∃ a b : Fin 5, a ≠ b ∧ ρ = swap a b) ∨ ∃ τ : Perm (Fin 5), τ * τ = ρ := by
  decide +kernel

theorem swap_not_sq (a b : Fin 5) (hab : a ≠ b) : ¬ ∃ τ : Perm (Fin 5), τ * τ = swap a b := by
  rintro ⟨τ, hτ⟩
  have h1 : sign (τ * τ) = sign (swap a b) := by rw [hτ]
  rw [Perm.sign_mul, sign_swap hab] at h1
  rcases Int.units_eq_one_or (sign τ) with h | h <;> rw [h] at h1 <;> exact absurd h1 (by decide)

theorem swap_ne_one' {a b : Fin 5} (hab : a ≠ b) : (swap a b : Perm (Fin 5)) ≠ 1 := by
  intro h
  have := congrArg (fun f : Perm (Fin 5) => f a) h
  simp [swap_apply_left] at this
  exact hab this.symm

theorem isSwap_of_mulEquiv (e : Perm (Fin 5) ≃* Perm (Fin 5)) {σ : Perm (Fin 5)} (h : σ.IsSwap) :
    (e σ).IsSwap := by
  obtain ⟨a, b, hab, rfl⟩ := h
  have h1 : e (swap a b) * e (swap a b) = 1 := by
    rw [← map_mul, swap_mul_self, map_one]
  have h2 : e (swap a b) ≠ 1 := by
    intro h2
    have := e.injective (h2.trans (map_one e).symm)
    exact swap_ne_one' hab this
  rcases involution_ne_one_isSwap_or_sq _ h1 h2 with h3 | ⟨τ, hτ⟩
  · obtain ⟨c, d, hcd, hd⟩ := h3
    exact ⟨c, d, hcd, hd⟩
  · exfalso
    apply swap_not_sq a b hab
    refine ⟨e.symm τ, ?_⟩
    apply e.injective
    rw [map_mul]
    simpa using hτ

@[expose] def cyc5 (a b c d e : Fin 5) : Perm (Fin 5) := swap a b * swap b c * swap c d * swap d e

theorem cyc5_conj : ∀ a b c d e : Fin 5, a ≠ b → a ≠ c → a ≠ d → a ≠ e → b ≠ c → b ≠ d →
    b ≠ e → c ≠ d → c ≠ e → d ≠ e →
    cyc5 a b c d e * swap a b * (cyc5 a b c d e)⁻¹ = swap b c ∧
      cyc5 a b c d e * swap c d * (cyc5 a b c d e)⁻¹ = swap d e := by
  decide +kernel

theorem sign_cyc5 {a b c d e : Fin 5} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (hde : d ≠ e) :
    sign (cyc5 a b c d e) = 1 := by
  unfold cyc5
  rw [Perm.sign_mul, Perm.sign_mul, Perm.sign_mul, sign_swap hab, sign_swap hbc, sign_swap hcd,
    sign_swap hde]
  decide

theorem exists_fifth : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    ∃ e : Fin 5, a ≠ e ∧ b ≠ e ∧ c ≠ e ∧ d ≠ e := by decide

@[expose] def Ev (f : Fin 5 → ZMod 2) : Prop := f 0 + f 1 + f 2 + f 3 + f 4 = 0

instance : DecidablePred Ev := fun f => inferInstanceAs (Decidable (f 0 + f 1 + f 2 + f 3 + f 4 = 0))

@[expose] def Fixed (σ : Perm (Fin 5)) (f : Fin 5 → ZMod 2) : Prop := ∀ i, f (σ⁻¹ i) = f i

@[expose] def FixSet (S : Set (Perm (Fin 5))) : Type :=
  {f : Fin 5 → ZMod 2 // Ev f ∧ ∀ σ ∈ S, Fixed σ f}

@[expose] def allVecs : List (Fin 5 → ZMod 2) :=
  (List.finRange 32).map fun n => fun i => (((n.val >>> i.val) % 2 : ℕ) : ZMod 2)

theorem mem_allVecs : ∀ f : Fin 5 → ZMod 2, f ∈ allVecs := by decide +kernel

theorem nodup_allVecs : allVecs.Nodup := by decide +kernel

theorem card_subtype_eq_length (P : (Fin 5 → ZMod 2) → Prop) [DecidablePred P] :
    Nat.card {f : Fin 5 → ZMod 2 // P f} = (allVecs.filter fun f => decide (P f)).length := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have : Finset.univ.filter P = (allVecs.filter fun f => decide (P f)).toFinset := by
    ext f
    simp [mem_allVecs f]
  rw [this]
  exact List.toFinset_card_of_nodup (nodup_allVecs.filter _)

theorem card_ev : Nat.card {f : Fin 5 → ZMod 2 // Ev f} = 16 := by
  rw [card_subtype_eq_length]
  decide +kernel

theorem card_ev_swap : ∀ a b : Fin 5, a ≠ b → Nat.card {f : Fin 5 → ZMod 2 // Ev f ∧ f a = f b} = 8 := by
  intro a b hab
  rw [card_subtype_eq_length]
  revert a b
  decide +kernel

theorem card_ev_two : ∀ a b c d : Fin 5, (a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d) →
    Nat.card {f : Fin 5 → ZMod 2 // Ev f ∧ f a = f b ∧ f c = f d} = 4 := by
  intro a b c d h
  rw [card_subtype_eq_length]
  revert a b c d
  decide +kernel

theorem fixed_one (f : Fin 5 → ZMod 2) : Fixed 1 f := fun i => by simp

theorem fixed_mul {σ τ : Perm (Fin 5)} {f : Fin 5 → ZMod 2} (h₁ : Fixed σ f) (h₂ : Fixed τ f) :
    Fixed (σ * τ) f := fun i => by
  rw [mul_inv_rev, Perm.mul_apply, h₂ (σ⁻¹ i), h₁ i]

theorem fixed_swap_iff {a b : Fin 5} {f : Fin 5 → ZMod 2} : Fixed (swap a b) f ↔ f a = f b := by
  constructor
  · intro h
    have := h a
    rw [swap_inv, swap_apply_left] at this
    exact this.symm
  · intro h i
    rw [swap_inv]
    by_cases hia : i = a
    · subst hia
      rw [swap_apply_left, h]
    · by_cases hib : i = b
      · subst hib
        rw [swap_apply_right, h]
      · rw [swap_apply_of_ne_of_ne hia hib]

theorem fixed_swap_mul_iff {a b c d : Fin 5} (hac : a ≠ c) (hbc : b ≠ c)
    (hbd : b ≠ d) {f : Fin 5 → ZMod 2} :
    Fixed (swap a b * swap c d) f ↔ f a = f b ∧ f c = f d := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · have := h a
      rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply, swap_apply_left,
        swap_apply_of_ne_of_ne hbc hbd] at this
      exact this.symm
    · have := h c
      rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply,
        swap_apply_of_ne_of_ne hac.symm hbc.symm, swap_apply_left] at this
      exact this.symm
  · rintro ⟨h₁, h₂⟩
    exact fixed_mul (fixed_swap_iff.2 h₁) (fixed_swap_iff.2 h₂)

theorem card_fixSet_le_card (S : Set (Perm (Fin 5))) {P : (Fin 5 → ZMod 2) → Prop}
    (h : ∀ f, Ev f → (∀ σ ∈ S, Fixed σ f) → P f) :
    Nat.card (FixSet S) ≤ Nat.card {f : Fin 5 → ZMod 2 // P f} := by
  refine Nat.card_le_card_of_injective
    (fun f : {f : Fin 5 → ZMod 2 // Ev f ∧ ∀ σ ∈ S, Fixed σ f} =>
      (⟨f.1, h f.1 f.2.1 f.2.2⟩ : {f : Fin 5 → ZMod 2 // P f})) ?_
  intro f g hfg
  exact Subtype.ext (by simpa using congrArg Subtype.val hfg)

theorem card_fixSet_le_sixteen (S : Set (Perm (Fin 5))) : Nat.card (FixSet S) ≤ 16 := by
  rw [← card_ev]
  exact card_fixSet_le_card S fun f hf _ => hf

theorem card_fixSet_le_of_swap {S : Set (Perm (Fin 5))} {a b : Fin 5} (hab : a ≠ b)
    (h : swap a b ∈ S) : Nat.card (FixSet S) ≤ 8 := by
  rw [← card_ev_swap a b hab]
  exact card_fixSet_le_card S fun f hf hS => ⟨hf, fixed_swap_iff.1 (hS _ h)⟩

theorem card_fixSet_le_of_swap_mul {S : Set (Perm (Fin 5))} {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hbd : b ≠ d)
    (h : swap a b * swap c d ∈ S) : Nat.card (FixSet S) ≤ 8 := by
  rw [← card_ev_swap a b hab]
  exact card_fixSet_le_card S fun f hf hS =>
    ⟨hf, ((fixed_swap_mul_iff hac hbc hbd).1 (hS _ h)).1⟩

theorem card_fixSet_le_four {S : Set (Perm (Fin 5))} {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h₁ : swap a b ∈ S) (h₂ : swap c d ∈ S) : Nat.card (FixSet S) ≤ 4 := by
  rw [← card_ev_two a b c d ⟨hab, hac, had, hbc, hbd, hcd⟩]
  exact card_fixSet_le_card S fun f hf hS =>
    ⟨hf, fixed_swap_iff.1 (hS _ h₁), fixed_swap_iff.1 (hS _ h₂)⟩

theorem card_fixSet_eq_four {S : Set (Perm (Fin 5))} {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (hS : ∀ σ ∈ S, σ = 1 ∨ σ = swap a b ∨ σ = swap c d ∨ σ = swap a b * swap c d)
    (h₁ : swap a b ∈ S) (h₂ : swap c d ∈ S) : Nat.card (FixSet S) = 4 := by
  rw [← card_ev_two a b c d ⟨hab, hac, had, hbc, hbd, hcd⟩]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun f => ?_)
  constructor
  · rintro ⟨hf, hS'⟩
    exact ⟨hf, fixed_swap_iff.1 (hS' _ h₁), fixed_swap_iff.1 (hS' _ h₂)⟩
  · rintro ⟨hf, e₁, e₂⟩
    refine ⟨hf, fun σ hσ => ?_⟩
    rcases hS σ hσ with rfl | rfl | rfl | rfl
    · exact fixed_one f
    · exact fixed_swap_iff.2 e₁
    · exact fixed_swap_iff.2 e₂
    · exact fixed_mul (fixed_swap_iff.2 e₁) (fixed_swap_iff.2 e₂)

theorem card_le_three {B : Subgroup (Perm (Fin 5))} {x y : Perm (Fin 5)}
    (h : ∀ σ ∈ B, σ = 1 ∨ σ = x ∨ σ = y) : Nat.card ↥B ≤ 3 := by
  classical
  have h1 : (B : Set (Perm (Fin 5))) ⊆ {1, x, y} := fun σ hσ => by
    rcases h σ hσ with rfl | rfl | rfl <;> simp
  calc Nat.card ↥B = Set.ncard (B : Set (Perm (Fin 5))) := (Nat.card_coe_set_eq _).symm
    _ ≤ Set.ncard ({1, x, y} : Set (Perm (Fin 5))) := Set.ncard_le_ncard h1
    _ ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        have := Set.ncard_insert_le x ({y} : Set (Perm (Fin 5)))
        rw [Set.ncard_singleton] at this
        omega

theorem swaps_mem_of_card_eq_four {a b c d : Fin 5} (B : Subgroup (Perm (Fin 5)))
    (hB : ∀ σ ∈ B, σ = 1 ∨ σ = swap a b ∨ σ = swap c d ∨ σ = swap a b * swap c d)
    (h4 : Nat.card ↥B = 4) : swap a b ∈ B ∧ swap c d ∈ B := by
  constructor
  · by_contra hx
    have := card_le_three (B := B) (x := swap c d) (y := swap a b * swap c d) fun σ hσ => by
      rcases hB σ hσ with h | h | h | h
      · exact Or.inl h
      · exact absurd (h ▸ hσ) hx
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    omega
  · by_contra hx
    have := card_le_three (B := B) (x := swap a b) (y := swap a b * swap c d) fun σ hσ => by
      rcases hB σ hσ with h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd (h ▸ hσ) hx
      · exact Or.inr (Or.inr h)
    omega

theorem card_mul_card_fixSet_le {a b c d : Fin 5}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (B : Subgroup (Perm (Fin 5)))
    (hB : ∀ σ ∈ B, σ = 1 ∨ σ = swap a b ∨ σ = swap c d ∨ σ = swap a b * swap c d)
    (hQ : Nat.card ↥B ∣ 4) : Nat.card ↥B * Nat.card (FixSet (B : Set (Perm (Fin 5)))) ≤ 16 := by
  have h4' : Nat.card ↥B ∣ 2 ^ 2 := by simpa using hQ
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h4'
  interval_cases k
  · rw [hk']
    simpa using card_fixSet_le_sixteen (B : Set (Perm (Fin 5)))
  · have h2 : Nat.card ↥B = 2 := by simpa using hk'
    have hne : B ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at h2
      omega
    obtain ⟨σ, hσ1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    have hσ : σ.1 = swap a b ∨ σ.1 = swap c d ∨ σ.1 = swap a b * swap c d := by
      rcases hB σ.1 σ.2 with h | h | h | h
      · exact absurd (Subtype.ext h) hσ1
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    have h8 : Nat.card (FixSet (B : Set (Perm (Fin 5)))) ≤ 8 := by
      rcases hσ with h | h | h
      · exact card_fixSet_le_of_swap hab (h ▸ σ.2)
      · exact card_fixSet_le_of_swap hcd (h ▸ σ.2)
      · exact card_fixSet_le_of_swap_mul hab hac hbc hbd (h ▸ σ.2)
    rw [h2]
    omega
  · have h4 : Nat.card ↥B = 4 := by simpa using hk'
    obtain ⟨hs₁, hs₂⟩ := swaps_mem_of_card_eq_four B hB h4
    have := card_fixSet_le_four hab hac had hbc hbd hcd hs₁ hs₂
    rw [h4]
    omega

theorem four_distinct : ∀ a b c d : Fin 5, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    swap a b ≠ 1 ∧ swap c d ≠ 1 ∧ swap a b * swap c d ≠ 1 ∧ swap a b ≠ swap c d ∧
      swap a b ≠ swap a b * swap c d ∧ swap c d ≠ swap a b * swap c d := by decide +kernel

theorem mem_four_iff {a b c d : Fin 5} (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c)
    (hbd : b ≠ d) (hcd : c ≠ d) (Q : Subgroup (Perm (Fin 5))) (hQ4 : Nat.card ↥Q = 4)
    (h₁ : swap a b ∈ Q) (h₂ : swap c d ∈ Q) (σ : Perm (Fin 5)) :
    σ ∈ Q ↔ σ = 1 ∨ σ = swap a b ∨ σ = swap c d ∨ σ = swap a b * swap c d := by
  classical
  have hm₃ : swap a b * swap c d ∈ Q := Q.mul_mem h₁ h₂
  constructor
  · intro hσ
    by_contra hne
    push Not at hne
    obtain ⟨hn1, hn2, hn3, hn4⟩ := hne
    obtain ⟨d1, d2, d3, d4, d5, d6⟩ := four_distinct a b c d hab hac had hbc hbd hcd
    have hsub : ({σ, swap a b * swap c d, swap c d, swap a b, 1} : Set (Perm (Fin 5))) ⊆ Q := by
      intro x hx
      rcases hx with rfl | rfl | rfl | rfl | rfl
      · exact hσ
      · exact hm₃
      · exact h₂
      · exact h₁
      · exact Q.one_mem
    have n1 : σ ∉ ({swap a b * swap c d, swap c d, swap a b, 1} : Set (Perm (Fin 5))) := by
      simp [hn1, hn2, hn3, hn4]
    have n2 : swap a b * swap c d ∉ ({swap c d, swap a b, 1} : Set (Perm (Fin 5))) := by
      simp [d6.symm, d5.symm, d3]
    have n3 : swap c d ∉ ({swap a b, 1} : Set (Perm (Fin 5))) := by
      simp [d4.symm, d2]
    have n4 : swap a b ∉ ({1} : Set (Perm (Fin 5))) := by
      simp [d1]
    have hcard : ({σ, swap a b * swap c d, swap c d, swap a b, 1} : Set (Perm (Fin 5))).ncard = 5 := by
      rw [Set.ncard_insert_of_notMem n1, Set.ncard_insert_of_notMem n2,
        Set.ncard_insert_of_notMem n3, Set.ncard_insert_of_notMem n4, Set.ncard_singleton]
    have h5 : Nat.card ↥Q = Set.ncard (Q : Set (Perm (Fin 5))) := (Nat.card_coe_set_eq _).symm
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    omega
  · rintro (rfl | rfl | rfl | rfl)
    · exact Q.one_mem
    · exact h₁
    · exact h₂
    · exact hm₃

theorem exists_even_perm (i j : Fin 5) :
    ∃ σ : Perm (Fin 5), σ ∈ alternatingGroup (Fin 5) ∧ σ⁻¹ i = j := by
  by_cases hij : i = j
  · exact ⟨1, Subgroup.one_mem _, by simp [hij]⟩
  · obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 5, k ≠ i ∧ k ≠ j :=
      (by decide : ∀ i j : Fin 5, ∃ k : Fin 5, k ≠ i ∧ k ≠ j) i j
    refine ⟨swap j k * swap i j, ?_, ?_⟩
    · rw [Perm.mem_alternatingGroup, Perm.sign_mul, sign_swap hkj.symm, sign_swap hij]
      decide
    · rw [mul_inv_rev, swap_inv, swap_inv, Perm.mul_apply,
        swap_apply_of_ne_of_ne hij hki.symm, swap_apply_left]

theorem eq_zero_of_fixed_alt {f : Fin 5 → ZMod 2} (hf : Ev f)
    (h : ∀ σ ∈ alternatingGroup (Fin 5), Fixed σ f) : f = 0 := by
  have hconst : ∀ i, f i = f 0 := fun i => by
    obtain ⟨σ, hσ, hσi⟩ := exists_even_perm i 0
    have := h σ hσ i
    rw [hσi] at this
    exact this.symm
  have h0 : f 0 = 0 := by
    have e : f 0 + f 1 + f 2 + f 3 + f 4 = f 0 + f 0 + f 0 + f 0 + f 0 := by
      rw [hconst 1, hconst 2, hconst 3, hconst 4]
    unfold Ev at hf
    rw [e] at hf
    exact (by decide : ∀ x : ZMod 2, x + x + x + x + x = 0 → x = 0) _ hf
  funext i
  rw [hconst i, h0]
  rfl

end CFSG.Quasithin.LRed10
