module

public import CFSG.Assembly.Defs

public section

namespace CFSG.Quasithin.H.A7F

open Equiv

@[expose] def c71 : Perm (Fin 7) := swap 0 1 * swap 0 2

@[expose] def c74 : Perm (Fin 7) := swap 3 4 * swap 3 5

@[expose] def c72 : Perm (Fin 7) := c71 * c74

@[expose] def InKer (σ : Perm (Fin 7)) (x : Fin 7 → ZMod 2) : Prop :=
  ∀ i, x i + x (σ i) + x (σ (σ i)) = 0

instance (σ : Perm (Fin 7)) : DecidablePred (InKer σ) := fun x => by
  unfold InKer; infer_instance

theorem card_ker_c71 :
    (Finset.univ.filter (fun x : Fin 7 → ZMod 2 => ∑ i, x i = 0 ∧ InKer c71 x)).card = 4 := by
  decide +kernel

theorem card_ker_c72 :
    (Finset.univ.filter (fun x : Fin 7 → ZMod 2 => ∑ i, x i = 0 ∧ InKer c72 x)).card = 16 := by
  decide +kernel

theorem mem_ker_c72 : ∀ a ∈ ({(0, 1), (1, 2), (3, 4), (4, 5)} : Finset (Fin 7 × Fin 7)),
    InKer c72 (Pi.single a.1 1 + Pi.single a.2 1) := by
  decide +kernel

theorem c71_isThreeCycle : c71.IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem c74_isThreeCycle : c74.IsThreeCycle :=
  Equiv.Perm.isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

theorem disjoint_c71_c74 : Equiv.Perm.Disjoint c71 c74 := by
  intro x
  fin_cases x <;> decide

theorem cycleType_c72 : c72.cycleType = {3, 3} := by
  rw [c72, Equiv.Perm.Disjoint.cycleType_mul disjoint_c71_c74, c71_isThreeCycle, c74_isThreeCycle]
  rfl

theorem cycleType_of_orderOf_three {σ : Perm (Fin 7)} (h : orderOf σ = 3) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (h ▸ Nat.prime_three)
  rw [h] at hn
  have hsum := Equiv.Perm.sum_cycleType_le σ
  rw [hn, Multiset.sum_replicate, Fintype.card_fin, smul_eq_mul] at hsum
  have hn1 : n ≤ 1 := by omega
  interval_cases n
  · left; rw [hn]; rfl
  · right; rw [hn]; rfl

theorem isConj_c71_or_c72 {σ : Perm (Fin 7)} (h : orderOf σ = 3) :
    IsConj c71 σ ∨ IsConj c72 σ := by
  rcases cycleType_of_orderOf_three h with h1 | h1
  · left
    rw [Equiv.Perm.isConj_iff_cycleType_eq, h1]
    exact c71_isThreeCycle
  · right
    rw [Equiv.Perm.isConj_iff_cycleType_eq, h1, cycleType_c72]

theorem eq_of_fix_pair {σ : Perm (Fin 7)} {a b : Fin 7} (hab : a ≠ b)
    (h : ∀ i, (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) (σ⁻¹ i) =
      (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) i) (j : Fin 7) :
    σ⁻¹ j = a ∨ σ⁻¹ j = b ↔ j = a ∨ j = b := by
  have key : ∀ k : Fin 7, (Pi.single a 1 + Pi.single b 1 : Fin 7 → ZMod 2) k = 1 ↔
      k = a ∨ k = b := by
    intro k
    by_cases hka : k = a
    · subst hka; simp [hab]
    · by_cases hkb : k = b
      · subst hkb; simp [hka]
      · simp [hka, hkb]
  rw [← key, ← key, h j]

theorem eq_one_of_fix_ker_c72 {σ : Perm (Fin 7)}
    (h : ∀ x : Fin 7 → ZMod 2, ∑ i, x i = 0 → InKer c72 x → ∀ i, x (σ⁻¹ i) = x i) : σ = 1 := by
  have hfix : ∀ a ∈ ({(0, 1), (1, 2), (3, 4), (4, 5)} : Finset (Fin 7 × Fin 7)),
      ∀ j, σ⁻¹ j = a.1 ∨ σ⁻¹ j = a.2 ↔ j = a.1 ∨ j = a.2 := by
    intro a ha j
    have hne : a.1 ≠ a.2 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> decide
    refine eq_of_fix_pair hne (h _ ?_ (mem_ker_c72 a ha)) j
    have e : (∑ i, (Pi.single a.1 1 + Pi.single a.2 1 : Fin 7 → ZMod 2) i) = 1 + 1 := by
      simp [Finset.sum_add_distrib]
    rw [e]
    decide
  have h01 := hfix (0, 1) (by decide)
  have h12 := hfix (1, 2) (by decide)
  have h34 := hfix (3, 4) (by decide)
  have h45 := hfix (4, 5) (by decide)
  simp only at h01 h12 h34 h45
  have hinv : σ⁻¹ = 1 := by
    ext j
    fin_cases j
    · rcases (h01 0).mpr (Or.inl rfl) with h | h
      · simp [h]
      · exfalso
        have := (h12 0).mp (Or.inl h)
        simp at this
    · rcases (h01 1).mpr (Or.inr rfl) with h | h
      · exfalso
        have := (h12 1).mpr (Or.inl rfl)
        rw [h] at this
        simp at this
      · simp [h]
    · rcases (h12 2).mpr (Or.inr rfl) with h | h
      · exfalso
        have := (h01 2).mp (Or.inr h)
        simp at this
      · simp [h]
    · rcases (h34 3).mpr (Or.inl rfl) with h | h
      · simp [h]
      · exfalso
        have := (h45 3).mp (Or.inl h)
        simp at this
    · rcases (h34 4).mpr (Or.inr rfl) with h | h
      · exfalso
        have := (h45 4).mpr (Or.inl rfl)
        rw [h] at this
        simp at this
      · simp [h]
    · rcases (h45 5).mpr (Or.inr rfl) with h | h
      · exfalso
        have := (h34 5).mp (Or.inr h)
        simp at this
      · simp [h]
    ·
      have h6 : ∀ k : Fin 7, k ≠ 6 → σ⁻¹ 6 ≠ k := by
        intro k hk h
        fin_cases k
        · have := (h01 6).mp (Or.inl h); simp at this
        · have := (h01 6).mp (Or.inr h); simp at this
        · have := (h12 6).mp (Or.inr h); simp at this
        · have := (h34 6).mp (Or.inl h); simp at this
        · have := (h34 6).mp (Or.inr h); simp at this
        · have := (h45 6).mp (Or.inr h); simp at this
        · exact absurd rfl hk
      have h7 : σ⁻¹ 6 = 6 := by
        by_contra hne
        exact h6 _ hne rfl
      exact congrArg Fin.val h7
  rw [← inv_inv σ, hinv, inv_one]

@[expose] def kerSet (σ : Perm (Fin 7)) : Finset (Fin 7 → ZMod 2) :=
  Finset.univ.filter (fun x : Fin 7 → ZMod 2 => ∑ i, x i = 0 ∧ InKer σ x)

theorem mem_kerSet {σ : Perm (Fin 7)} {x : Fin 7 → ZMod 2} :
    x ∈ kerSet σ ↔ ∑ i, x i = 0 ∧ InKer σ x := by
  simp [kerSet]

theorem inKer_conj (π c : Perm (Fin 7)) (x : Fin 7 → ZMod 2) :
    InKer (π * c * π⁻¹) x ↔ InKer c (fun j => x (π j)) := by
  constructor
  · intro h j
    have := h (π j)
    simpa [Equiv.Perm.mul_apply] using this
  · intro h i
    have := h (π⁻¹ i)
    simpa [Equiv.Perm.mul_apply] using this

theorem comp_mem_kerSet {π c : Perm (Fin 7)} {x : Fin 7 → ZMod 2} (hx : x ∈ kerSet (π * c * π⁻¹)) :
    (fun j => x (π j)) ∈ kerSet c := by
  rw [mem_kerSet] at hx ⊢
  exact ⟨by rw [Equiv.sum_comp π x]; exact hx.1, (inKer_conj π c x).1 hx.2⟩

theorem comp_inv_mem_kerSet {π c : Perm (Fin 7)} {x : Fin 7 → ZMod 2} (hx : x ∈ kerSet c) :
    (fun i => x (π⁻¹ i)) ∈ kerSet (π * c * π⁻¹) := by
  rw [mem_kerSet] at hx ⊢
  refine ⟨by rw [Equiv.sum_comp π⁻¹ x]; exact hx.1, (inKer_conj π c _).2 ?_⟩
  simpa using hx.2

theorem card_kerSet_conj (π c : Perm (Fin 7)) :
    (kerSet (π * c * π⁻¹)).card = (kerSet c).card :=
  Finset.card_bij' (fun x _ => fun j => x (π j)) (fun x _ => fun i => x (π⁻¹ i))
    (fun _ hx => comp_mem_kerSet hx) (fun _ hx => comp_inv_mem_kerSet hx)
    (fun x _ => funext fun i => by simp) (fun x _ => funext fun j => by simp)

theorem eq_one_of_fix_kerSet (π τ : Perm (Fin 7))
    (h : ∀ x ∈ kerSet (π * c72 * π⁻¹), ∀ i, x (τ⁻¹ i) = x i) : τ = 1 := by
  have h1 : π⁻¹ * τ * π = 1 := by
    apply eq_one_of_fix_ker_c72
    intro x hx hk i
    have hx' := comp_inv_mem_kerSet (π := π) (mem_kerSet.mpr ⟨hx, hk⟩)
    have := h _ hx' (π i)
    simpa [Equiv.Perm.mul_apply, mul_inv_rev] using this
  calc τ = π * (π⁻¹ * τ * π) * π⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem orderOf_dvd_420 (σ : Perm (Fin 7)) : orderOf σ ∣ 420 := by
  rw [← Equiv.Perm.lcm_cycleType]
  refine Multiset.lcm_dvd.mpr fun n hn => ?_
  have h2 := Equiv.Perm.two_le_of_mem_cycleType hn
  have h7 : n ≤ 7 := (Equiv.Perm.le_card_support_of_mem_cycleType hn).trans
    ((Finset.card_le_univ _).trans (by simp))
  interval_cases n <;> norm_num

end CFSG.Quasithin.H.A7F
