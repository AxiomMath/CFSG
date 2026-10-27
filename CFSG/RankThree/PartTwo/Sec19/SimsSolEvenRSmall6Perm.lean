module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmallPerm

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall (PresPair)

@[expose] def sig1 (π : Perm (Fin 6)) : Perm (Fin 6) := swap (π 0) (π 1) * swap (π 2) (π 3)

@[expose] def sig2 (π : Perm (Fin 6)) : Perm (Fin 6) := swap (π 0) (π 1) * swap (π 4) (π 5)

@[expose] def sig3 (π : Perm (Fin 6)) : Perm (Fin 6) := swap (π 2) (π 3) * swap (π 4) (π 5)

@[expose] def InP (π σ : Perm (Fin 6)) : Prop := σ = 1 ∨ σ = sig1 π ∨ σ = sig2 π ∨ σ = sig3 π

local instance (π σ : Perm (Fin 6)) : Decidable (InP π σ) :=
  inferInstanceAs (Decidable (σ = 1 ∨ σ = sig1 π ∨ σ = sig2 π ∨ σ = sig3 π))

local instance (σ : Perm (Fin 6)) (i j : Fin 6) : Decidable (PresPair σ i j) :=
  inferInstanceAs (Decidable ((σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)))

private theorem eq_conj_iff (π a b : Perm (Fin 6)) : a = π * b * π⁻¹ ↔ π⁻¹ * a * π = b := by
  constructor
  · rintro rfl
    group
  · rintro rfl
    group

theorem sig1_eq (π : Perm (Fin 6)) : sig1 π = π * sig1 1 * π⁻¹ := by
  unfold sig1
  rw [swap_apply_apply π 0 1, swap_apply_apply π 2 3]
  simp [mul_assoc]

theorem sig2_eq (π : Perm (Fin 6)) : sig2 π = π * sig2 1 * π⁻¹ := by
  unfold sig2
  rw [swap_apply_apply π 0 1, swap_apply_apply π 4 5]
  simp [mul_assoc]

theorem sig3_eq (π : Perm (Fin 6)) : sig3 π = π * sig3 1 * π⁻¹ := by
  unfold sig3
  rw [swap_apply_apply π 2 3, swap_apply_apply π 4 5]
  simp [mul_assoc]

theorem inP_conj (π σ : Perm (Fin 6)) : InP π σ ↔ InP 1 (π⁻¹ * σ * π) := by
  have e : ∀ b : Perm (Fin 6), σ = π * b * π⁻¹ ↔ π⁻¹ * σ * π = b := fun b => eq_conj_iff π σ b
  have e1 : σ = 1 ↔ π⁻¹ * σ * π = 1 := by
    rw [← e 1]
    simp
  unfold InP
  rw [sig1_eq π, sig2_eq π, sig3_eq π, e1, e (sig1 1), e (sig2 1), e (sig3 1)]

theorem presPair_conj (ρ σ : Perm (Fin 6)) (i j : Fin 6) :
    PresPair (ρ * σ * ρ⁻¹) (ρ i) (ρ j) ↔ PresPair σ i j := by
  unfold PresPair
  simp only [Perm.mul_apply, Perm.inv_def, Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]

private theorem conj_sig1 (π : Perm (Fin 6)) : π⁻¹ * sig1 π * π = sig1 1 :=
  (eq_conj_iff π (sig1 π) (sig1 1)).1 (sig1_eq π)

private theorem conj_sig2 (π : Perm (Fin 6)) : π⁻¹ * sig2 π * π = sig2 1 :=
  (eq_conj_iff π (sig2 π) (sig2 1)).1 (sig2_eq π)

private theorem eq_of_conj_eq {π a b : Perm (Fin 6)} (h : π⁻¹ * a * π = b) :
    a = π * b * π⁻¹ :=
  (eq_conj_iff π a b).2 h

private theorem conj_mul_comm {π a b : Perm (Fin 6)} (h : a * b = b * a) :
    (π⁻¹ * a * π) * (π⁻¹ * b * π) = (π⁻¹ * b * π) * (π⁻¹ * a * π) :=
  calc (π⁻¹ * a * π) * (π⁻¹ * b * π) = π⁻¹ * (a * b) * π := by group
    _ = π⁻¹ * (b * a) * π := by rw [h]
    _ = (π⁻¹ * b * π) * (π⁻¹ * a * π) := by group

private theorem conj_ne_one {π τ : Perm (Fin 6)} (h : τ ≠ 1) : π⁻¹ * τ * π ≠ 1 := fun h' =>
  h (calc τ = π * (π⁻¹ * τ * π) * π⁻¹ := by group
    _ = 1 := by rw [h']; group)

private theorem conj_pow_eq_one {π τ : Perm (Fin 6)} {m : ℕ} (h : τ ^ m = 1) :
    (π⁻¹ * τ * π) ^ m = 1 := by
  have := conj_pow (a := π⁻¹) (b := τ) (i := m)
  rw [inv_inv] at this
  rw [this, h]
  group

private theorem pow_eq_one_of_conj {π τ : Perm (Fin 6)} {m : ℕ} (h : (π⁻¹ * τ * π) ^ m = 1) :
    τ ^ m = 1 := by
  have := conj_pow (a := π) (b := π⁻¹ * τ * π) (i := m)
  rw [show π * (π⁻¹ * τ * π) * π⁻¹ = τ by group, h] at this
  rw [this]
  group

private theorem normalizes_conj {π τ : Perm (Fin 6)} (h1 : InP π (τ * sig1 π * τ⁻¹))
    (h2 : InP π (τ * sig2 π * τ⁻¹)) :
    InP 1 ((π⁻¹ * τ * π) * sig1 1 * (π⁻¹ * τ * π)⁻¹) ∧
      InP 1 ((π⁻¹ * τ * π) * sig2 1 * (π⁻¹ * τ * π)⁻¹) := by
  have key : ∀ s : Perm (Fin 6), (π⁻¹ * τ * π) * (π⁻¹ * s * π) * (π⁻¹ * τ * π)⁻¹ =
      π⁻¹ * (τ * s * τ⁻¹) * π := fun s => by group
  rw [← conj_sig1 π, ← conj_sig2 π, key, key]
  exact ⟨(inP_conj π _).1 h1, (inP_conj π _).1 h2⟩

private theorem fin_pow_four : ∀ τ : Perm (Fin 6), τ * sig1 1 = sig1 1 * τ → τ ^ 4 = 1 := by
  decide +kernel

private theorem fin_canonical : sig1 1 * swap 4 5 * (sig1 1 * swap 4 5) = 1 ∧
    sig1 1 * (sig1 1 * swap 4 5) ≠ 1 := by
  decide +kernel

private theorem fin_c1 : ∀ τ : Perm (Fin 6), τ ≠ 1 → τ ≠ swap 0 1 →
    ¬ ∀ i j : Fin 6, i ≠ j → (PresPair τ i j ↔ PresPair (swap 0 1) i j) := by
  decide +kernel

private theorem fin_c2a : ∀ τ : Perm (Fin 6), τ ≠ 1 →
    (∀ i j : Fin 6, i ≠ j → (PresPair τ i j ↔ PresPair (sig1 1) i j)) →
    InP 1 τ ∨ τ = sig1 1 * swap 4 5 := by
  decide +kernel

private theorem fin_c2b : ¬ ∀ i j : Fin 6, i ≠ j →
    (PresPair (sig1 1 * (sig1 1 * swap 4 5)) i j ↔ PresPair (sig1 1) i j) := by
  decide +kernel

private theorem fin_c3 : ∀ τ : Perm (Fin 6), τ ≠ 1 → τ ≠ sig1 1 * swap 4 5 →
    (∀ i j : Fin 6, i ≠ j → (PresPair τ i j ↔ PresPair (sig1 1 * swap 4 5) i j)) →
    ¬ ∀ i j : Fin 6, i ≠ j →
      (PresPair ((sig1 1 * swap 4 5) * τ) i j ↔ PresPair (sig1 1 * swap 4 5) i j) := by
  decide +kernel

private theorem fin_card : ∀ τ : Perm (Fin 6), τ ^ 3 = 1 → τ ≠ 1 → InP 1 (τ * sig1 1 * τ⁻¹) →
    InP 1 (τ * sig2 1 * τ⁻¹) → ∀ ρ : Perm (Fin 6), ρ * sig1 1 = sig1 1 * ρ →
      ρ * sig2 1 = sig2 1 * ρ → ρ * τ = τ * ρ → ρ = 1 ∨ ρ = sig1 1 * swap 4 5 := by
  decide +kernel

private theorem fin_vec : ∀ τ : Perm (Fin 6), τ ^ 3 = 1 → τ ≠ 1 → InP 1 (τ * sig1 1 * τ⁻¹) →
    InP 1 (τ * sig2 1 * τ⁻¹) → ∀ x : Fin 6 → ZMod 2,
      (-vecPerm (sig1 1) x + x = 0 ∨ -vecPerm (sig1 1) x + x = allOnes 6) →
      (-vecPerm (sig2 1) x + x = 0 ∨ -vecPerm (sig2 1) x + x = allOnes 6) →
      (-vecPerm τ x + x = 0 ∨ -vecPerm τ x + x = allOnes 6) → x = 0 ∨ x = allOnes 6 := by
  decide +kernel

private theorem fin_inP : ∀ σ : Perm (Fin 6), InP 1 σ → PresPair σ 0 1 ∧ PresPair σ 2 3 := by
  rintro σ (rfl | rfl | rfl | rfl) <;> decide +kernel

private theorem cycleType_eq_replicate {σ : Perm (Fin 6)} (hσ : σ * σ = 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have h := cycleType_of_pow_prime_eq_one (p := 2) (by rw [pow_two]; exact hσ)
  have hs : σ.support.card = Multiset.card σ.cycleType * 2 := by
    rw [← sum_cycleType, h]
    simp
  rw [hs, Nat.mul_div_cancel _ two_pos]
  exact h

private theorem exists_conj_of_card_support {σ τ : Perm (Fin 6)} (hσ : σ * σ = 1)
    (hτ : τ * τ = 1) (h : σ.support.card = τ.support.card) :
    ∃ ρ : Perm (Fin 6), ρ⁻¹ * σ * ρ = τ := by
  have hc : IsConj σ τ :=
    isConj_iff_cycleType_eq.2 (by rw [cycleType_eq_replicate hσ, cycleType_eq_replicate hτ, h])
  obtain ⟨c, hc⟩ := isConj_iff.1 hc
  exact ⟨c⁻¹, by simpa using hc⟩

private theorem exists_conj_canonical {σ : Perm (Fin 6)} (h2 : σ * σ = 1) (h1 : σ ≠ 1) :
    ∃ ρ : Perm (Fin 6), ρ⁻¹ * σ * ρ = swap 0 1 ∨ ρ⁻¹ * σ * ρ = sig1 1 ∨
      ρ⁻¹ * σ * ρ = sig1 1 * swap 4 5 := by
  have hle : σ.support.card ≤ 6 := by simpa using Finset.card_le_univ σ.support
  have hpos : σ.support.card ≠ 0 := fun h => h1 (card_support_eq_zero.1 h)
  have hev : 2 ∣ σ.support.card := two_dvd_card_support (by rw [pow_two]; exact h2)
  have hs1 : swap (0 : Fin 6) 1 * swap 0 1 = 1 := swap_mul_self _ _
  have hs2 : sig1 1 * sig1 1 = 1 := by unfold sig1; decide
  have hs3 : sig1 1 * swap 4 5 * (sig1 1 * swap 4 5) = 1 := fin_canonical.1
  have hc1 : (swap (0 : Fin 6) 1).support.card = 2 := by decide
  have hc2 : (sig1 1).support.card = 4 := by unfold sig1; decide
  have hc3 : (sig1 1 * swap 4 5).support.card = 6 := by unfold sig1; decide
  obtain ⟨k, hk⟩ := hev
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hk' with rfl | rfl | rfl
  · obtain ⟨ρ, hρ⟩ := exists_conj_of_card_support h2 hs1 (by rw [hc1]; omega)
    exact ⟨ρ, Or.inl hρ⟩
  · obtain ⟨ρ, hρ⟩ := exists_conj_of_card_support h2 hs2 (by rw [hc2]; omega)
    exact ⟨ρ, Or.inr (Or.inl hρ)⟩
  · obtain ⟨ρ, hρ⟩ := exists_conj_of_card_support h2 hs3 (by rw [hc3]; omega)
    exact ⟨ρ, Or.inr (Or.inr hρ)⟩

theorem pow_four_eq_one_of_commute (π : Perm (Fin 6)) {τ : Perm (Fin 6)}
    (h : τ * sig1 π = sig1 π * τ) : τ ^ 4 = 1 := by
  have h1 := conj_mul_comm (π := π) h
  rw [conj_sig1] at h1
  exact pow_eq_one_of_conj (fin_pow_four _ h1)

theorem eq_one_of_commute_of_pow_odd (π : Perm (Fin 6)) {τ : Perm (Fin 6)}
    (h : τ * sig1 π = sig1 π * τ) {m : ℕ} (hm : Odd m) (hτ : τ ^ m = 1) : τ = 1 := by
  have h4 := pow_four_eq_one_of_commute π h
  have hcop : Nat.Coprime 4 m := by
    have : Nat.Coprime (2 ^ 2) m := Nat.Coprime.pow_left 2 (Nat.coprime_two_left.2 hm)
    simpa using this
  have hd : orderOf τ ∣ Nat.gcd 4 m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h4) (orderOf_dvd_of_pow_eq_one hτ)
  rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

private theorem inP_of_canonical {P : Subgroup (Perm (Fin 6))} {σ₀ : Perm (Fin 6)}
    (hσ₀ : σ₀ = swap 0 1 ∨ σ₀ = sig1 1 ∨ σ₀ = sig1 1 * swap 4 5) (hσP : σ₀ ∈ P)
    (hpairs : ∀ τ ∈ P, τ ≠ 1 → ∀ i j : Fin 6, i ≠ j → (PresPair τ i j ↔ PresPair σ₀ i j))
    (h3 : ∃ τ ∈ P, τ ≠ 1 ∧ τ ≠ σ₀) : ∀ τ ∈ P, InP 1 τ := by
  rcases hσ₀ with rfl | rfl | rfl
  · exfalso
    obtain ⟨τ, hτ, h1, h2⟩ := h3
    exact fin_c1 τ h1 h2 (hpairs τ hτ h1)
  · intro τ hτ
    by_cases h1 : τ = 1
    · exact Or.inl h1
    rcases fin_c2a τ h1 (hpairs τ hτ h1) with h | rfl
    · exact h
    · exact absurd (hpairs _ (P.mul_mem hσP hτ) fin_canonical.2) fin_c2b
  · exfalso
    obtain ⟨τ, hτ, h1, h2⟩ := h3
    have hne : sig1 1 * swap 4 5 * τ ≠ 1 := fun h =>
      h2 (mul_left_cancel (h.trans fin_canonical.1.symm))
    exact fin_c3 τ h1 h2 (hpairs τ hτ h1) (hpairs _ (P.mul_mem hσP hτ) hne)

theorem exists_pairing_of_presPair {P : Subgroup (Perm (Fin 6))} {σ : Perm (Fin 6)}
    (hσP : σ ∈ P) (hσ1 : σ ≠ 1) (hσ2 : σ * σ = 1)
    (hpairs : ∀ τ ∈ P, τ ≠ 1 → ∀ i j : Fin 6, i ≠ j → (PresPair τ i j ↔ PresPair σ i j))
    (h3 : ∃ τ ∈ P, τ ≠ 1 ∧ τ ≠ σ) :
    ∃ π : Perm (Fin 6), ∀ τ ∈ P, InP π τ := by
  obtain ⟨ρ, hρ⟩ := exists_conj_canonical hσ2 hσ1
  let P' : Subgroup (Perm (Fin 6)) := P.comap (MulAut.conj ρ).toMonoidHom
  have hmem : ∀ x, x ∈ P' ↔ ρ * x * ρ⁻¹ ∈ P := fun x => Iff.rfl
  have hσ : σ = ρ * (ρ⁻¹ * σ * ρ) * ρ⁻¹ := by group
  generalize ρ⁻¹ * σ * ρ = σ₀ at hρ hσ
  have hσ₀P : σ₀ ∈ P' := by
    rw [hmem, ← hσ]
    exact hσP
  have hpairs' : ∀ τ ∈ P', τ ≠ 1 → ∀ i j : Fin 6, i ≠ j →
      (PresPair τ i j ↔ PresPair σ₀ i j) := by
    intro τ hτ hτ1 i j hij
    have h := hpairs (ρ * τ * ρ⁻¹) ((hmem τ).1 hτ) (fun h => hτ1 (by simpa using h)) (ρ i) (ρ j)
      (fun h => hij (ρ.injective h))
    rwa [hσ, presPair_conj, presPair_conj] at h
  have h3' : ∃ τ ∈ P', τ ≠ 1 ∧ τ ≠ σ₀ := by
    obtain ⟨τ, hτ, h1, h2⟩ := h3
    refine ⟨ρ⁻¹ * τ * ρ, (hmem _).2 ?_, conj_ne_one h1, fun h => h2 ?_⟩
    · simpa [mul_assoc] using hτ
    · rw [hσ, ← h]
      group
  have hcore := inP_of_canonical hρ hσ₀P hpairs' h3'
  refine ⟨ρ, fun τ hτ => ?_⟩
  rw [inP_conj]
  exact hcore _ ((hmem _).2 (by simpa [mul_assoc] using hτ))

private theorem natCard_le_of_forall_mem {P : Subgroup (Perm (Fin 6))}
    {F : Finset (Perm (Fin 6))} (h : ∀ τ ∈ P, τ ∈ F) : Nat.card P ≤ F.card := by
  classical
  have hsub : (P : Set (Perm (Fin 6))) ⊆ (F : Set (Perm (Fin 6))) := fun τ hτ => h τ hτ
  calc Nat.card P = (P : Set (Perm (Fin 6))).ncard := by
        rw [← Nat.card_coe_set_eq, SetLike.coe_sort_coe]
    _ ≤ (F : Set (Perm (Fin 6))).ncard := Set.ncard_le_ncard hsub F.finite_toSet
    _ = F.card := Set.ncard_coe_finset F

private theorem natCard_le_three {P : Subgroup (Perm (Fin 6))} {a b : Perm (Fin 6)}
    (h : ∀ τ ∈ P, τ = 1 ∨ τ = a ∨ τ = b) : Nat.card P ≤ 3 := by
  classical
  refine (natCard_le_of_forall_mem (F := {1, a, b}) fun τ hτ => ?_).trans Finset.card_le_three
  simpa using h τ hτ

theorem inP_iff_of_card {π : Perm (Fin 6)} {P : Subgroup (Perm (Fin 6))}
    (hP : ∀ τ ∈ P, InP π τ) (h4 : 4 ≤ Nat.card P) :
    sig1 π ∈ P ∧ sig2 π ∈ P ∧ sig3 π ∈ P := by
  refine ⟨?_, ?_, ?_⟩
  · by_contra hn
    have := natCard_le_three (P := P) (a := sig2 π) (b := sig3 π) fun τ hτ => by
      rcases hP τ hτ with h | rfl | h | h
      · exact Or.inl h
      · exact absurd hτ hn
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    omega
  · by_contra hn
    have := natCard_le_three (P := P) (a := sig1 π) (b := sig3 π) fun τ hτ => by
      rcases hP τ hτ with h | h | rfl | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd hτ hn
      · exact Or.inr (Or.inr h)
    omega
  · by_contra hn
    have := natCard_le_three (P := P) (a := sig1 π) (b := sig2 π) fun τ hτ => by
      rcases hP τ hτ with h | h | h | rfl
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact absurd hτ hn
    omega

theorem card_le_two_of_commute (π : Perm (Fin 6)) {τ : Perm (Fin 6)} (hτ3 : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (h1 : InP π (τ * sig1 π * τ⁻¹)) (h2 : InP π (τ * sig2 π * τ⁻¹))
    {H : Subgroup (Perm (Fin 6))}
    (hH : ∀ ρ ∈ H, ρ * sig1 π = sig1 π * ρ ∧ ρ * sig2 π = sig2 π * ρ ∧ ρ * τ = τ * ρ) :
    Nat.card H ≤ 2 := by
  classical
  obtain ⟨n1, n2⟩ := normalizes_conj h1 h2
  have hmem : ∀ ρ ∈ H, ρ ∈ ({1, π * (sig1 1 * swap 4 5) * π⁻¹} : Finset (Perm (Fin 6))) := by
    intro ρ hρ
    obtain ⟨c1, c2, c3⟩ := hH ρ hρ
    have c1' := conj_mul_comm (π := π) c1
    have c2' := conj_mul_comm (π := π) c2
    have c3' := conj_mul_comm (π := π) c3
    rw [conj_sig1] at c1'
    rw [conj_sig2] at c2'
    rcases fin_card (π⁻¹ * τ * π) (conj_pow_eq_one hτ3) (conj_ne_one hτ1) n1 n2 (π⁻¹ * ρ * π)
      c1' c2' c3' with h | h
    · have hρ1 : ρ = 1 := by
        calc ρ = π * (π⁻¹ * ρ * π) * π⁻¹ := by group
          _ = 1 := by rw [h]; group
      simp [hρ1]
    · simp [eq_of_conj_eq h]
  exact (natCard_le_of_forall_mem hmem).trans Finset.card_le_two

theorem eq_zero_of_fixed (π : Perm (Fin 6)) {τ : Perm (Fin 6)} (hτ3 : τ ^ 3 = 1)
    (hτ1 : τ ≠ 1) (h1 : InP π (τ * sig1 π * τ⁻¹)) (h2 : InP π (τ * sig2 π * τ⁻¹))
    {v : permBar 6} (hv1 : barAct (sig1 π) v = v) (hv2 : barAct (sig2 π) v = v)
    (hvτ : barAct τ v = v) : v = 0 := by
  obtain ⟨n1, n2⟩ := normalizes_conj h1 h2
  have hconj : ∀ σ : Perm (Fin 6), barAct σ v = v →
      barAct (π⁻¹ * σ * π) (barAct π⁻¹ v) = barAct π⁻¹ v := by
    intro σ hσ
    rw [barAct_mul, barAct_mul, ← barAct_mul π π⁻¹, mul_inv_cancel, barAct_one, hσ]
  obtain ⟨x, hx⟩ := QuotientAddGroup.mk_surjective (barAct π⁻¹ v)
  have f1 := hconj _ hv1
  have f2 := hconj _ hv2
  have f3 := hconj _ hvτ
  rw [conj_sig1, ← hx, barAct_mk, QuotientAddGroup.eq, mem_zmultiples_allOnes_iff] at f1
  rw [conj_sig2, ← hx, barAct_mk, QuotientAddGroup.eq, mem_zmultiples_allOnes_iff] at f2
  rw [← hx, barAct_mk, QuotientAddGroup.eq, mem_zmultiples_allOnes_iff] at f3
  have hx0 := fin_vec (π⁻¹ * τ * π) (conj_pow_eq_one hτ3) (conj_ne_one hτ1) n1 n2 x f1 f2 f3
  have hw : barAct π⁻¹ v = 0 := by
    rw [← hx, QuotientAddGroup.eq_zero_iff, mem_zmultiples_allOnes_iff]
    exact hx0
  have := barAct_mul π π⁻¹ v
  rw [mul_inv_cancel, barAct_one, hw, map_zero] at this
  exact this

theorem presPair_of_inP {π σ : Perm (Fin 6)} (h : InP π σ) :
    PresPair σ (π 0) (π 1) ∧ PresPair σ (π 2) (π 3) := by
  have h1 := fin_inP _ ((inP_conj π σ).1 h)
  have e : π * (π⁻¹ * σ * π) * π⁻¹ = σ := by group
  rw [← presPair_conj π _ 0 1, ← presPair_conj π _ 2 3, e] at h1
  exact h1

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
