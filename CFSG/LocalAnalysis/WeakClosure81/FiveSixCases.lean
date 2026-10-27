module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSixNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Equiv

theorem exists_cyc3_mem_partStab_of_mem {α : Type*} [DecidableEq α] {Γ : Set α} {α₀ : α}
    (hα : α₀ ∈ Γ) (h3 : 3 ≤ Γ.ncard) :
    ∃ x y z : α, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ cyc3 x y z ∈ partStab Γ ∧ cyc3 x y z α₀ ≠ α₀ := by
  have hfin : Γ.Finite := Set.finite_of_ncard_pos (by omega)
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ := (Set.two_lt_ncard_iff hfin).1 (by omega)
  by_cases h : α₀ = a ∨ α₀ = b ∨ α₀ = c
  · refine ⟨a, b, c, hab, hac, hbc, cyc3_mem_partStab_of_mem ha hb hc, ?_⟩
    rcases h with rfl | rfl | rfl
    · rw [cyc3_apply_left hab hac hbc]; exact hab.symm
    · rw [cyc3_apply_middle hab hac hbc]; exact hbc.symm
    · rw [cyc3_apply_right hab hac hbc]; exact hac
  · obtain ⟨h1, h2, -⟩ : α₀ ≠ a ∧ α₀ ≠ b ∧ α₀ ≠ c := by simpa [not_or] using h
    refine ⟨α₀, a, b, h1, h2, hab, cyc3_mem_partStab_of_mem hα ha hb, ?_⟩
    rw [cyc3_apply_left h1 h2 hab]
    exact h1.symm

theorem seven_le_of_nonempty_mulEquiv_alternatingGroup {n k : ℕ} (hk : 7 ≤ k)
    {K : Subgroup (Perm (Fin n))} (e : Nonempty (↥K ≃* alternatingGroup (Fin k))) : 7 ≤ n := by
  obtain ⟨e⟩ := e
  by_contra hn
  have hk1 : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.2 (by omega)
  have h1 : 2 * Nat.card K = k.factorial := by
    rw [Nat.card_congr e.toEquiv, two_mul_nat_card_alternatingGroup, Nat.card_perm,
      Nat.card_fin]
  have h2 : Nat.card K ∣ n.factorial := by
    have := Subgroup.card_subgroup_dvd_card K
    rwa [Nat.card_perm, Nat.card_fin] at this
  have h3 : n.factorial ≤ 720 := (Nat.factorial_le (by omega : n ≤ 6)).trans (by decide)
  have h4 : 5040 ≤ k.factorial := le_trans (by decide) (Nat.factorial_le hk)
  have h5 := Nat.le_of_dvd (Nat.factorial_pos n) h2
  omega

theorem exists_cyc3_mem_partStab_of_notMem {α : Type*} [DecidableEq α] {Γ : Set α} {α₀ : α}
    (hα : α₀ ∉ Γ) (h3 : 3 ≤ Γᶜ.ncard) :
    ∃ x y z : α, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ cyc3 x y z ∈ partStab Γ ∧ cyc3 x y z α₀ ≠ α₀ := by
  simpa only [partStab_compl] using exists_cyc3_mem_partStab_of_mem (Γ := Γᶜ) hα h3

theorem three_le_and_three_le_or_six_le {g c n : ℕ} (hg : 3 ≤ g) (hpow : ∃ j : ℕ, g = 2 ^ j)
    (hgc : g + c = n) (hn : 7 ≤ n) : (3 ≤ g ∧ 3 ≤ c) ∨ 6 ≤ g ∨ 6 ≤ c := by
  obtain ⟨j, rfl⟩ := hpow
  rcases Nat.lt_or_ge c 3 with hc | hc
  · right; left
    rcases Nat.lt_or_ge j 3 with hj | hj
    · interval_cases j <;> omega
    · calc 6 ≤ 2 ^ 3 := by norm_num
        _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  · exact Or.inl ⟨hg, hc⟩

theorem false_of_not_nine_dvd {n : ℕ} (hn : 7 ≤ n) {K M : Subgroup (Perm (Fin n))}
    (hA : alternatingGroup (Fin n) ≤ K) {Γ : Set (Fin n)} (hM : K ⊓ partStab Γ ≤ M)
    (h3 : 3 ≤ Γ.ncard) (hpow : ∃ j : ℕ, Γ.ncard = 2 ^ j) (h9 : ¬ 9 ∣ Nat.card M) : False := by
  have hsum : Γ.ncard + Γᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨P, hP9, hPA, hPΓ⟩ :=
    exists_card_nine_le (three_le_and_three_le_or_six_le h3 hpow hsum hn)
  have hPM : P ≤ M := fun x hx => hM ⟨hA (hPA hx), hPΓ hx⟩
  exact h9 (hP9 ▸ Subgroup.card_dvd_of_le hPM)

theorem exists_two_pow_add_one_of_stabilizer {n : ℕ} {K M : Subgroup (Perm (Fin n))}
    (hA : alternatingGroup (Fin n) ≤ K) {Γ : Set (Fin n)} (hM : K ⊓ partStab Γ ≤ M) {α : Fin n}
    (hα : M ≤ MulAction.stabilizer (Perm (Fin n)) α) (h3 : 3 ≤ Γ.ncard)
    (hpow : ∃ j : ℕ, Γ.ncard = 2 ^ j) (hodd : Odd n) : ∃ m : ℕ, n = 2 ^ m + 1 := by
  have key : ∀ x y z : Fin n, x ≠ y → y ≠ z → cyc3 x y z ∈ partStab Γ → cyc3 x y z α = α := by
    intro x y z hxy hyz hmem
    have hK : cyc3 x y z ∈ K := hA (cyc3_mem_alternatingGroup hxy hyz)
    simpa [MulAction.mem_stabilizer_iff] using hα (hM ⟨hK, hmem⟩)
  have hαΓ : α ∉ Γ := fun h => by
    obtain ⟨x, y, z, hxy, -, hyz, hmem, hne⟩ := exists_cyc3_mem_partStab_of_mem h h3
    exact hne (key x y z hxy hyz hmem)
  have hc2 : Γᶜ.ncard ≤ 2 := by
    by_contra hc
    obtain ⟨x, y, z, hxy, -, hyz, hmem, hne⟩ :=
      exists_cyc3_mem_partStab_of_notMem hαΓ (not_le.1 hc)
    exact hne (key x y z hxy hyz hmem)
  have hc1 : 0 < Γᶜ.ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨α, hαΓ⟩
  have hsum : Γ.ncard + Γᶜ.ncard = n := by
    rw [Set.ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]
  obtain ⟨j, hj⟩ := hpow
  have hj0 : j ≠ 0 := by
    rintro rfl
    omega
  obtain ⟨s, hs⟩ : 2 ∣ Γ.ncard := hj ▸ dvd_pow_self 2 hj0
  obtain ⟨r, hr⟩ := hodd
  exact ⟨j, by omega⟩

end CFSG.LocalAnalysis.WeakClosure81
