module

public import CFSG.LocalAnalysis.WeakClosure81.FiveSixPart

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Equiv

theorem fusionIsSylowIn_of_isSylowIn_two {G : Type*} [Group G] [Finite G] {S H : Subgroup G}
    (h : IsSylowIn 2 S H) : fusionIsSylowIn 2 S H := by
  refine ⟨h.1, h.2.1, fun P hPH hP hSP => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hm := Subgroup.relIndex_mul_relIndex S P H hSP hPH
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hdvd : S.relIndex P ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card (S.subgroupOf P)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases j with _ | j
  · rw [pow_zero] at hj
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hj) hSP
  · exfalso
    apply h.2.2
    rw [← hm, hj, pow_succ]
    exact Dvd.dvd.mul_right (Dvd.intro_left _ rfl) _

theorem b5_FiveSixOrbit_exists_mem_ne_ne_of_three_le_ncard {α : Type*} {s : Set α} {a b : α}
    (h : 3 ≤ s.ncard) (hab : a ≠ b) : ∃ x ∈ s, x ≠ a ∧ x ≠ b := by
  by_contra hx
  have hsub : s ⊆ {a, b} := by
    intro x hxs
    by_contra hxab
    exact hx ⟨x, hxs, fun hxa => hxab (by simp [hxa]), fun hxb => hxab (by simp [hxb])⟩
  have hle : s.ncard ≤ 2 := by
    calc s.ncard ≤ ({a, b} : Set α).ncard := Set.ncard_le_ncard hsub
      _ = 2 := Set.ncard_pair hab
  omega

theorem exists_goodPart {n : ℕ} (hn : 4 < n) {S : Subgroup (Perm (Fin n))}
    (hS : IsSylowIn 2 S ⊤) :
    ∃ Γ : Set (Fin n), S ≤ partStab Γ ∧ Γᶜ.Nonempty ∧ (∃ j : ℕ, Γ.ncard = 2 ^ j) ∧
      ∃ a b c : Fin n, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ swap a b ∈ S ∧ a ∈ Γ ∧ b ∈ Γ ∧ c ∈ Γ := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, hsw, s, hs, hsa⟩ :=
    exists_swap_mem_isSylowIn (S := S) (by omega) hS
  let O : Set (Fin n) := MulAction.orbit ↥S a
  by_cases hO : O = Set.univ
  ·
    obtain ⟨m, hm⟩ := hS.2.1.card_orbit a
    have hn2 : n = 2 ^ m := by
      have h1 : (Set.univ : Set (Fin n)).ncard = Nat.card (Fin n) := Set.ncard_univ (Fin n)
      rw [← Fintype.card_fin n, ← Nat.card_eq_fintype_card, ← h1, ← hO,
        ← Nat.card_coe_set_eq O]
      exact hm
    have hm3 : 3 ≤ m := by
      by_contra h
      have h2 : m ≤ 2 := by omega
      have hle : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num : 0 < 2) h2
      norm_num at hle
      omega
    have hm2 : 2 ≤ m := by omega
    have hpow2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
      nth_rewrite 1 [show m = (m - 1) + 1 by omega]
      rw [pow_succ']
    have hcardFin : Fintype.card (Fin n) = 2 ^ m := by rw [Fintype.card_fin, hn2]
    have hfus : fusionIsSylowIn 2 S ⊤ := fusionIsSylowIn_of_isSylowIn_two hS
    obtain ⟨H₁, hcardH, hpres, -⟩ :=
      CFSG.Holt.H78.exists_half_system_of_fusionIsSylowIn_top (X := Fin n) hfus hm2 hcardFin
    have hkH : Nat.card H₁ = 2 ^ (m - 1) := by
      rw [hpow2] at hcardH
      omega
    have hH₁ncard : H₁.ncard = 2 ^ (m - 1) := by
      rw [← Nat.card_coe_set_eq H₁]
      exact hkH
    have hH₁cncard : H₁ᶜ.ncard = 2 ^ (m - 1) :=
      Set.ncard_compl_of_ncard_eq_add H₁ (by
        have e1 : Nat.card (Fin n) = n := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]
        have e3 : 2 ^ m = 2 ^ (m - 1) + 2 ^ (m - 1) := by
          rw [hpow2]
          ring
        omega)
    have hH₁three : 3 ≤ H₁.ncard := by
      rw [hH₁ncard]
      have h2 : 2 ^ 2 ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      norm_num at h2
      omega
    have hH₁cthree : 3 ≤ H₁ᶜ.ncard := by
      rw [hH₁cncard]
      have h2 : 2 ^ 2 ≤ 2 ^ (m - 1) :=
        Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      norm_num at h2
      omega
    have hH₁ne : H₁.Nonempty := by
      rw [← Set.ncard_pos, hH₁ncard]
      positivity
    have hH₁cne : H₁ᶜ.Nonempty := by
      rw [← Set.ncard_pos, hH₁cncard]
      positivity
    have hSleH : S ≤ partStab H₁ := fun p hp => mem_partStab.mpr (hpres p hp)
    have hswPres : ∀ x, swap a b x ∈ H₁ ↔ x ∈ H₁ := by
      rcases hpres (swap a b) hsw with h | h
      · exact h
      · exfalso
        obtain ⟨x, hxH, hxa, hxb⟩ := b5_FiveSixOrbit_exists_mem_ne_ne_of_three_le_ncard hH₁three hab
        have hx : swap a b x = x := Equiv.swap_apply_of_ne_of_ne hxa hxb
        have hmem : swap a b x ∈ H₁ := by rwa [hx]
        exact (h x).mp hmem hxH
    let Γ : Set (Fin n) := if a ∈ H₁ then H₁ else H₁ᶜ
    have haΓ : a ∈ Γ := by
      dsimp only [Γ]
      split_ifs with haH
      · exact haH
      · exact haH
    have hSleΓ : S ≤ partStab Γ := by
      dsimp only [Γ]
      split_ifs with haH
      · exact hSleH
      · rw [partStab_compl]
        exact hSleH
    have hΓcne : Γᶜ.Nonempty := by
      dsimp only [Γ]
      split_ifs with haH
      · exact hH₁cne
      · simpa only [compl_compl] using hH₁ne
    have hΓpow : ∃ j : ℕ, Γ.ncard = 2 ^ j := by
      dsimp only [Γ]
      split_ifs with haH
      · exact ⟨m - 1, hH₁ncard⟩
      · exact ⟨m - 1, hH₁cncard⟩
    have hΓthree : 3 ≤ Γ.ncard := by
      dsimp only [Γ]
      split_ifs with haH
      · exact hH₁three
      · exact hH₁cthree
    have hpresΓ : ∀ x, swap a b x ∈ Γ ↔ x ∈ Γ := by
      dsimp only [Γ]
      split_ifs with haH
      · exact hswPres
      · intro x
        exact not_congr (hswPres x)
    have hbΓ : b ∈ Γ := by
      have h := (hpresΓ a).mpr haΓ
      rwa [Equiv.swap_apply_left] at h
    obtain ⟨c', hc'Γ, hc'a, hc'b⟩ := b5_FiveSixOrbit_exists_mem_ne_ne_of_three_le_ncard hΓthree hab
    exact ⟨Γ, hSleΓ, hΓcne, hΓpow, a, b, c', hab, Ne.symm hc'a, Ne.symm hc'b, hsw, haΓ,
      hbΓ, hc'Γ⟩
  ·
    have hSleO : S ≤ partStab O := by
      intro g hg
      rw [mem_partStab]
      left
      intro x
      constructor
      · intro hx
        have hgx : (⟨g, hg⟩ : ↥S) • x ∈ O := by
          simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using hx
        have h1 : (⟨g, hg⟩ : ↥S)⁻¹ • ((⟨g, hg⟩ : ↥S) • x) ∈ O :=
          MulAction.mapsTo_smul_orbit (⟨g, hg⟩ : ↥S)⁻¹ a hgx
        simpa only [inv_smul_smul] using h1
      · intro hx
        have h1 : (⟨g, hg⟩ : ↥S) • x ∈ O :=
          MulAction.mapsTo_smul_orbit (⟨g, hg⟩ : ↥S) a hx
        simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using h1
    have hOcne : Oᶜ.Nonempty := Set.nonempty_compl.mpr hO
    have hOpow : ∃ j : ℕ, O.ncard = 2 ^ j := by
      obtain ⟨j, hj⟩ := hS.2.1.card_orbit a
      exact ⟨j, by rw [← Nat.card_coe_set_eq O]; exact hj⟩
    have haO : a ∈ O := MulAction.mem_orbit_self a
    have hbO : b ∈ O := by
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨swap a b, hsw⟩, by
        simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def]
          using Equiv.swap_apply_left a b⟩
    have hcO : c ∈ O := by
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨s, hs⟩, by
        simpa only [MulAction.subgroup_smul_def, Equiv.Perm.smul_def] using hsa⟩
    exact ⟨O, hSleO, hOcne, hOpow, a, b, c, hab, hac, hbc, hsw, haO, hbO, hcO⟩

end CFSG.LocalAnalysis.WeakClosure81
