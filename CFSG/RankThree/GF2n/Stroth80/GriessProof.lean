module

public import CFSG.RankThree.GF2n.Stroth80.GriessOrthSmall
public import CFSG.RankThree.GF2n.Stroth80.GriessOmegaPlusFour
public import CFSG.RankThree.GF2n.Stroth80.GriessSmallClauses
public import CFSG.RankThree.GF2n.Stroth80.GriessSL34
public import CFSG.RankThree.GF2n.Stroth80.Sec311Griess
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatReindex
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Assembly.LowTwoRank

section Clauses

variable {K : Type} [Field K] [Finite K] {E : Type} [Group E] [Finite E]

theorem exists_card_eq_two_pow_of_four_le [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    ∃ f : ℕ, 2 ≤ f ∧ Nat.card K = 2 ^ f := by
  have := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  refine ⟨n, ?_, by rw [Nat.card_eq_fintype_card, hn]⟩
  by_contra hlt
  have : (n : ℕ) = 1 := by have := n.pos; omega
  rw [Nat.card_eq_fintype_card, hn, this] at h4
  omega

theorem statedSL_ker_eq_bot (hGA : GriessAllModelsStatement) {m f : ℕ} (hm : 2 ≤ m)
    (hf : 2 ≤ f) (hK : Nat.card K = 2 ^ f) (h2 : ¬ (m = 2 ∧ f = 2)) (h3 : ¬ (m = 3 ∧ f = 2))
    (hE : Group.IsPerfect E) (π : E →* GL (Fin m) K) (hrange : π.range = StatedSL m K)
    (hker : π.ker ≤ Subgroup.center E) : π.ker = ⊥ := by
  have h := statedSL_ker_card_dvd hGA hm hf hK hE π hrange hker
  rw [exceptionalOrders_psl_eq_one hf h2 h3] at h
  have h1 : Nat.card π.ker ∣ 1 * 1 := h
  exact Subgroup.card_eq_one.mp (Nat.dvd_one.mp h1)

theorem griess_sl_clause (hGA : GriessAllModelsStatement) (h34 : GriessSL34Statement)
    [CharP K 2] (hK4 : 4 ≤ Nat.card K) (hE : Group.IsPerfect E) (Y : Subgroup E)
    (hY : Y ≤ Subgroup.center E) :
    ∀ m : ℕ, 2 ≤ m → ∀ π : E →* GL (Fin m) K, π.range = StatedSL m K → π.ker = Y →
      Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
        (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
          e ∈ Subgroup.normalizer (A : Set E)) →
        Nat.card A < (if Nat.card K = 4 then (if m = 2 then 4 else if m = 3 then 16 else 0)
          else 0) := by
  intro m hm π hrange hker
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_of_four_le hK4
  have hkerY : π.ker ≤ Subgroup.center E := hker ▸ hY
  by_cases h4 : Nat.card K = 4
  · by_cases hm2 : m = 2
    · subst hm2
      have := statedSL_two_four_clause hGA h4 hE π hrange hkerY
      rw [hker] at this
      simpa [h4] using this
    · by_cases hm3 : m = 3
      · subst hm3
        have := h34 K h4 E Y hY hE.1 π hrange hker
        simpa [h4] using this
      · refine Or.inl ?_
        have hf2 : f = 2 := by
          have : (2 : ℕ) ^ f = 2 ^ 2 := by rw [← hK, h4]; norm_num
          exact Nat.pow_right_injective (le_refl 2) this
        have := statedSL_ker_eq_bot hGA hm hf hK (fun h => hm2 h.1) (fun h => hm3 h.1) hE π
          hrange hkerY
        rwa [hker] at this
  · refine Or.inl ?_
    have hf2 : f ≠ 2 := by
      rintro rfl
      exact h4 (by rw [hK]; norm_num)
    have := statedSL_ker_eq_bot hGA hm hf hK (fun h => hf2 h.2) (fun h => hf2 h.2) hE π hrange
      hkerY
    rwa [hker] at this

theorem griess_sp_clause (hGA : GriessAllModelsStatement) (h34 : GriessSL34Statement)
    [CharP K 2] (hK4 : 4 ≤ Nat.card K) (hE : Group.IsPerfect E) (Y : Subgroup E)
    (hY : Y ≤ Subgroup.center E) :
    ∀ m : ℕ, 1 ≤ m → ∀ π : E →* GL (Fin m ⊕ Fin m) K, π.range = StatedSp m K → π.ker = Y →
      Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
        (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
          e ∈ Subgroup.normalizer (A : Set E)) →
        Nat.card A < (if Nat.card K = 4 ∧ m = 1 then 4 else 0) := by
  intro m hm π hrange hker
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_of_four_le hK4
  by_cases hm1 : m = 1
  · subst hm1
    set π' : E →* GL (Fin 2) K := (reindexGL sumFinTwo).toMonoidHom.comp π with hπ'
    have hrange' : π'.range = StatedSL 2 K := by
      rw [hπ', MonoidHom.range_comp, hrange, map_reindexGL_statedSp_one]
    have hker' : π'.ker = Y := by
      exact (MonoidHom.ker_mulEquiv_comp π (reindexGL sumFinTwo)).trans hker
    have := griess_sl_clause hGA h34 hK4 hE Y hY 2 le_rfl π' hrange' hker'
    simpa using this
  · refine Or.inl ?_
    have := statedSp_ker_eq_bot hGA (by omega) hf hK hE π hrange (hker ▸ hY)
    rwa [hker] at this

theorem griess_omegaPlus_clause (hGA : GriessAllModelsStatement) [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) (hE : Group.IsPerfect E) (Y : Subgroup E)
    (hY : Y ≤ Subgroup.center E) :
    ∀ m : ℕ, 2 ≤ m → ∀ π : E →* GL (Fin m ⊕ Fin m) K,
      π.range = StatedOmega (StatedQuadPlus m K) → π.ker = Y →
      Y = ⊥ ∨ ∀ A : Subgroup E, A ⊓ Y = ⊥ → IsElemAbelian 2 A →
        (∀ e ∈ Subgroup.normalizer ((A ⊔ Y : Subgroup E) : Set E),
          e ∈ Subgroup.normalizer (A : Set E)) →
        Nat.card A < (if Nat.card K = 4 ∧ m = 2 then 16 else 0) := by
  intro m hm π hrange hker
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_of_four_le hK4
  have hkerY : π.ker ≤ Subgroup.center E := hker ▸ hY
  by_cases hm2 : m = 2
  · subst hm2
    by_cases hf2 : f = 2
    · have h4 : Nat.card K = 4 := by rw [hK, hf2]; norm_num
      have hexp := statedOmegaPlus_four_ker_exponent hGA hf hK hE π hrange hkerY
      rw [if_pos hf2] at hexp
      have := statedOmega_plus_four_four_clause h4 hE π hrange hkerY hexp
      rw [hker] at this
      simpa [h4] using this
    · refine Or.inl ?_
      have := statedOmegaPlus_four_ker_eq_bot hGA (by omega) hK hE π hrange hkerY
      rwa [hker] at this
  · refine Or.inl ?_
    by_cases hm3 : m = 3
    · subst hm3
      have := statedOmegaPlus_six_ker_eq_bot hGA hf hK hE π hrange hkerY
      rwa [hker] at this
    · have := statedOmegaPlus_ker_eq_bot hGA (by omega) hf hK hE π hrange hkerY
      rwa [hker] at this

theorem griess_omegaMinus_clause (hGA : GriessAllModelsStatement) [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) (hE : Group.IsPerfect E) (Y : Subgroup E)
    (hY : Y ≤ Subgroup.center E) :
    ∀ (m : ℕ) (b c : K), 2 ≤ m → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∀ π : E →* GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K,
      π.range = StatedOmega (StatedQuadMinus m K b c) → π.ker = Y → Y = ⊥ := by
  intro m b c hm hirr π hrange hker
  obtain ⟨f, hf, hK⟩ := exists_card_eq_two_pow_of_four_le hK4
  have hkerY : π.ker ≤ Subgroup.center E := hker ▸ hY
  by_cases hm2 : m = 2
  · subst hm2
    have := statedOmegaMinus_four_ker_eq_bot hGA hf hK hirr hE π hrange hkerY
    rwa [hker] at this
  · by_cases hm3 : m = 3
    · subst hm3
      have := statedOmegaMinus_six_ker_eq_bot hGA hf hK hirr hE π hrange hkerY
      rwa [hker] at this
    · have := statedOmegaMinus_ker_eq_bot hGA (by omega) (by omega) hK hirr hE π hrange hkerY
      rwa [hker] at this

end Clauses

theorem griessCoverStatement_of_table (hGA : GriessAllModelsStatement)
    (h34 : GriessSL34Statement) : GriessCoverStatement := by
  intro K _ _ _ hK4 E _ _ Y hY hperf
  have hE : Group.IsPerfect E := ⟨hperf⟩
  exact ⟨griess_sl_clause hGA h34 hK4 hE Y hY, griess_sp_clause hGA h34 hK4 hE Y hY,
    griess_omegaPlus_clause hGA hK4 hE Y hY, griess_omegaMinus_clause hGA hK4 hE Y hY⟩

section Certs


theorem griessCoverStatement_of_sl34 (h34 : GriessSL34Statement) : GriessCoverStatement :=
  griessCoverStatement_of_table
    CFSG.Milestones.cl_lit_griess_schur_multipliers_all_models_statement h34

end Certs

end CFSG.RankThree.GF2n.Stroth80
