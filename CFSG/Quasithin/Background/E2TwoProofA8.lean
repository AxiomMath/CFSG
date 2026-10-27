module

public import CFSG.Quasithin.Background.E2TwoProofFam
public import CFSG.Quasithin.Background.E2TwoProofPerm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even8

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique CFSG.QuasithinUnique.L246C127 Equiv

namespace E2P

namespace A8

abbrev A : Subgroup (Perm (Fin 8)) := alternatingGroup (Fin 8)

abbrev U : Subgroup ↥A := Even8.D.subgroupOf A

abbrev L (j : ℕ) : Subgroup (Perm (Fin 8)) :=
  Subgroup.closure {g | g ∈ (Even8.tGens :: Even8.lat).getD j []}

abbrev P (j : ℕ) : Subgroup ↥A := (L j).subgroupOf A

@[expose] def b8 (x : Fin 8) : Bool := decide (x.val < 4)

abbrev Q : Subgroup ↥A := (boolStab2 b8).subgroupOf A

@[expose] def x24 : Perm (Fin 8) := Even8.L1.getD 3 1

theorem x24_mem : x24 ∈ L 1 := Subgroup.subset_closure (by decide)

theorem x24_sign : Perm.sign x24 = 1 := by decide +kernel

theorem x24_not_mem : x24 ∉ boolStab2 b8 := by
  rintro (h | h)
  · have h2 := h 2
    revert h2
    decide +kernel
  · have h0 := h 0
    revert h0
    decide +kernel

theorem getD_eq {j : ℕ} (hj1 : 1 ≤ j) (hj : j < 8) :
    (Even8.tGens :: Even8.lat).getD j [] =
      Even8.tGens ++ [((Even8.tGens :: Even8.lat).getD j []).getD 3 1] := by
  interval_cases j <;> rfl

theorem L_le_A {j : ℕ} (hj : j < 8) : L j ≤ A := by
  rw [Subgroup.closure_le]
  intro g hg
  apply Equiv.Perm.mem_alternatingGroup.mpr
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · exact Even8.tGens_even g hg
  rw [Set.mem_ofPred_eq, getD_eq hj1 hj] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact Even8.tGens_even g hg
  · rw [List.mem_singleton.mp hg]
    interval_cases j <;> decide +kernel

theorem D_le_L {j : ℕ} (hj : j < 8) : Even8.D ≤ L j := by
  apply Subgroup.closure_mono
  intro g hg
  rcases Nat.eq_zero_or_pos j with rfl | hj1
  · exact hg
  rw [Set.mem_ofPred_eq, getD_eq hj1 hj]
  exact List.mem_append_left _ hg

theorem U_le_P {j : ℕ} (hj : j < 8) : U ≤ P j := Subgroup.subgroupOf_mono _ (D_le_L hj)

theorem L_le_part {j : ℕ} (hj : j = 2 ∨ j = 3 ∨ j = 4) : L j ≤ boolStab2 b8 := by
  rw [Subgroup.closure_le]
  intro g hg
  have ht : ∀ g ∈ Even8.tGens, g ∈ boolStab2 b8 := by
    intro g hg
    simp only [Even8.tGens, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact Or.inr fun x => by fin_cases x <;> decide +kernel
    · exact Or.inl fun x => by fin_cases x <;> decide +kernel
    · exact Or.inr fun x => by fin_cases x <;> decide +kernel
  have hj8 : j < 8 := by omega
  rw [Set.mem_ofPred_eq, getD_eq (by omega) hj8] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact ht g hg
  · rw [List.mem_singleton.mp hg]
    rcases hj with rfl | rfl | rfl
    · exact Or.inl fun x => by fin_cases x <;> decide +kernel
    · exact Or.inl fun x => by fin_cases x <;> decide +kernel
    · exact Or.inl fun x => by fin_cases x <;> decide +kernel

theorem card_L {j : ℕ} (hj : j < 8) :
    Nat.card (L j) = Even8.sizes.getD j 0 := by
  have h := lat_card Even8.cert Even8.cert_check j hj
  have e : (Even8.cert.tGens :: Even8.cert.lat)[j]'hj = (Even8.tGens :: Even8.lat).getD j [] := by
    rw [List.getD_eq_getElem _ _ hj]
    rfl
  rw [e] at h
  exact h

theorem card_P {j : ℕ} (hj : j < 8) :
    Nat.card (P j) = Even8.sizes.getD j 0 := by
  rw [card_subgroupOf_of_le (L_le_A hj), card_L hj]

theorem overgroups (Y : Subgroup ↥A) (hY : U ≤ Y) :
    ∃ j, j < 8 ∧ Y = P j ∧ Nat.card Y = Even8.sizes.getD j 0 := by
  obtain ⟨j, hj, -, hYj, -⟩ :=
    lat_cases Even8.cert Even8.closure_mGens Even8.cert_check Y hY
  have hj8 : j < 8 := hj
  have e : (Even8.cert.tGens :: Even8.cert.lat)[j]'hj = (Even8.tGens :: Even8.lat).getD j [] := by
    rw [List.getD_eq_getElem _ _ hj8]
    rfl
  rw [e] at hYj
  refine ⟨j, hj8, hYj, ?_⟩
  rw [hYj, card_P hj8]

theorem card_A : Nat.card A = 20160 := Even8.card_alt

theorem U_le_Q : U ≤ Q :=
  Subgroup.subgroupOf_mono _ ((D_le_L (by norm_num : 4 < 8)).trans (L_le_part (by norm_num)))

theorem x24_mem_A : x24 ∈ A := Equiv.Perm.mem_alternatingGroup.mpr x24_sign

theorem Q_eq : Q = P 4 := by
  obtain ⟨j, hj, hQj, hcQ⟩ := overgroups Q U_le_Q
  have hdvd : Nat.card (P 4) ∣ Nat.card Q :=
    Subgroup.card_dvd_of_le (Subgroup.subgroupOf_mono _ (L_le_part (by norm_num)))
  rw [card_P (by norm_num), hcQ] at hdvd
  have hQ : Q ≠ ⊤ := by
    intro h
    have hx : (⟨x24, x24_mem_A⟩ : ↥A) ∈ Q := by rw [h]; trivial
    exact x24_not_mem hx
  interval_cases j
  all_goals first | (exfalso; revert hdvd; decide) | skip
  · exact hQj
  · exact absurd (Subgroup.eq_top_of_card_eq _ (by rw [hcQ, card_A]; rfl)) hQ

theorem P_le_P4 {j : ℕ} (hj : j = 2 ∨ j = 3) : P j ≤ P 4 := by
  rw [← Q_eq]
  exact Subgroup.subgroupOf_mono _ (L_le_part (by omega))

theorem P1_not_le : ¬ P 1 ≤ P 4 := by
  intro h
  rw [← Q_eq] at h
  exact x24_not_mem (h (Subgroup.mem_subgroupOf.mpr x24_mem : (⟨x24, x24_mem_A⟩ : ↥A) ∈ P 1))

theorem eq_P4 {W : Subgroup ↥A} (hU : U ≤ W)
    (hc : Nat.card W = 576) : W = P 4 := by
  obtain ⟨j, hj, hWj, hcW⟩ := overgroups W hU
  rw [hc] at hcW
  interval_cases j
  all_goals first | (exfalso; revert hcW; decide) | skip
  exact hWj

theorem eq_P1 {W : Subgroup ↥A} (hU : U ≤ W)
    (hc : Nat.card W = 192) (hW : ¬ W ≤ P 4) : W = P 1 := by
  obtain ⟨j, hj, hWj, hcW⟩ := overgroups W hU
  rw [hc] at hcW
  interval_cases j
  all_goals first | (exfalso; revert hcW; decide) | skip
  · exact hWj
  · exact absurd (hWj ▸ P_le_P4 (Or.inl rfl)) hW
  · exact absurd (hWj ▸ P_le_P4 (Or.inr rfl)) hW

theorem P4_ne_top : P 4 ≠ ⊤ := by
  intro h
  have h1 := card_P (j := 4) (by norm_num)
  rw [h, Subgroup.card_top, card_A] at h1
  exact absurd h1 (by decide)

theorem P1_ne_top : P 1 ≠ ⊤ := by
  intro h
  have h1 := card_P (j := 1) (by norm_num)
  rw [h, Subgroup.card_top, card_A] at h1
  exact absurd h1 (by decide)

theorem sup_eq_top : P 4 ⊔ P 1 = ⊤ := by
  obtain ⟨j, hj, hWj, hcW⟩ := overgroups (P 4 ⊔ P 1) ((U_le_P (by norm_num)).trans le_sup_left)
  have hdvd : Nat.card (P 4) ∣ Nat.card ↥(P 4 ⊔ P 1) := Subgroup.card_dvd_of_le le_sup_left
  rw [card_P (by norm_num), hcW] at hdvd
  interval_cases j
  all_goals first | (exfalso; revert hdvd; decide) | skip
  · exact absurd (hWj ▸ (le_sup_right : P 1 ≤ P 4 ⊔ P 1)) P1_not_le
  · exact Subgroup.eq_top_of_card_eq _ (by rw [hcW, card_A]; rfl)

theorem inv (α : MulAut ↥A) (hα : U.map α.toMonoidHom = U) :
    (P 4).map α.toMonoidHom = P 4 ∧ (P 1).map α.toMonoidHom = P 1 := by
  have h4 : (P 4).map α.toMonoidHom = P 4 := by
    refine eq_P4 ?_ ?_
    · rw [← hα]
      exact Subgroup.map_mono (U_le_P (by norm_num))
    · rw [Subgroup.card_map_of_injective α.injective, card_P (by norm_num)]
      rfl
  refine ⟨h4, eq_P1 ?_ ?_ ?_⟩
  · rw [← hα]
    exact Subgroup.map_mono (U_le_P (by norm_num))
  · rw [Subgroup.card_map_of_injective α.injective, card_P (by norm_num)]
    rfl
  · intro h
    rw [← h4, Subgroup.map_le_map_iff_of_injective α.injective] at h
    exact P1_not_le h

end A8

variable {X : Type} [Group X] [Finite X] {K T M : Subgroup X}

theorem ASHyp.not_a8 (hX : ASHyp K T M)
    (e : ↥K ≃* alternatingGroup (Fin 8)) : False :=
  hX.false_of_invPair e Even8.isSylow_D (A8.U_le_P (by norm_num)) (A8.U_le_P (by norm_num))
    A8.P4_ne_top A8.P1_ne_top A8.sup_eq_top A8.inv

end E2P

end CFSG.Quasithin
