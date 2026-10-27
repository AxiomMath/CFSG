module

public import CFSG.Quasithin.H13.GoldschmidtC137S6Fin1

public section

namespace CFSG.Quasithin.H13.U3.GC137

open Subgroup CFSG.Quasithin.B3

@[expose] def dcReps : List Tab :=
  [[0, 1, 2, 4, 3, 5], [0, 2, 1, 4, 3, 5], [0, 2, 4, 5, 1, 3], [0, 4, 1, 5, 2, 3],
    [0, 4, 2, 5, 1, 3]]

@[expose] def dcl (w : Tab) : List Tab :=
  T6l.flatMap fun t => T6l.map fun u => mulT (mulT t w) u

@[expose] def covL : List Tab :=
  H1l ++ H2l.filter (fun t => !H1l.contains t) ++ dcReps.flatMap fun w => (dcl w).dedup

set_option maxRecDepth 100000 in
theorem covL_ok : covL.length = 720 ∧ covL.Nodup ∧ ∀ t ∈ covL, isTab 6 t = true := by
  decide +kernel

theorem mem_covL (g : Gp 6) : tab g ∈ covL := by
  classical
  obtain ⟨hlen, hnd, hv⟩ := covL_ok
  let S : Finset Tab := covL.toFinset
  have hS : S.card = 720 := by
    rw [List.toFinset_card_of_nodup hnd, hlen]
  let F : S → Gp 6 := fun t => Classical.choose (exists_tab_eq (hv t.1 (List.mem_toFinset.1 t.2)))
  have hF : ∀ t : S, tab (F t) = t.1 := fun t =>
    Classical.choose_spec (exists_tab_eq (hv t.1 (List.mem_toFinset.1 t.2)))
  have hinj : Function.Injective F := fun a b h => Subtype.ext (by rw [← hF a, ← hF b, h])
  have hcard : Fintype.card S = Fintype.card (Gp 6) := by
    rw [Fintype.card_coe, hS, Fintype.card_perm, Fintype.card_fin]
    rfl
  obtain ⟨t, ht⟩ := (Fintype.bijective_iff_injective_and_card F).2 ⟨hinj, hcard⟩ |>.2 g
  rw [← ht, hF]
  exact List.mem_toFinset.1 t.2

@[expose] def tokT (w : Tab) (a : ℕ) : Tab :=
  if a == 100 then w else if a == 101 then invT w else T6l.getD a (idT 6)

@[expose] def evalWord (w : Tab) : List ℕ → Tab
  | [] => idT 6
  | a :: l => mulT (tokT w a) (evalWord w l)

@[expose] def wordsFor : List (Tab × List ℕ × List ℕ) :=
  [([0, 1, 2, 4, 3, 5], [0, 100, 10, 100, 8, 100, 12], [0, 100, 0]),
    ([0, 2, 1, 4, 3, 5], [2, 100, 4, 100, 10], [1, 100, 1, 100, 1]),
    ([0, 2, 4, 5, 1, 3], [2, 100, 1, 101, 2], [9, 101, 2, 100, 9]),
    ([0, 4, 1, 5, 2, 3], [2, 101, 1, 100, 2], [9, 100, 2, 101, 9]),
    ([0, 4, 2, 5, 1, 3], [2, 100, 1, 100, 2], [3, 100, 2, 100, 3])]

set_option maxRecDepth 100000 in
theorem wordsOK : (wordsFor.map (·.1)) = dcReps ∧ ∀ e ∈ wordsFor,
    (e.2.1.all fun a => decide (a < 16) || a == 100 || a == 101) = true ∧
    (e.2.2.all fun a => decide (a < 16) || a == 100 || a == 101) = true ∧
    evalWord e.1 e.2.1 = tab (Equiv.swap (1 : Fin 6) 2) ∧
    evalWord e.1 e.2.2 = tab (Equiv.swap (3 : Fin 6) 4) := by
  decide +kernel


theorem evalWord_mem {K : Subgroup (Gp 6)} (hK : T6 ≤ K) {w : Tab} {W : Gp 6} (hW : tab W = w)
    (hWK : W ∈ K) :
    ∀ l : List ℕ, (l.all fun a => decide (a < 16) || a == 100 || a == 101) = true →
      ∃ σ ∈ K, tab σ = evalWord w l := by
  intro l
  induction l with
  | nil =>
    intro _
    exact ⟨1, K.one_mem, by rw [tab_one]; rfl⟩
  | cons a l ih =>
    intro h
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨σ', hσ'K, hσ'⟩ := ih h.2
    have htok : ∃ τ ∈ K, tab τ = tokT w a := by
      simp only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      rcases h.1 with (ha | ha) | ha
      · have hmem : T6l.getD a (idT 6) ∈ T6l := by
          rw [List.getD_eq_getElem _ _ (by simp [T6l]; omega)]
          exact List.getElem_mem _
        obtain ⟨τ, hτ⟩ := exists_tab_eq ((subOK_spec subOK_lists.1).1 _ hmem)
        refine ⟨τ, hK ((mem_T6).2 (by rw [hτ]; exact hmem)), ?_⟩
        have : ¬ a = 100 := by omega
        have : ¬ a = 101 := by omega
        simp [tokT, *]
      · refine ⟨W, hWK, ?_⟩
        simp [tokT, ha, hW]
      · refine ⟨W⁻¹, K.inv_mem hWK, ?_⟩
        simp [tokT, ha, tab_inv, hW]
    obtain ⟨τ, hτK, hτ⟩ := htok
    exact ⟨τ * σ', K.mul_mem hτK hσ'K, by rw [tab_mul, hτ, hσ']; rfl⟩

theorem eq_top_of_swaps {K : Subgroup (Gp 6)} (hK : T6 ≤ K) (h12 : Equiv.swap (1 : Fin 6) 2 ∈ K)
    (h34 : Equiv.swap (3 : Fin 6) 4 ∈ K) : K = ⊤ := by
  have hT : ∀ (a b : Fin 6), tab (Equiv.swap a b) ∈ T6l → Equiv.swap a b ∈ K := fun a b h =>
    hK ((mem_T6).2 h)
  have h01 : Equiv.swap (0 : Fin 6) 1 ∈ K := hT _ _ (by decide +kernel)
  have h23 : Equiv.swap (2 : Fin 6) 3 ∈ K := hT _ _ (by decide +kernel)
  have h45 : Equiv.swap (4 : Fin 6) 5 ∈ K := hT _ _ (by decide +kernel)
  rw [eq_top_iff, ← Subgroup.closure_eq_top_of_mclosure_eq_top
    (Equiv.Perm.mclosure_swap_castSucc_succ 5), Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact h01
  · exact h12
  · exact h23
  · exact h34
  · exact h45

theorem dcReps_tab : ∀ w ∈ dcReps, isTab 6 w = true := by decide +kernel

theorem eq_top_of_not_mem {K : Subgroup (Gp 6)} (hK : T6 ≤ K) {g : Gp 6} (hg : g ∈ K)
    (h1 : g ∉ H1) (h2 : g ∉ H2) : K = ⊤ := by
  have hc := mem_covL g
  have h1' : tab g ∉ H1l := fun h => h1 ((mem_H1).2 h)
  have h2' : tab g ∉ H2l := fun h => h2 ((mem_H2).2 h)
  have hc3 : ∃ w ∈ dcReps, tab g ∈ dcl w := by
    simp only [covL, List.mem_append, List.mem_flatMap, List.mem_dedup] at hc
    rcases hc with (hc | hc) | hc
    · exact absurd hc h1'
    · exact absurd (List.mem_of_mem_filter hc) h2'
    · exact hc
  obtain ⟨w, hw, hgw⟩ := hc3
  obtain ⟨W, hW⟩ := exists_tab_eq (dcReps_tab w hw)
  simp only [dcl, List.mem_flatMap, List.mem_map] at hgw
  obtain ⟨t, ht, u, hu, hgtu⟩ := hgw
  obtain ⟨Tt, hTt⟩ := exists_tab_eq ((subOK_spec subOK_lists.1).1 t ht)
  obtain ⟨U, hU⟩ := exists_tab_eq ((subOK_spec subOK_lists.1).1 u hu)
  have hTK : Tt ∈ K := hK ((mem_T6).2 (by rw [hTt]; exact ht))
  have hUK : U ∈ K := hK ((mem_T6).2 (by rw [hU]; exact hu))
  have hg_eq : g = Tt * W * U := by
    apply tab_injective
    rw [tab_mul, tab_mul, hTt, hW, hU]
    exact hgtu.symm
  have hWK : W ∈ K := by
    have : W = Tt⁻¹ * g * U⁻¹ := by rw [hg_eq]; group
    rw [this]
    exact K.mul_mem (K.mul_mem (K.inv_mem hTK) hg) (K.inv_mem hUK)
  obtain ⟨hmap, hwords⟩ := wordsOK
  have hwm : w ∈ wordsFor.map (·.1) := by rw [hmap]; exact hw
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hwm
  obtain ⟨hw1, hw2, hev1, hev2⟩ := hwords e he
  obtain ⟨σ₁, hσ₁K, hσ₁⟩ := evalWord_mem hK hW hWK e.2.1 hw1
  obtain ⟨σ₂, hσ₂K, hσ₂⟩ := evalWord_mem hK hW hWK e.2.2 hw2
  have e1 : σ₁ = Equiv.swap (1 : Fin 6) 2 := tab_injective (by rw [hσ₁, hev1])
  have e2 : σ₂ = Equiv.swap (3 : Fin 6) 4 := tab_injective (by rw [hσ₂, hev2])
  exact eq_top_of_swaps hK (e1 ▸ hσ₁K) (e2 ▸ hσ₂K)

theorem eq_or_eq_of_le {A B K : Subgroup (Gp 6)} (hA : Nat.card A = 16) (hB : Nat.card B = 48)
    (hAK : A ≤ K) (hKB : K ≤ B) : K = A ∨ K = B := by
  have h1 : Nat.card A ∣ Nat.card K := Subgroup.card_dvd_of_le hAK
  have h2 : Nat.card K ∣ Nat.card B := Subgroup.card_dvd_of_le hKB
  rw [hA] at h1
  rw [hB] at h2
  have hKpos : 0 < Nat.card K := Nat.card_pos
  have hle : Nat.card K ≤ 48 := Nat.le_of_dvd (by norm_num) h2
  obtain ⟨m, hm⟩ := h1
  have hm_le : m ≤ 3 := by omega
  have hm_pos : 0 < m := by omega
  interval_cases m
  · left
    exact (Subgroup.eq_of_le_of_card_ge hAK (by omega)).symm
  · rw [hm] at h2
    exact absurd h2 (by decide)
  · right
    exact Subgroup.eq_of_le_of_card_ge hKB (by omega)

theorem overgroups {K : Subgroup (Gp 6)} (hK : T6 ≤ K) :
    K = T6 ∨ K = H1 ∨ K = H2 ∨ K = ⊤ := by
  by_cases hH1 : K ≤ H1
  · rcases eq_or_eq_of_le card_T6 card_H1 hK hH1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  by_cases hH2 : K ≤ H2
  · rcases eq_or_eq_of_le card_T6 card_H2 hK hH2 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
  obtain ⟨a, haK, haH1⟩ := IsConcreteLE.not_le_iff_exists.1 hH1
  obtain ⟨b, hbK, hbH2⟩ := IsConcreteLE.not_le_iff_exists.1 hH2
  refine Or.inr (Or.inr (Or.inr ?_))
  by_cases ha2 : a ∈ H2
  · by_cases hb1 : b ∈ H1
    · refine eq_top_of_not_mem hK (K.mul_mem haK hbK) ?_ ?_
      · intro h
        exact haH1 (by simpa using H1.mul_mem h (H1.inv_mem hb1))
      · intro h
        exact hbH2 (by simpa using H2.mul_mem (H2.inv_mem ha2) h)
    · exact eq_top_of_not_mem hK hbK hb1 hbH2
  · exact eq_top_of_not_mem hK haK haH1 ha2

end CFSG.Quasithin.H13.U3.GC137
