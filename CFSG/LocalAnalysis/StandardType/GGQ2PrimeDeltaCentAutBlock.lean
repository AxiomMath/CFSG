module

public import CFSG.LargeExtraspecial.SMod20AutReal
import all CFSG.Fischer.F4

public section

namespace CFSG.GGQ2Prime

open CFSG.Fischer CFSG.LargeExtraspecial.SMod20.Aut Matrix

private theorem hermStd_single_left_sq (m : Fin 6) (w : W) :
    hermStd (Pi.single m 1) w = (w m) ^ 2 := by
  rw [← herm_eq_std]; exact herm_e_left m w

private theorem hermStd_pair_left (a : F4) (m n : Fin 6) (w : W) :
    hermStd (Pi.single m 1 + a • Pi.single n 1) w = (w m) ^ 2 + a * (w n) ^ 2 := by
  rw [hermStd_add_left, hermStd_smul_left, hermStd_single_left_sq, hermStd_single_left_sq]

theorem pairVec_ne_zero_and_isotropic {i j : Fin 6} (hij : i ≠ j) {c : F4} (hc : c ≠ 0) :
    (Pi.single i 1 + c • Pi.single j 1 : W) ≠ 0 ∧
      hermStd (Pi.single i 1 + c • Pi.single j 1) (Pi.single i 1 + c • Pi.single j 1) = 0 := by
  have cube : ∀ a : F4, a ≠ 0 → a * a ^ 2 = 1 := by decide
  have two : (1 : F4) + 1 = 0 := by decide
  have hui : (Pi.single i 1 + c • Pi.single j 1 : W) i = 1 := by simp [Pi.single_apply, hij]
  have huj : (Pi.single i 1 + c • Pi.single j 1 : W) j = c := by
    simp [Pi.single_apply, hij.symm]
  refine ⟨fun h => ?_, ?_⟩
  · have := congrFun h i
    rw [hui] at this
    exact one_ne_zero this
  · rw [hermStd_pair_left, hui, huj, cube c hc, one_pow, two]

private theorem exists_index_ne_three_of_fin_six :
    ∀ i j n : Fin 6, ∃ m : Fin 6, m ≠ i ∧ m ≠ j ∧ m ≠ n := by
  decide

private theorem eq_smul_pair_of_orth {i j : Fin 6} (hij : i ≠ j) {c : F4} (hc : c ≠ 0) {v : W}
    (hv : ∀ x : W, x ≠ 0 → hermStd x x = 0 →
      hermStd x (Pi.single i 1 + c • Pi.single j 1) = 0 → hermStd x v = 0) :
    ∃ κ : F4, v = κ • (Pi.single i 1 + c • Pi.single j 1) := by
  have cube : ∀ a : F4, a ≠ 0 → a * a ^ 2 = 1 := by decide
  have two : (1 : F4) + 1 = 0 := by decide
  have hx : ∀ (a : F4), a ≠ 0 → ∀ m n : Fin 6, m ≠ n → m ≠ i → m ≠ j → n ≠ i → n ≠ j →
      hermStd (Pi.single m 1 + a • Pi.single n 1) v = 0 := by
    intro a ha m n hmn hmi hmj hni hnj
    apply hv
    · intro h0
      have := congrFun h0 m
      simp [Pi.single_apply, hmn] at this
    · rw [hermStd_pair_left]
      simp [Pi.single_apply, hmn, hmn.symm, cube a ha, two]
    · rw [hermStd_pair_left]
      simp [Pi.single_apply, hmi, hmj, hni, hnj]
  have h0 : ∀ n, n ≠ i → n ≠ j → v n = 0 := by
    intro n hni hnj
    obtain ⟨m, hmi, hmj, hmn⟩ := exists_index_ne_three_of_fin_six i j n
    have e1 := hx 1 one_ne_zero m n hmn hmi hmj hni hnj
    have e2 := hx F4.ω (by decide) m n hmn hmi hmj hni hnj
    rw [hermStd_pair_left] at e1 e2
    have key : ∀ a b : F4, a + 1 * b = 0 → a + F4.ω * b = 0 → b = 0 := by decide
    exact (pow_eq_zero_iff two_ne_zero).1 (key _ _ e1 e2)
  obtain ⟨hne, hiso⟩ := pairVec_ne_zero_and_isotropic hij hc
  have hvu := hv _ hne hiso hiso
  rw [hermStd_pair_left] at hvu
  have key : ∀ a b c : F4, c ≠ 0 → a ^ 2 + c * b ^ 2 = 0 → a = c ^ 2 * b := by decide
  refine ⟨c ^ 2 * v j, funext fun k => ?_⟩
  by_cases hki : k = i
  · subst hki
    simp [Pi.single_apply, hij, key _ _ c hc hvu]
  · by_cases hkj : k = j
    · subst hkj
      simp only [Pi.smul_apply, Pi.add_apply, Pi.single_apply, hki, hij.symm, if_true, if_false,
        smul_eq_mul, zero_add, mul_one]
      linear_combination (-(v k)) * cube c hc
    · simp [Pi.single_apply, hki, hkj, h0 k hki hkj]

private theorem semiVec_pair_apply_entry (A : GU0) (φ : F4 ≃+* F4) (i j : Fin 6) (c : F4)
    (k : Fin 6) : semiVec A φ (Pi.single i 1 + c • Pi.single j 1) k =
      ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) k i +
        φ c * ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) k j := by
  have hf : fvec φ (Pi.single i 1 + c • Pi.single j 1) = Pi.single i 1 + φ c • Pi.single j 1 := by
    funext l
    simp only [fvec, Pi.add_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, map_add, map_mul]
    split_ifs <;> simp
  rw [semiVec, hf, mulVec_add, mulVec_smul, mulVec_single_one, mulVec_single_one]
  simp [Matrix.col_apply]

private theorem exists_index_ne_zero_ne_two :
    ∀ j k : Fin 6, ∃ i : Fin 6, i ≠ 0 ∧ i ≠ j ∧ i ≠ k := by
  decide

private theorem semiVec_block_diag_of_fix_pairs (A : GU0) (φ : F4 ≃+* F4)
    (h : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ c : F4, (c = 1 ∨ c = F4.ω) →
      ∃ κ : F4, semiVec A φ (Pi.single i 1 + c • Pi.single j 1) =
        κ • (Pi.single i 1 + c • Pi.single j 1)) :
    (∀ x : F4, φ x = x) ∧ ∃ α β : F4, α ≠ 0 ∧ β ≠ 0 ∧ ∀ k l : Fin 6,
      ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) k l =
        if k = l then (if l = 0 then α else β) else 0 := by
  set M := ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) with hM
  have hent : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ c : F4, (c = 1 ∨ c = F4.ω) →
      ∃ κ : F4, ∀ k, M k i + φ c * M k j =
        κ * ((if k = i then 1 else 0) + c * (if k = j then 1 else 0)) := by
    intro i j hi hj hij c hc
    obtain ⟨κ, hκ⟩ := h i j hi hj hij c hc
    refine ⟨κ, fun k => ?_⟩
    have := congrFun hκ k
    rw [semiVec_pair_apply_entry] at this
    simpa [Pi.single_apply] using this
  have hω1 : φ F4.ω ≠ 1 := fun h1 => by
    have : φ F4.ω = φ 1 := by rw [h1, map_one]
    exact absurd (φ.injective this) (by decide)
  have key1 : ∀ a b w : F4, w ≠ 1 → a + b = 0 → a + w * b = 0 → b = 0 := by decide
  have S1 : ∀ j k : Fin 6, j ≠ 0 → k ≠ j → M k j = 0 := by
    intro j k hj hkj
    obtain ⟨i, hi0, hij, hik⟩ := exists_index_ne_zero_ne_two j k
    obtain ⟨κ₁, e1⟩ := hent i j hi0 hj hij 1 (Or.inl rfl)
    obtain ⟨κ₂, e2⟩ := hent i j hi0 hj hij F4.ω (Or.inr rfl)
    have e1' := e1 k
    have e2' := e2 k
    simp [hkj, Ne.symm hik] at e1' e2'
    exact key1 _ _ _ hω1 e1' e2'
  have S2 : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → M i i = M j j := by
    intro i j hi hj hij
    obtain ⟨κ, e⟩ := hent i j hi hj hij 1 (Or.inl rfl)
    have ei := e i
    have ej := e j
    simp [hij, Ne.symm hij, S1 j i hj hij, S1 i j hi (Ne.symm hij)] at ei ej
    rw [ei, ej]
  have hβ : ∀ j : Fin 6, j ≠ 0 → M j j = M 1 1 := by
    intro j hj
    by_cases h1 : j = 1
    · rw [h1]
    · exact (S2 1 j (by decide) hj (Ne.symm h1)).symm
  have hcol : ∀ j : Fin 6, M *ᵥ (Pi.single j 1) ≠ 0 → M j j ≠ 0 ∨ j = 0 := by
    intro j hne
    by_cases hj : j = 0
    · exact Or.inr hj
    · refine Or.inl fun h0 => hne ?_
      funext k
      rw [mulVec_single_one, col_apply]
      by_cases hk : k = j
      · subst hk; exact h0
      · exact S1 j k hj hk
  have hne1 : (Pi.single (1 : Fin 6) (1 : F4) : W) ≠ 0 := fun h0 => by
    have := congrFun h0 1
    simp at this
  have hβ0 : M 1 1 ≠ 0 := by
    rcases hcol 1 (mulVec_ne_zero (A : GL (Fin 6) F4) hne1) with h1 | h1
    · exact h1
    · exact absurd h1 (by decide)
  have S3 : φ F4.ω = F4.ω := by
    obtain ⟨κ, e⟩ := hent 1 2 (by decide) (by decide) (by decide) F4.ω (Or.inr rfl)
    have e1 := e 1
    have e2 := e 2
    simp [S1 2 1 (by decide) (by decide), S1 1 2 (by decide) (by decide)] at e1 e2
    rw [hβ 2 (by decide), e1] at e2
    have hκ : κ ≠ 0 := by rw [← e1]; exact hβ0
    exact mul_right_cancel₀ hκ (by rw [e2, mul_comm])
  have hsq : ∀ (x : W) (j : Fin 6), hermStd x (Pi.single j 1) = x j := fun x j => by
    rw [hermStd_swap, hermStd_single_left_sq]
    exact F4.sq_sq _
  have S4 : ∀ j : Fin 6, j ≠ 0 → M j 0 = 0 := by
    intro j hj
    have hMj : M *ᵥ (Pi.single j 1) = M 1 1 • (Pi.single j 1 : W) := by
      funext k
      rw [mulVec_single_one, col_apply]
      by_cases hk : k = j
      · subst hk; simp [hβ k hj]
      · simp [S1 j k hj hk, Pi.single_apply, hk]
    have iso := hermStd_mulVec A (Pi.single 0 1) (Pi.single j 1)
    rw [hMj, hermStd_smul_right] at iso
    simp only [hsq, mulVec_single_one, col_apply] at iso
    simp [Pi.single_apply, hj] at iso
    rcases iso with h | h
    · exact absurd h hβ0
    · exact h
  have hα0 : M 0 0 ≠ 0 := by
    have hne0 : (Pi.single (0 : Fin 6) (1 : F4) : W) ≠ 0 := fun h0 => by
      have := congrFun h0 0
      simp at this
    intro h0
    apply mulVec_ne_zero (A : GL (Fin 6) F4) hne0
    funext k
    rw [mulVec_single_one, col_apply]
    by_cases hk : k = 0
    · subst hk; exact h0
    · exact S4 k hk
  refine ⟨fun x => ?_, M 0 0, M 1 1, hα0, hβ0, fun k l => ?_⟩
  · have hx : ∀ x : F4, x = 0 ∨ x = 1 ∨ x = F4.ω ∨ x = F4.ω + 1 := by decide
    rcases hx x with rfl | rfl | rfl | rfl
    · exact map_zero φ
    · exact map_one φ
    · exact S3
    · rw [map_add, S3, map_one]
  · by_cases hl : l = 0
    · subst hl
      by_cases hk : k = 0
      · subst hk; simp
      · simp [hk, S4 k hk]
    · by_cases hk : k = l
      · subst hk; simp [hl, hβ k hl]
      · simp [hk, S1 l k hl hk]

theorem semiVec_diag_of_orth_pairs (A : GU0) (φ : F4 ≃+* F4)
    (h : ∀ i j : Fin 6, i ≠ 0 → j ≠ 0 → i ≠ j → ∀ c : F4, (c = 1 ∨ c = F4.ω) →
      ∀ x : W, x ≠ 0 → hermStd x x = 0 → hermStd x (Pi.single i 1 + c • Pi.single j 1) = 0 →
        hermStd x (semiVec A φ (Pi.single i 1 + c • Pi.single j 1)) = 0) :
    (∀ x : F4, φ x = x) ∧ ∃ α β : F4, α ≠ 0 ∧ β ≠ 0 ∧ ∀ k l : Fin 6,
      ((A : GL (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4) k l =
        if k = l then (if l = 0 then α else β) else 0 :=
  semiVec_block_diag_of_fix_pairs A φ fun i j hi hj hij c hc =>
    eq_smul_pair_of_orth hij (by rcases hc with rfl | rfl <;> decide) (h i j hi hj hij c hc)

end CFSG.GGQ2Prime
