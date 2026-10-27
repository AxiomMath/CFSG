module

public import CFSG.LocalAnalysis.StandardType.FS81.N7MainAlg

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

@[expose] def nmE6 : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  {M | ∃ A : Finset (Fin 8), 0 ∉ A ∧ A.card = 6 ∧ M = nmSgn A}

@[expose] def nmF1 : Set (Matrix (Fin 8) (Fin 8) (ZMod 3)) :=
  {M | ∃ A : Finset (Fin 8), 0 ∉ A ∧ Even A.card ∧ M = nmSgn A}

@[expose] noncomputable def nmFixCount (M : Matrix (Fin 8) (Fin 8) (ZMod 3)) : ℕ :=
  Nat.card {v : Coords 8 // M *ᵥ v = v}

theorem nmE6_subset_nmF1 : nmE6 ⊆ nmF1 := by
  rintro M ⟨A, h0, hcard, rfl⟩
  exact ⟨A, h0, by rw [hcard]; exact ⟨3, rfl⟩, rfl⟩

theorem nmF1_subset_nmF : nmF1 ⊆ nmF := by
  rintro M ⟨A, h0, heven, rfl⟩
  exact nmSgn_mem_nmF heven

theorem nmF1_one : (1 : Matrix (Fin 8) (Fin 8) (ZMod 3)) ∈ nmF1 := by
  refine ⟨∅, by simp, ?_, ?_⟩
  · exact ⟨0, rfl⟩
  · ext i j
    by_cases hij : i = j <;> simp [nmSgn, Matrix.one_apply, hij]

private theorem nmh_card_symmDiff_add_two_mul (A B : Finset (Fin 8)) :
    (symmDiff A B).card + 2 * (A ∩ B).card = A.card + B.card := by
  have h1 := Finset.card_sdiff_add_card_inter A B
  have h2 := Finset.card_sdiff_add_card_inter B A
  have e : (symmDiff A B).card = (A \ B).card + (B \ A).card := by
    rw [Finset.symmDiff_def, Finset.card_union_of_disjoint disjoint_sdiff_sdiff]
  rw [Finset.inter_comm B A] at h2
  omega

theorem nmF1_mul {a b : Matrix (Fin 8) (Fin 8) (ZMod 3)} (ha : a ∈ nmF1) (hb : b ∈ nmF1) :
    a * b ∈ nmF1 := by
  obtain ⟨A, hA0, hAeven, rfl⟩ := ha
  obtain ⟨B, hB0, hBeven, rfl⟩ := hb
  refine ⟨symmDiff A B, ?_, ?_, nmSgn_mul⟩
  · simp [Finset.mem_symmDiff, hA0, hB0]
  · have h := nmh_card_symmDiff_add_two_mul A B
    rcases hAeven with ⟨k, hk⟩
    rcases hBeven with ⟨l, hl⟩
    have hle : (A ∩ B).card ≤ A.card := Finset.card_le_card Finset.inter_subset_left
    use k + l - (A ∩ B).card
    omega

theorem nmF1_eq_prod_E6 {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ nmF1) :
    ∃ l : List (Matrix (Fin 8) (Fin 8) (ZMod 3)), (∀ t ∈ l, t ∈ nmE6) ∧ M = l.prod := by
  obtain ⟨A, hA0, hAeven, rfl⟩ := hM
  let P (n : ℕ) : Prop := ∀ A : Finset (Fin 8), A.card = n → 0 ∉ A → Even A.card →
    ∃ l : List (Matrix (Fin 8) (Fin 8) (ZMod 3)), (∀ t ∈ l, t ∈ nmE6) ∧ nmSgn A = l.prod
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro A hcard h0 heven
      by_cases hA : A = ∅
      · subst hA
        refine ⟨[], by simp, ?_⟩
        rw [List.prod_nil]
        ext i j
        by_cases hij : i = j <;> simp [nmSgn, Matrix.one_apply, hij]
      · have hne : A.card ≠ 0 := by
          intro h
          exact hA (Finset.card_eq_zero.mp h)
        rcases heven with ⟨k, hk⟩
        have hkpos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hkpos
          · subst hk0
            simp at hk
            exact absurd hk hA
          · exact hkpos
        have h2 : 2 ≤ A.card := by omega
        have h1lt : 1 < A.card := by omega
        obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp h1lt
        have hi0 : i ≠ 0 := fun h => h0 (h ▸ hi)
        have hj0 : j ≠ 0 := fun h => h0 (h ▸ hj)
        let B := A \ {i, j}
        have hsub : ({i, j} : Finset (Fin 8)) ⊆ A := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rcases hx with rfl | rfl <;> assumption
        have hBcard : B.card = A.card - 2 := by
          rw [Finset.card_sdiff_of_subset hsub, Finset.card_pair hij]
        have hBeven : Even B.card := by
          rw [hBcard]
          use k - 1
          omega
        have hBlt : B.card < A.card := by
          rw [hBcard]
          omega
        rw [hcard] at hBlt
        obtain ⟨l, hl_mem, hl_prod⟩ := ih B.card hBlt B rfl (by simp [B, h0]) hBeven
        let ti := nmSgn (Finset.univ \ {0, i})
        let tj := nmSgn (Finset.univ \ {0, j})
        have hti_mem : ti ∈ nmE6 := by
          refine ⟨Finset.univ \ {0, i}, ?_, ?_, rfl⟩
          · simp [hi0]
          · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair (Ne.symm hi0),
              Finset.card_univ, Fintype.card_fin]
        have htj_mem : tj ∈ nmE6 := by
          refine ⟨Finset.univ \ {0, j}, ?_, ?_, rfl⟩
          · simp [hj0]
          · rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_pair (Ne.symm hj0),
              Finset.card_univ, Fintype.card_fin]
        have hsymm : symmDiff (Finset.univ \ {0, i}) (Finset.univ \ {0, j}) = {i, j} := by
          ext x
          simp only [Finset.mem_symmDiff, Finset.mem_sdiff, Finset.mem_univ,
            Finset.mem_singleton, Finset.mem_insert, true_and]
          by_cases hx0 : x = 0
          · subst hx0; simp [hi0, hj0, Ne.symm hi0, Ne.symm hj0]
          · by_cases hxi : x = i
            · subst hxi; simp [hi0, hij]
            · by_cases hxj : x = j
              · subst hxj; simp [hj0, hij, Ne.symm hij]
              · simp [hx0, hxi, hxj]
        have htij : ti * tj = nmSgn {i, j} := by
          dsimp [ti, tj]
          rw [nmSgn_mul, hsymm]
        have hdisj : Disjoint {i, j} B := by
          rw [Finset.disjoint_iff_inter_eq_empty]
          ext x
          simp [B]
        have hunion : {i, j} ∪ B = A := by
          rw [Finset.union_sdiff_of_subset hsub]
        have hsymm2 : symmDiff {i, j} B = A := by
          rw [Finset.symmDiff_eq_union hdisj, hunion]
        refine ⟨ti :: tj :: l, ?_, ?_⟩
        · intro t ht
          simp only [List.mem_cons] at ht
          rcases ht with rfl | rfl | ht
          · exact hti_mem
          · exact htj_mem
          · exact hl_mem t ht
        · rw [List.prod_cons, List.prod_cons, ← hl_prod, ← mul_assoc, htij,
            nmSgn_mul, hsymm2]
  exact hP A.card A rfl hA0 hAeven

theorem nmFixCount_conj {g g' M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (h₁ : g * g' = 1)
    (h₂ : g' * g = 1) : nmFixCount (g * M * g') = nmFixCount M := by
  unfold nmFixCount
  let e : Coords 8 ≃ Coords 8 := {
    toFun := fun v => g' *ᵥ v
    invFun := fun w => g *ᵥ w
    left_inv := fun v => by
      change g *ᵥ (g' *ᵥ v) = v
      rw [Matrix.mulVec_mulVec, h₁, Matrix.one_mulVec]
    right_inv := fun w => by
      change g' *ᵥ (g *ᵥ w) = w
      rw [Matrix.mulVec_mulVec, h₂, Matrix.one_mulVec]
  }
  have h_iff : ∀ v : Coords 8, ((g * M * g') *ᵥ v = v) ↔
      (M *ᵥ (g' *ᵥ v) = g' *ᵥ v) := by
    intro v
    constructor
    · intro hv
      have h1 : g *ᵥ (M *ᵥ (g' *ᵥ v)) = v := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
        exact hv
      have h2 : g' *ᵥ (g *ᵥ (M *ᵥ (g' *ᵥ v))) = g' *ᵥ v := by rw [h1]
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h₂, one_mul] at h2
    · intro hv
      have h1 : g *ᵥ (M *ᵥ (g' *ᵥ v)) = g *ᵥ (g' *ᵥ v) := by rw [hv]
      have h2 : (g * M * g') *ᵥ v = v := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, Matrix.mulVec_mulVec, h₁,
          Matrix.one_mulVec]
      exact h2
  exact Nat.card_congr (e.subtypeEquiv h_iff)

theorem nmFixCount_of_mem_nmE6 {M : Matrix (Fin 8) (Fin 8) (ZMod 3)} (hM : M ∈ nmE6) :
    nmFixCount M = 9 := by
  obtain ⟨A, hA0, hAcard, rfl⟩ := hM
  unfold nmFixCount
  have h_iff : ∀ v : Coords 8, nmSgn A *ᵥ v = v ↔ ∀ i ∈ A, v i = 0 := by
    intro v
    constructor
    · intro h i hi
      have hcoord := congrFun h i
      rw [nmSgn_mulVec] at hcoord
      simp only [if_pos hi] at hcoord
      rcases (ZMod.neg_eq_self_iff (v i)).mp hcoord with h0 | h2
      · exact h0
      · omega
    · intro h
      ext i
      rw [nmSgn_mulVec]
      by_cases hi : i ∈ A
      · simp [hi, h i hi]; exact neg_zero
      · simp [hi]
  rw [Nat.card_congr (Equiv.subtypeEquivRight h_iff)]
  let e : {v : Coords 8 // ∀ i ∈ A, v i = 0} ≃ (↥Aᶜ → ZMod 3) := {
    toFun := fun v i => v.1 i.1
    invFun := fun w => ⟨fun i => if h : i ∈ A then 0 else w ⟨i, by simpa using h⟩, by
      intro i hi
      simp [hi]⟩
    left_inv := by
      intro v
      apply Subtype.ext
      funext i
      by_cases hi : i ∈ A
      · simp [hi, v.2 i hi]
      · simp [hi]
    right_inv := by
      intro w
      funext i
      have hi : (i : Fin 8) ∉ A := Finset.mem_compl.mp i.2
      simp [hi]
  }
  rw [Nat.card_congr e]
  rw [Nat.card_fun, Nat.card_zmod]
  have hcardA : Nat.card ↥Aᶜ = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hAcard]
  rw [hcardA]
  norm_num

end CFSG.StandardType.FrameRoute.FS81

end
