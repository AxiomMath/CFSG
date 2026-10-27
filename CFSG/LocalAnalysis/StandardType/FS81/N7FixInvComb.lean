module

public import CFSG.LocalAnalysis.StandardType.FS81.N7FixDefs

public section

namespace CFSG.StandardType.FrameRoute.FS81

open scoped Matrix

theorem q2nN7_sq_of_mul_self {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (h2 : spMat σ s * spMat σ s = 1) : ∀ j, σ (σ j) = j ∧ s (σ j) * s j = 1 := by
  intro j
  have e := congrFun (congrFun h2 (σ (σ j))) j
  rw [spMat_mul, spMat_apply, Equiv.Perm.mul_apply, if_pos rfl, Matrix.one_apply] at e
  have hne : s (σ j) * s j ≠ 0 := by
    rcases hs (σ j) with h1 | h1 <;> rcases hs j with h3 | h3 <;> rw [h1, h3] <;> decide
  by_cases hj : σ (σ j) = j
  · rw [if_pos hj] at e
    exact ⟨hj, e⟩
  · rw [if_neg hj] at e
    exact absurd e hne

theorem q2nN7_classify {σ : Equiv.Perm (Fin 8)} {s : Fin 8 → ZMod 3} (hs : IsSign s)
    (hσ0 : σ 0 = 0) (hs0 : s 0 = 1) (hprod : ∏ i : Fin 7, s i.succ = 1)
    (hsq : ∀ j, σ (σ j) = j ∧ s (σ j) * s j = 1)
    (hone : ∀ i i' : Fin 8, i ≠ 0 → i' ≠ 0 → (σ i ≠ i ∨ s i = 1) → (σ i' ≠ i' ∨ s i' = 1) →
      i' = i ∨ i' = σ i) :
    ∃ S : Finset (Fin 8), (0 : Fin 8) ∉ S ∧ S.card = 6 ∧ spMat σ s = sgn S := by
  classical
  have hprod8 : ∏ i : Fin 8, s i = 1 := by
    rw [Fin.prod_univ_succ, hs0, one_mul, hprod]
  have hnotgood : ∀ i : Fin 8, i ≠ 0 → ¬(σ i ≠ i ∨ s i = 1) → σ i = i ∧ s i = -1 := by
    intro i _ h
    have hfix : σ i = i := by
      by_contra hne
      exact h (Or.inl hne)
    refine ⟨hfix, ?_⟩
    rcases hs i with h1 | h1
    · exact (h (Or.inr h1)).elim
    · exact h1
  by_cases hg : ∃ i : Fin 8, i ≠ 0 ∧ (σ i ≠ i ∨ s i = 1)
  ·
    obtain ⟨i₀, hi₀ne, hi₀good⟩ := hg
    by_cases hfix0 : σ i₀ = i₀
    ·
      have hi₀s : s i₀ = 1 := by
        rcases hi₀good with h | h
        · exact absurd hfix0 h
        · exact h
      have hother : ∀ i : Fin 8, i ≠ 0 → i ≠ i₀ → σ i = i ∧ s i = -1 := by
        intro i hi hi'
        refine hnotgood i hi ?_
        intro hgood
        rcases hone i₀ i hi₀ne hi hi₀good hgood with h' | h'
        · exact hi' h'
        · exact hi' (h'.trans hfix0)
      have hσ1 : σ = 1 := Equiv.ext fun i => by
        by_cases hi : i = 0
        · subst hi
          exact hσ0
        · by_cases hi' : i = i₀
          · subst hi'
            exact hfix0
          · exact (hother i hi hi').1
      have hsS : s = fun i =>
          if i ∈ (Finset.univ \ ({0, i₀} : Finset (Fin 8))) then -1 else 1 := by
        funext i
        by_cases hi : i ∈ (Finset.univ \ ({0, i₀} : Finset (Fin 8)))
        · rw [if_pos hi]
          exact (hother i
            (fun h => (Finset.mem_sdiff.mp hi).2 (by simp [h]))
            (fun h => (Finset.mem_sdiff.mp hi).2 (by simp [h]))).2
        · rw [if_neg hi]
          have hmem : i = 0 ∨ i = i₀ := by
            by_cases h0 : i = 0
            · exact Or.inl h0
            · have hhi : ¬ i = 0 → i = i₀ := by simpa using hi
              exact Or.inr (hhi h0)
          rcases hmem with h | h
          · rw [h, hs0]
          · rw [h, hi₀s]
      refine ⟨Finset.univ \ ({0, i₀} : Finset (Fin 8)), ?_, ?_, ?_⟩
      · simp
      · have hsub : ({0, i₀} : Finset (Fin 8)) ⊆ Finset.univ := Finset.subset_univ _
        rw [Finset.card_sdiff_of_subset hsub, Finset.card_univ, Fintype.card_fin]
        have hpair : ({0, i₀} : Finset (Fin 8)).card = 2 := by
          rw [Finset.card_pair_eq_two_iff]
          exact hi₀ne.symm
        rw [hpair]
      · calc
          spMat σ s = spMat 1 s := by rw [hσ1]
          _ = spMat 1 (fun i =>
                if i ∈ (Finset.univ \ ({0, i₀} : Finset (Fin 8))) then -1 else 1) := by
                  rw [hsS]
          _ = sgn (Finset.univ \ ({0, i₀} : Finset (Fin 8))) :=
                (q2nN7_sgn_eq_spMat _).symm
    ·
      exfalso
      set j₀ : Fin 8 := σ i₀ with hj₀def
      have hj₀ne0 : j₀ ≠ 0 := by
        intro h
        have hσ : σ i₀ = σ 0 := by rw [← hj₀def, h, hσ0]
        exact hi₀ne (σ.injective hσ)
      have hj₀ne_i₀ : j₀ ≠ i₀ := hfix0
      have hj₀good : σ j₀ ≠ j₀ ∨ s j₀ = 1 := by
        left
        have h1 : σ j₀ = i₀ := (hsq i₀).1
        intro h
        exact hj₀ne_i₀ (h.symm.trans h1)
      have hother : ∀ i : Fin 8, i ≠ 0 → i ≠ i₀ → i ≠ j₀ → σ i = i ∧ s i = -1 := by
        intro i hi hi' hj'
        refine hnotgood i hi ?_
        intro hgood
        rcases hone i₀ i hi₀ne hi hi₀good hgood with h' | h'
        · exact hi' h'
        · exact hj' (h'.trans hj₀def.symm)
      have hpair : s i₀ * s j₀ = 1 := by
        have h := (hsq i₀).2
        rw [← hj₀def] at h
        rw [mul_comm] at h
        exact h
      have hTcard : ({0, i₀, j₀} : Finset (Fin 8)).card = 3 := by
        rw [Finset.card_insert_of_notMem (by simp [hi₀ne.symm, hj₀ne0.symm]),
          Finset.card_insert_of_notMem (by simp [Ne.symm hj₀ne_i₀]), Finset.card_singleton]
      have hprodT : ∏ x ∈ ({0, i₀, j₀} : Finset (Fin 8)), s x = 1 := by
        rw [Finset.prod_insert (by simp [hi₀ne.symm, hj₀ne0.symm]),
          Finset.prod_insert (by simp [Ne.symm hj₀ne_i₀]), Finset.prod_singleton, hs0, hpair]
        exact one_mul 1
      have hcompl : ∏ x ∈ Finset.univ \ ({0, i₀, j₀} : Finset (Fin 8)), s x = -1 := by
        have hconst : ∀ x ∈ Finset.univ \ ({0, i₀, j₀} : Finset (Fin 8)),
            s x = (-1 : ZMod 3) := by
          intro x hx
          have hx1 : x ≠ 0 := by
            intro h; subst h; exact (Finset.mem_sdiff.mp hx).2 (by simp)
          have hx2 : x ≠ i₀ := by
            intro h; subst h; exact (Finset.mem_sdiff.mp hx).2 (by simp)
          have hx3 : x ≠ j₀ := by
            intro h; subst h; exact (Finset.mem_sdiff.mp hx).2 (by simp)
          exact (hother x hx1 hx2 hx3).2
        have hcard : (Finset.univ \ ({0, i₀, j₀} : Finset (Fin 8))).card = 5 := by
          rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
            Fintype.card_fin, hTcard]
        calc
          ∏ x ∈ Finset.univ \ ({0, i₀, j₀} : Finset (Fin 8)), s x = (-1 : ZMod 3) ^ _ :=
            Finset.prod_eq_pow_card hconst
          _ = (-1 : ZMod 3) ^ 5 := by rw [hcard]
          _ = -1 := by decide
      have hsplit := Finset.prod_sdiff (s₁ := ({0, i₀, j₀} : Finset (Fin 8)))
        (s₂ := Finset.univ) (f := s) (by simp)
      rw [hcompl, hprodT] at hsplit
      rw [hprod8] at hsplit
      exact absurd hsplit (by decide)
  ·
    exfalso
    have hconst : ∏ i : Fin 7, s i.succ = ∏ _i : Fin 7, (-1 : ZMod 3) :=
      Finset.prod_congr rfl fun i _ =>
        (hnotgood i.succ i.succ_ne_zero fun h => hg ⟨i.succ, i.succ_ne_zero, h⟩).2
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hconst
    rw [hconst] at hprod
    exact absurd hprod (by decide)

end CFSG.StandardType.FrameRoute.FS81

end
