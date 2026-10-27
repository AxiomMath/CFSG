module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel

public section

namespace CFSG.StandardType

private lemma l6m9_det_of_mul (N C : Matrix (Fin 9) (Fin 9) ℤ) (d : ℤ)
    (h : N * C = d • 1) (hd : ¬ (3 : ℤ) ∣ d) : ¬ (3 : ℤ) ∣ C.det := by
  intro hdiv
  have hdet : N.det * C.det = d ^ 9 := by
    have h := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one] at h
    exact h
  have hpow : (3 : ℤ) ∣ d ^ 9 := by
    rw [← hdet]
    exact dvd_mul_of_dvd_right hdiv N.det
  exact hd (Int.Prime.dvd_pow' Nat.prime_three hpow)

private lemma l6m9_det_A : ¬ (3 : ℤ) ∣ (CartanMatrix.A 9).det :=
  l6m9_det_of_mul
    (!![9, 8, 7, 6, 5, 4, 3, 2, 1;
       8, 16, 14, 12, 10, 8, 6, 4, 2;
       7, 14, 21, 18, 15, 12, 9, 6, 3;
       6, 12, 18, 24, 20, 16, 12, 8, 4;
       5, 10, 15, 20, 25, 20, 15, 10, 5;
       4, 8, 12, 16, 20, 24, 18, 12, 6;
       3, 6, 9, 12, 15, 18, 21, 14, 7;
       2, 4, 6, 8, 10, 12, 14, 16, 8;
       1, 2, 3, 4, 5, 6, 7, 8, 9])
    (CartanMatrix.A 9) 10 (by decide +kernel) (by norm_num)

private lemma l6m9_det_B : ¬ (3 : ℤ) ∣ (CartanMatrix.B 9).det :=
  l6m9_det_of_mul
    (!![2, 2, 2, 2, 2, 2, 2, 2, 2;
       2, 4, 4, 4, 4, 4, 4, 4, 4;
       2, 4, 6, 6, 6, 6, 6, 6, 6;
       2, 4, 6, 8, 8, 8, 8, 8, 8;
       2, 4, 6, 8, 10, 10, 10, 10, 10;
       2, 4, 6, 8, 10, 12, 12, 12, 12;
       2, 4, 6, 8, 10, 12, 14, 14, 14;
       2, 4, 6, 8, 10, 12, 14, 16, 16;
       1, 2, 3, 4, 5, 6, 7, 8, 9])
    (CartanMatrix.B 9) 2 (by decide +kernel) (by norm_num)

private lemma l6m9_det_C : ¬ (3 : ℤ) ∣ (CartanMatrix.C 9).det :=
  l6m9_det_of_mul
    (!![2, 2, 2, 2, 2, 2, 2, 2, 1;
       2, 4, 4, 4, 4, 4, 4, 4, 2;
       2, 4, 6, 6, 6, 6, 6, 6, 3;
       2, 4, 6, 8, 8, 8, 8, 8, 4;
       2, 4, 6, 8, 10, 10, 10, 10, 5;
       2, 4, 6, 8, 10, 12, 12, 12, 6;
       2, 4, 6, 8, 10, 12, 14, 14, 7;
       2, 4, 6, 8, 10, 12, 14, 16, 8;
       2, 4, 6, 8, 10, 12, 14, 16, 9])
    (CartanMatrix.C 9) 2 (by decide +kernel) (by norm_num)

private lemma l6m9_det_D : ¬ (3 : ℤ) ∣ (CartanMatrix.D 9).det :=
  l6m9_det_of_mul
    (!![4, 4, 4, 4, 4, 4, 4, 2, 2;
       4, 8, 8, 8, 8, 8, 8, 4, 4;
       4, 8, 12, 12, 12, 12, 12, 6, 6;
       4, 8, 12, 16, 16, 16, 16, 8, 8;
       4, 8, 12, 16, 20, 20, 20, 10, 10;
       4, 8, 12, 16, 20, 24, 24, 12, 12;
       4, 8, 12, 16, 20, 24, 28, 14, 14;
       2, 4, 6, 8, 10, 12, 14, 9, 7;
       2, 4, 6, 8, 10, 12, 14, 7, 9])
    (CartanMatrix.D 9) 4 (by decide +kernel) (by norm_num)

private lemma l6m9_A9_off :
    ∀ a b : Fin 9, a ≠ b →
      (((CoxeterMatrix.A 9).M a b = 2 ∧ CartanMatrix.A 9 a b = 0) ∨
       ((CoxeterMatrix.A 9).M a b = 3 ∧ CartanMatrix.A 9 a b = -1)) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
      | exact absurd rfl hab
      | decide +kernel

private lemma l6m9_B9_off :
    ∀ a b : Fin 9, a ≠ b → ¬ ((a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7)) →
      (((CoxeterMatrix.B 9).M a b = 2 ∧ CartanMatrix.B 9 a b = 0) ∨
       ((CoxeterMatrix.B 9).M a b = 3 ∧ CartanMatrix.B 9 a b = -1)) := by
  intro a b hab hdbl
  fin_cases a <;> fin_cases b <;>
    first
      | exact absurd (by decide) hdbl
      | exact absurd rfl hab
      | decide +kernel

private lemma l6m9_C9_off :
    ∀ a b : Fin 9, a ≠ b → ¬ ((a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7)) →
      (((CoxeterMatrix.B 9).M a b = 2 ∧ CartanMatrix.C 9 a b = 0) ∨
       ((CoxeterMatrix.B 9).M a b = 3 ∧ CartanMatrix.C 9 a b = -1)) := by
  intro a b hab hdbl
  fin_cases a <;> fin_cases b <;>
    first
      | exact absurd (by decide) hdbl
      | exact absurd rfl hab
      | decide +kernel

private lemma l6m9_D9_off :
    ∀ a b : Fin 9, a ≠ b →
      (((ggCoxeterMatrixD 9).M a b = 2 ∧ CartanMatrix.D 9 a b = 0) ∨
       ((ggCoxeterMatrixD 9).M a b = 3 ∧ CartanMatrix.D 9 a b = -1)) := by
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    first
      | exact absurd rfl hab
      | decide +kernel

private lemma l6m9_card_ne {Λ : Type} [Fintype Λ] (hcard : Fintype.card Λ = 9)
    {k : ℕ} (e : Fin k ≃ Λ) (hk : k ≠ 9) : False := by
  have h := Fintype.card_congr e
  rw [Fintype.card_fin, hcard] at h
  exact hk h

private lemma l6m9_not_dvd_det {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (hcard : Fintype.card Λ = 9) {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) : ¬ (3 : ℤ) ∣ C.det := by
  unfold GGIsWeylMatrix at hM
  rcases hM with ⟨n, e, hn, hABD⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩ | ⟨e, -⟩
  · rcases hABD with hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩
    ·
      have hn9 : n = 9 := by
        have h := Fintype.card_congr e
        rwa [Fintype.card_fin, hcard] at h
      subst n
      have hMe : ∀ a b : Fin 9, M (e a) (e b) = (CoxeterMatrix.A 9).M a b := by
        intro a b
        rw [hA, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have hCsub : C.submatrix e e = CartanMatrix.A 9 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Matrix.submatrix_apply, CartanMatrix.A, hC.1]
        · have hne : e a ≠ e b := fun hh => hab (e.injective hh)
          have hval := hC.2 (e a) (e b) hne
          rw [hMe a b] at hval
          have htarget := l6m9_A9_off a b hab
          rcases hval with ⟨hM2, hc, -⟩ | ⟨hM3, hc, -⟩ | ⟨hM4, -⟩ | ⟨hM6, -⟩
          · rcases htarget with ⟨-, hA'⟩ | ⟨hMlab, -⟩
            · rw [Matrix.submatrix_apply, hc, hA']
            · omega
          · rcases htarget with ⟨hMlab, -⟩ | ⟨-, hA'⟩
            · omega
            · rw [Matrix.submatrix_apply, hc, hA']
          · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
          · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
      rw [← Matrix.det_submatrix_equiv_self e C, hCsub]
      exact l6m9_det_A
    ·
      have hn9 : n = 9 := by
        have h := Fintype.card_congr e
        rwa [Fintype.card_fin, hcard] at h
      subst n
      have hMe : ∀ a b : Fin 9, M (e a) (e b) = (CoxeterMatrix.B 9).M a b := by
        intro a b
        rw [hB, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have hne78 : e (7 : Fin 9) ≠ e (8 : Fin 9) :=
        fun hh => (by decide : (7 : Fin 9) ≠ 8) (e.injective hh)
      have hval78 := hC.2 (e (7 : Fin 9)) (e (8 : Fin 9)) hne78
      rw [hMe 7 8, show (CoxeterMatrix.B 9).M (7 : Fin 9) (8 : Fin 9) = 4 by decide +kernel]
        at hval78
      have hprod : C (e 7) (e 8) * C (e 8) (e 7) = 2 ∧ C (e 7) (e 8) < 0 ∧
          C (e 8) (e 7) < 0 := by
        rcases hval78 with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h1, h2, h3⟩ | ⟨h, -⟩
        · exact absurd h (by norm_num)
        · exact absurd h (by norm_num)
        · exact ⟨h1, h2, h3⟩
        · exact absurd h (by norm_num)
      have horient : (C (e 7) (e 8) = -1 ∧ C (e 8) (e 7) = -2) ∨
          (C (e 7) (e 8) = -2 ∧ C (e 8) (e 7) = -1) := by
        have hx : C (e 7) (e 8) < 0 := hprod.2.1
        have hy : C (e 8) (e 7) < 0 := hprod.2.2
        have h1 : C (e 7) (e 8) * (-1) ≤ C (e 7) (e 8) * C (e 8) (e 7) :=
          mul_le_mul_of_nonpos_left (by omega : C (e 8) (e 7) ≤ -1) (le_of_lt hx)
        have hxge : -2 ≤ C (e 7) (e 8) := by nlinarith [hprod.1, h1]
        have hx2 : C (e 7) (e 8) = -1 ∨ C (e 7) (e 8) = -2 := by omega
        rcases hx2 with h | h
        · exact Or.inl ⟨h, by nlinarith [hprod.1, h]⟩
        · exact Or.inr ⟨h, by nlinarith [hprod.1, h]⟩
      rcases horient with ⟨h78, h87⟩ | ⟨h78, h87⟩
      ·
        have hCsub : C.submatrix e e = CartanMatrix.C 9 := by
          ext a b
          by_cases hab : a = b
          · subst hab
            simp [Matrix.submatrix_apply, CartanMatrix.C, hC.1]
          · have hne : e a ≠ e b := fun hh => hab (e.injective hh)
            have hval := hC.2 (e a) (e b) hne
            rw [hMe a b] at hval
            by_cases hdbl : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7)
            · rcases hdbl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · simp only [Matrix.submatrix_apply]
                rw [show (CartanMatrix.C 9) (7 : Fin 9) (8 : Fin 9) = -1 by decide +kernel]
                exact h78
              · simp only [Matrix.submatrix_apply]
                rw [show (CartanMatrix.C 9) (8 : Fin 9) (7 : Fin 9) = -2 by decide +kernel]
                exact h87
            · have htarget := l6m9_C9_off a b hab hdbl
              rcases hval with ⟨hM2, hc, -⟩ | ⟨hM3, hc, -⟩ | ⟨hM4, -⟩ | ⟨hM6, -⟩
              · rcases htarget with ⟨-, hB⟩ | ⟨hMlab, -⟩
                · rw [Matrix.submatrix_apply, hc, hB]
                · omega
              · rcases htarget with ⟨hMlab, -⟩ | ⟨-, hB⟩
                · omega
                · rw [Matrix.submatrix_apply, hc, hB]
              · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
              · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
        rw [← Matrix.det_submatrix_equiv_self e C, hCsub]
        exact l6m9_det_C
      ·
        have hCsub : C.submatrix e e = CartanMatrix.B 9 := by
          ext a b
          by_cases hab : a = b
          · subst hab
            simp [Matrix.submatrix_apply, CartanMatrix.B, hC.1]
          · have hne : e a ≠ e b := fun hh => hab (e.injective hh)
            have hval := hC.2 (e a) (e b) hne
            rw [hMe a b] at hval
            by_cases hdbl : (a = 7 ∧ b = 8) ∨ (a = 8 ∧ b = 7)
            · rcases hdbl with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
              · simp only [Matrix.submatrix_apply]
                rw [show (CartanMatrix.B 9) (7 : Fin 9) (8 : Fin 9) = -2 by decide +kernel]
                exact h78
              · simp only [Matrix.submatrix_apply]
                rw [show (CartanMatrix.B 9) (8 : Fin 9) (7 : Fin 9) = -1 by decide +kernel]
                exact h87
            · have htarget := l6m9_B9_off a b hab hdbl
              rcases hval with ⟨hM2, hc, -⟩ | ⟨hM3, hc, -⟩ | ⟨hM4, -⟩ | ⟨hM6, -⟩
              · rcases htarget with ⟨-, hB⟩ | ⟨hMlab, -⟩
                · rw [Matrix.submatrix_apply, hc, hB]
                · omega
              · rcases htarget with ⟨hMlab, -⟩ | ⟨-, hB⟩
                · omega
                · rw [Matrix.submatrix_apply, hc, hB]
              · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
              · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
        rw [← Matrix.det_submatrix_equiv_self e C, hCsub]
        exact l6m9_det_B
    ·
      have hn9 : n = 9 := by
        have h := Fintype.card_congr e
        rwa [Fintype.card_fin, hcard] at h
      subst n
      have hMe : ∀ a b : Fin 9, M (e a) (e b) = (ggCoxeterMatrixD 9).M a b := by
        intro a b
        rw [hD, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      have hCsub : C.submatrix e e = CartanMatrix.D 9 := by
        ext a b
        by_cases hab : a = b
        · subst hab
          simp [Matrix.submatrix_apply, CartanMatrix.D, hC.1]
        · have hne : e a ≠ e b := fun hh => hab (e.injective hh)
          have hval := hC.2 (e a) (e b) hne
          rw [hMe a b] at hval
          have htarget := l6m9_D9_off a b hab
          rcases hval with ⟨hM2, hc, -⟩ | ⟨hM3, hc, -⟩ | ⟨hM4, -⟩ | ⟨hM6, -⟩
          · rcases htarget with ⟨-, hD'⟩ | ⟨hMlab, -⟩
            · rw [Matrix.submatrix_apply, hc, hD']
            · omega
          · rcases htarget with ⟨hMlab, -⟩ | ⟨-, hD'⟩
            · omega
            · rw [Matrix.submatrix_apply, hc, hD']
          · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
          · rcases htarget with ⟨hMlab, -⟩ | ⟨hMlab', -⟩ <;> omega
      rw [← Matrix.det_submatrix_equiv_self e C, hCsub]
      exact l6m9_det_D
  · exact (l6m9_card_ne hcard e (by decide : (6 : ℕ) ≠ 9)).elim
  · exact (l6m9_card_ne hcard e (by decide : (7 : ℕ) ≠ 9)).elim
  · exact (l6m9_card_ne hcard e (by decide : (8 : ℕ) ≠ 9)).elim
  · exact (l6m9_card_ne hcard e (by decide : (4 : ℕ) ≠ 9)).elim
  · exact (l6m9_card_ne hcard e (by decide : (2 : ℕ) ≠ 9)).elim

theorem ggMaxRank_nine_indep {p : ℕ} [Fact p.Prime] (hp : p = 3) {Λ : Type} [Fintype Λ]
    [DecidableEq Λ] (hcard : Fintype.card Λ = 9) {M : CoxeterMatrix Λ} {C : Matrix Λ Λ ℤ}
    (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = ((C i j : ℤ) : ZMod p)) :
    LinearIndependent (ZMod p) h := by
  subst hp
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hnot : ¬ (3 : ℤ) ∣ C.det := l6m9_not_dvd_det hcard hM hC
  have hdet : (C.map (Int.castRingHom (ZMod 3))).det ≠ 0 := by
    rw [show (C.map (Int.castRingHom (ZMod 3))).det = ((C.det : ℤ) : ZMod 3) from
      ((Int.castRingHom (ZMod 3)).map_det C).symm]
    exact fun h0 => hnot ((ZMod.intCast_zmod_eq_zero_iff_dvd C.det 3).mp h0)
  have hmv : Matrix.mulVec (C.map (Int.castRingHom (ZMod 3))) g = 0 := by
    ext i
    have h := congrArg (α i) hg
    simp only [map_zero, map_sum, map_smul, hpair, smul_eq_mul] at h
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply, ← h]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hg0 : g = 0 := by
    apply Matrix.mulVec_injective_of_det_ne_zero hdet
    rw [hmv, Matrix.mulVec_zero]
  intro i
  rw [hg0]
  rfl

end CFSG.StandardType

end
