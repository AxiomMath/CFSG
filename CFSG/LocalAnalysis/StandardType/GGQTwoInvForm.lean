module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabel
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType
public import CFSG.LocalAnalysis.StandardType.GGQTwoLin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private def ggQ2x_sgn (n : ℕ) (i : Fin n) : ZMod 3 :=
  if (i : ℕ) + 1 < n then 1 else -1

private lemma ggQ2x_sgn_ne_zero (n : ℕ) (i : Fin n) : ggQ2x_sgn n i ≠ 0 := by
  unfold ggQ2x_sgn
  split <;> decide

private lemma ggQ2x_Bn_three {n : ℕ} {i j : Fin n} (h : CoxeterMatrix.B n i j = 3) :
    ggQ2x_sgn n i = ggQ2x_sgn n j := by
  unfold ggQ2x_sgn
  rw [CoxeterMatrix.B] at h
  simp only [CoxeterMatrix.M, Matrix.of_apply] at h
  split_ifs at h with hij hdouble hsimple
  · omega
  · omega
  · have hi : (i : ℕ) ≠ n - 1 := by
      intro hi
      rcases hsimple with hji | hij'
      · have : (j : ℕ) = n - 2 := by omega
        exact hdouble (Or.inl ⟨hi, this⟩)
      · omega
    have hj : (j : ℕ) ≠ n - 1 := by
      intro hj
      rcases hsimple with hji | hij'
      · omega
      · have : (i : ℕ) = n - 2 := by omega
        exact hdouble (Or.inr ⟨hj, this⟩)
    rw [if_pos (by omega : (i : ℕ) + 1 < n), if_pos (by omega : (j : ℕ) + 1 < n)]
  · omega

private lemma ggQ2x_Bn_four {n : ℕ} {i j : Fin n} (h : CoxeterMatrix.B n i j = 4) :
    ggQ2x_sgn n i = -ggQ2x_sgn n j := by
  unfold ggQ2x_sgn
  rw [CoxeterMatrix.B] at h
  simp only [CoxeterMatrix.M, Matrix.of_apply] at h
  split_ifs at h with hij hdouble hsimple
  · omega
  · rcases hdouble with ⟨hi, hj⟩ | ⟨hj, hi⟩
    · rw [if_neg (by omega : ¬ (i : ℕ) + 1 < n), if_pos (by omega : (j : ℕ) + 1 < n)]
    · rw [if_neg (by omega : ¬ (j : ℕ) + 1 < n), if_pos (by omega : (i : ℕ) + 1 < n)]
      decide
  · omega
  · omega

private lemma ggQ2x_Bn_ne_six (n : ℕ) (i j : Fin n) : CoxeterMatrix.B n i j ≠ 6 := by
  intro h
  rw [CoxeterMatrix.B] at h
  simp only [CoxeterMatrix.M, Matrix.of_apply] at h
  split_ifs at h <;> omega

private def ggQ2x_sgn4 (i : Fin 4) : ZMod 3 := if (i : ℕ) < 2 then 1 else -1

private lemma ggQ2x_sgn4_ne_zero (i : Fin 4) : ggQ2x_sgn4 i ≠ 0 := by
  fin_cases i <;> decide

private lemma ggQ2x_F4_three {i j : Fin 4} (h : CoxeterMatrix.F₄ i j = 3) :
    ggQ2x_sgn4 i = ggQ2x_sgn4 j := by
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

private lemma ggQ2x_F4_four {i j : Fin 4} (h : CoxeterMatrix.F₄ i j = 4) :
    ggQ2x_sgn4 i = -ggQ2x_sgn4 j := by
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

private lemma ggQ2x_F4_ne_six (i j : Fin 4) : CoxeterMatrix.F₄ i j ≠ 6 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ggQ2x_symmetrizer {ι : Type} [Fintype ι] (M : CoxeterMatrix ι) (C : Matrix ι ι ℤ)
    (hC : GGIntCartan M C) (s : ι → ZMod 3)
    (h3 : ∀ i j, i ≠ j → M i j = 3 → s i = s j)
    (h4 : ∀ i j, i ≠ j → M i j = 4 → s i = -s j)
    (h6 : ∀ i j, i ≠ j → M i j ≠ 6) :
    ∀ i j, s i * (C i j : ZMod 3) = s j * (C j i : ZMod 3) := by
  intro i j
  by_cases hij : i = j
  · subst hij; rw [hC.1]
  · rcases hC.2 i j hij with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, h1, h2, h3c⟩ |
      ⟨hm, h1, h2, h3c⟩
    · rw [h1, h2]; ring
    · have he : (C i j : ZMod 3) = (C j i : ZMod 3) := by rw [h1, h2]
      rw [he, h3 i j hij hm]
    · have hsum : C i j + C j i = -3 := by
        have hle : C i j + C j i ≤ -2 := by omega
        have hge : -3 ≤ C i j + C j i := by
          have hp : 0 ≤ (C i j + 1) * (C j i + 1) :=
            mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
          nlinarith [h1, hp]
        have hne : C i j + C j i ≠ -2 := by
          intro h2'
          nlinarith [h1, h2', sq_nonneg (C i j - C j i)]
        omega
      have hcast : (C i j : ZMod 3) = -(C j i : ZMod 3) := by
        have h0 : ((C i j + C j i : ℤ) : ZMod 3) = 0 := by
          rw [hsum]; decide
        rw [Int.cast_add] at h0
        exact eq_neg_of_add_eq_zero_left h0
      rw [hcast, h4 i j hij hm]
      exact neg_mul_neg (s j) (↑(C j i) : ZMod 3)
    · exact absurd hm (h6 i j hij)

private theorem ggQ2x_cartan_symm_of_simple {ι : Type} [Fintype ι] (M : CoxeterMatrix ι)
    (C : Matrix ι ι ℤ) (hC : GGIntCartan M C) (hval : ∀ i j, M i j ≠ 4 ∧ M i j ≠ 6) :
    ∀ i j, C i j = C j i := by
  intro i j
  by_cases hij : i = j
  · subst hij; rw [hC.1]
  · rcases hC.2 i j hij with ⟨hm, h1, h2⟩ | ⟨hm, h1, h2⟩ | ⟨hm, -, -, -⟩ | ⟨hm, -, -, -⟩
    · rw [h1, h2]
    · rw [h1, h2]
    · exact absurd hm (hval i j).1
    · exact absurd hm (hval i j).2

private lemma ggQ2x_A_values (n : ℕ) (i j : Fin n) :
    CoxeterMatrix.A n i j ≠ 4 ∧ CoxeterMatrix.A n i j ≠ 6 := by
  rw [CoxeterMatrix.A]
  simp only [CoxeterMatrix.M, Matrix.of_apply]
  split_ifs <;> omega

private lemma ggQ2x_D_values (n : ℕ) (i j : Fin n) :
    ggCoxeterMatrixD n i j ≠ 4 ∧ ggCoxeterMatrixD n i j ≠ 6 := by
  rw [ggCoxeterMatrixD_apply]
  split_ifs <;> omega

private lemma ggQ2x_E6_values (i j : Fin 6) :
    CoxeterMatrix.E₆ i j ≠ 4 ∧ CoxeterMatrix.E₆ i j ≠ 6 := by
  fin_cases i <;> fin_cases j <;> decide

private lemma ggQ2x_E7_values (i j : Fin 7) :
    CoxeterMatrix.E₇ i j ≠ 4 ∧ CoxeterMatrix.E₇ i j ≠ 6 := by
  fin_cases i <;> fin_cases j <;> decide

private lemma ggQ2x_E8_values (i j : Fin 8) :
    CoxeterMatrix.E₈ i j ≠ 4 ∧ CoxeterMatrix.E₈ i j ≠ 6 := by
  fin_cases i <;> fin_cases j <;> decide

private theorem ggQ2x_symmetrizer_weyl {ι : Type} [Fintype ι] (M : CoxeterMatrix ι)
    (C : Matrix ι ι ℤ) (hM : GGIsWeylMatrix M) (hC : GGIntCartan M C)
    (hcard : 4 ≤ Fintype.card ι) :
    ∃ s : ι → ZMod 3, (∀ i, s i ≠ 0) ∧
      ∀ i j, s i * (C i j : ZMod 3) = s j * (C j i : ZMod 3) := by
  classical
  rcases hM with ⟨n, e, hn, hA | ⟨hn2, hB⟩ | ⟨hn4, hD⟩⟩ | ⟨e, hE6⟩ | ⟨e, hE7⟩ | ⟨e, hE8⟩ |
    ⟨e, hF4⟩ | ⟨e, hG2⟩
  · refine ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩
    have hval : ∀ i j, M i j ≠ 4 ∧ M i j ≠ 6 := by
      intro i j
      rw [hA, CoxeterMatrix.reindex_apply]
      exact ggQ2x_A_values n (e.symm i) (e.symm j)
    intro i j
    rw [ggQ2x_cartan_symm_of_simple M C hC hval i j]
  · let s : ι → ZMod 3 := fun i => ggQ2x_sgn n (e.symm i)
    refine ⟨s, fun i => ggQ2x_sgn_ne_zero n _, ?_⟩
    refine ggQ2x_symmetrizer M C hC s ?_ ?_ ?_
    · intro i j hij h
      have h' : CoxeterMatrix.B n (e.symm i) (e.symm j) = 3 := by
        rw [hB, CoxeterMatrix.reindex_apply] at h; exact h
      show ggQ2x_sgn n (e.symm i) = ggQ2x_sgn n (e.symm j)
      exact ggQ2x_Bn_three h'
    · intro i j hij h
      have h' : CoxeterMatrix.B n (e.symm i) (e.symm j) = 4 := by
        rw [hB, CoxeterMatrix.reindex_apply] at h; exact h
      show ggQ2x_sgn n (e.symm i) = -ggQ2x_sgn n (e.symm j)
      exact ggQ2x_Bn_four h'
    · intro i j hij h
      have h' : CoxeterMatrix.B n (e.symm i) (e.symm j) = 6 := by
        rw [hB, CoxeterMatrix.reindex_apply] at h; exact h
      exact ggQ2x_Bn_ne_six n _ _ h'
  · refine ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩
    have hval : ∀ i j, M i j ≠ 4 ∧ M i j ≠ 6 := by
      intro i j
      rw [hD, CoxeterMatrix.reindex_apply]
      exact ggQ2x_D_values n (e.symm i) (e.symm j)
    intro i j
    rw [ggQ2x_cartan_symm_of_simple M C hC hval i j]
  · refine ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩
    have hval : ∀ i j, M i j ≠ 4 ∧ M i j ≠ 6 := by
      intro i j
      rw [hE6, CoxeterMatrix.reindex_apply]
      exact ggQ2x_E6_values (e.symm i) (e.symm j)
    intro i j
    rw [ggQ2x_cartan_symm_of_simple M C hC hval i j]
  · refine ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩
    have hval : ∀ i j, M i j ≠ 4 ∧ M i j ≠ 6 := by
      intro i j
      rw [hE7, CoxeterMatrix.reindex_apply]
      exact ggQ2x_E7_values (e.symm i) (e.symm j)
    intro i j
    rw [ggQ2x_cartan_symm_of_simple M C hC hval i j]
  · refine ⟨fun _ => 1, fun _ => one_ne_zero, ?_⟩
    have hval : ∀ i j, M i j ≠ 4 ∧ M i j ≠ 6 := by
      intro i j
      rw [hE8, CoxeterMatrix.reindex_apply]
      exact ggQ2x_E8_values (e.symm i) (e.symm j)
    intro i j
    rw [ggQ2x_cartan_symm_of_simple M C hC hval i j]
  · let s : ι → ZMod 3 := fun i => ggQ2x_sgn4 (e.symm i)
    refine ⟨s, fun i => ggQ2x_sgn4_ne_zero _, ?_⟩
    refine ggQ2x_symmetrizer M C hC s ?_ ?_ ?_
    · intro i j hij h
      have h' : CoxeterMatrix.F₄ (e.symm i) (e.symm j) = 3 := by
        rw [hF4, CoxeterMatrix.reindex_apply] at h; exact h
      show ggQ2x_sgn4 (e.symm i) = ggQ2x_sgn4 (e.symm j)
      exact ggQ2x_F4_three h'
    · intro i j hij h
      have h' : CoxeterMatrix.F₄ (e.symm i) (e.symm j) = 4 := by
        rw [hF4, CoxeterMatrix.reindex_apply] at h; exact h
      show ggQ2x_sgn4 (e.symm i) = -ggQ2x_sgn4 (e.symm j)
      exact ggQ2x_F4_four h'
    · intro i j hij h
      have h' : CoxeterMatrix.F₄ (e.symm i) (e.symm j) = 6 := by
        rw [hF4, CoxeterMatrix.reindex_apply] at h; exact h
      exact ggQ2x_F4_ne_six _ _ h'
  · exfalso
    have h2 : Fintype.card ι = 2 := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
    omega

private lemma ggQ2x_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma ggQ2x_bilin_expand {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (β : LinearMap.BilinForm (ZMod 3) V) (u v h : V) (a b : ZMod 3) :
    β (u - a • h) (v - b • h) = β u v - b * β u h - a * β h v + a * b * β h h := by
  rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
    LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right,
    LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right]
  ring

theorem ggQ2_exists_invariantForm {p : ℕ} [Fact p.Prime] (hp : p = 3) (D : GGQ2Lin p)
    (hbas : D.Basis) (h4 : 4 ≤ Fintype.card D.ι) :
    ∃ (β : LinearMap.BilinForm (ZMod p) D.V) (d : ↥D.rootPairs → ZMod p), β.IsSymm ∧
      (∀ γ, d γ ≠ 0) ∧ ∀ γ v, β γ.1.2 v = d γ * γ.1.1 v := by
  subst p
  classical
  haveI : Nonempty D.ι := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨d₀, hd₀ne, hd₀symm⟩ :=
    ggQ2x_symmetrizer_weyl D.coxeter D.cartan D.isWeyl D.isCartan h4
  let b : Basis D.ι (ZMod 3) D.V := basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  have hb : ⇑b = D.coroot := coe_basisOfLinearIndependentOfCardEqFinrank hbas.1 hbas.2
  let Mmat : Matrix D.ι D.ι (ZMod 3) := fun i j => d₀ i * (D.cartan i j : ZMod 3)
  have hMsymm : Mmat.IsSymm := Matrix.IsSymm.ext fun i j => hd₀symm j i
  let β : LinearMap.BilinForm (ZMod 3) D.V := Matrix.toBilin b Mmat
  have hβsymm : β.IsSymm := (Matrix.isSymm_toBilin_iff_isSymm b).mpr hMsymm
  have hβroot : ∀ k v, β (D.coroot k) v = d₀ k * D.root k v := by
    intro k v
    have hβk : β (D.coroot k) = d₀ k • D.root k := by
      refine b.ext fun j => ?_
      rw [congrFun hb j]
      have hβkj : β (D.coroot k) (D.coroot j) = Mmat k j := by
        have h1 : LinearMap.BilinForm.toMatrix b β = Mmat := by
          dsimp [β]; rw [LinearMap.BilinForm.toMatrix_toBilin]
        have h2 := congrFun (congrFun h1 k) j
        rw [LinearMap.BilinForm.toMatrix_apply] at h2
        rwa [congrFun hb k, congrFun hb j] at h2
      rw [hβkj]
      simp only [Mmat, LinearMap.smul_apply, smul_eq_mul, D.pairing]
    rw [hβk, LinearMap.smul_apply, smul_eq_mul]
  have hβinv : ∀ w ∈ D.weyl, ∀ u v, β (w u) (w v) = β u v := by
    let H : Subgroup (D.V ≃ₗ[ZMod 3] D.V) :=
      { carrier := {g | ∀ u v, β (g u) (g v) = β u v}
        one_mem' := by intro u v; simp
        mul_mem' := by
          intro g h hg hh u v
          have h1 : β ((g * h) u) ((g * h) v) = β (h u) (h v) := by
            rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
            exact hg (h u) (h v)
          rw [h1, hh u v]
        inv_mem' := by
          intro g hg u v
          have h := hg (g.symm u) (g.symm v)
          simp only [LinearEquiv.apply_symm_apply] at h
          exact h.symm }
    have hgen : ∀ k, D.simpleRefl k ∈ H := by
      intro k u v
      rw [GGQ2Lin.simpleRefl, Module.reflection_apply, Module.reflection_apply]
      have h1 : β u (D.coroot k) = d₀ k * D.root k u := by
        rw [hβsymm.eq u (D.coroot k), hβroot k u]
      have h2 : β (D.coroot k) v = d₀ k * D.root k v := hβroot k v
      have h3 : β (D.coroot k) (D.coroot k) = 2 * d₀ k := by
        rw [hβroot k (D.coroot k), D.root_coroot_self k]; ring
      rw [ggQ2x_bilin_expand β u v (D.coroot k) (D.root k u) (D.root k v)]
      rw [h1, h2, h3]
      ring
    have hle : D.weyl ≤ H := by
      rw [GGQ2Lin.weyl, GGQ2Lin.parab]
      exact (Subgroup.closure_le _).mpr (by rintro _ ⟨k, -, rfl⟩; exact hgen k)
    intro w hw u v
    exact hle hw u v
  let d : ↥D.rootPairs → ZMod 3 := fun γ => β γ.1.2 γ.1.2 / 2
  refine ⟨β, d, hβsymm, ?_, ?_⟩
  · intro γ
    dsimp only [d]
    obtain ⟨k, w, hw, hcor, hroot⟩ := γ.2
    have h2 : β γ.1.2 γ.1.2 = 2 * d₀ k := by
      rw [hcor]
      rw [hβinv w hw (D.coroot k) (D.coroot k)]
      rw [hβroot k (D.coroot k), D.root_coroot_self k]
      ring
    have hdγ : β γ.1.2 γ.1.2 / 2 = d₀ k := by
      rw [h2]
      exact mul_div_cancel_left₀ (d₀ k) ggQ2x_two_ne_zero
    rw [hdγ]
    exact hd₀ne k
  · intro γ v
    dsimp only [d]
    obtain ⟨k, w, hw, hcor, hroot⟩ := γ.2
    have h2 : β γ.1.2 γ.1.2 = 2 * d₀ k := by
      rw [hcor]
      rw [hβinv w hw (D.coroot k) (D.coroot k)]
      rw [hβroot k (D.coroot k), D.root_coroot_self k]
      ring
    have hdγ : β γ.1.2 γ.1.2 / 2 = d₀ k := by
      rw [h2]
      exact mul_div_cancel_left₀ (d₀ k) ggQ2x_two_ne_zero
    have h1 : β γ.1.2 v = β (D.coroot k) (w.symm v) := by
      rw [hcor]
      conv_lhs => rw [← w.apply_symm_apply v]
      exact hβinv w hw (D.coroot k) (w.symm v)
    have hroot' : γ.1.1 v = D.root k (w.symm v) := by
      rw [hroot]; rfl
    rw [h1, hβroot k (w.symm v), hroot', hdγ]

end CFSG.StandardType

end

