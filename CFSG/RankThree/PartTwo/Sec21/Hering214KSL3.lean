module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KRoot
import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67A2Diag
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering214

open Matrix
open CFSG.Assembly (IsElemAbelian)
section SL3

variable {K : Type} [Field K]

abbrev tv {i j : Fin 3} (h : i ≠ j) (t : K) : Matrix.SpecialLinearGroup (Fin 3) K :=
  Matrix.SpecialLinearGroup.transvection h t

theorem tv_val {i j : Fin 3} (h : i ≠ j) (t : K) :
    ((tv h t : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      1 + single i j t := rfl

theorem tv_mul {i j : Fin 3} (h : i ≠ j) (s t : K) : tv h s * tv h t = tv h (s + t) := by
  apply Subtype.ext
  show (1 + single i j s) * (1 + single i j t) = 1 + single i j (s + t)
  exact Matrix.transvection_mul_transvection_same (n := Fin 3) i j h s t

theorem tv_inj {i j : Fin 3} (h : i ≠ j) {s t : K} (hst : tv h s = tv h t) : s = t := by
  have := congrArg
    (fun g : Matrix.SpecialLinearGroup (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K)) i j) hst
  simpa [tv_val, Matrix.one_apply, h] using this

theorem diag_ne_zero {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : ∀ a b : Fin 3, a ≠ b → (D : Matrix (Fin 3) (Fin 3) K) a b = 0)
    (a : Fin 3) : (D : Matrix (Fin 3) (Fin 3) K) a a ≠ 0 := by
  have hdiag : (D : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun c => (D : Matrix _ _ K) c c := by
    ext c d
    by_cases hcd : c = d
    · subst hcd; simp
    · simp [hD c d hcd, Matrix.diagonal_apply_ne _ hcd]
  have hdet := D.2
  rw [hdiag, Matrix.det_diagonal] at hdet
  intro h0
  have : ∏ c, (D : Matrix (Fin 3) (Fin 3) K) c c = 0 := Finset.prod_eq_zero (Finset.mem_univ a) h0
  rw [this] at hdet
  exact zero_ne_one hdet

theorem diag_mul_tv {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : ∀ a b : Fin 3, a ≠ b → (D : Matrix (Fin 3) (Fin 3) K) a b = 0)
    {i j : Fin 3} (h : i ≠ j) (t : K) :
    D * tv h t = tv h ((D : Matrix (Fin 3) (Fin 3) K) i i *
      ((D : Matrix (Fin 3) (Fin 3) K) j j)⁻¹ * t) * D := by
  have hdiag : (D : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun c => (D : Matrix _ _ K) c c := by
    ext c d
    by_cases hcd : c = d
    · subst hcd; simp
    · simp [hD c d hcd, Matrix.diagonal_apply_ne _ hcd]
  have hj := diag_ne_zero hD j
  apply Subtype.ext
  show (D : Matrix (Fin 3) (Fin 3) K) * (1 + single i j t) =
    (1 + single i j ((D : Matrix (Fin 3) (Fin 3) K) i i *
      ((D : Matrix (Fin 3) (Fin 3) K) j j)⁻¹ * t)) * (D : Matrix (Fin 3) (Fin 3) K)
  set d : Fin 3 → K := fun c => (D : Matrix _ _ K) c c with hd
  rw [hdiag]
  ext a b
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.add_apply,
    Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.single_apply, Matrix.diagonal_apply]
  by_cases hab : a = b
  · subst hab
    have : ¬ (i = a ∧ j = a) := fun hh => h (hh.1.trans hh.2.symm)
    simp [this]
  · by_cases hij : i = a ∧ j = b
    · obtain ⟨rfl, rfl⟩ := hij
      have hj' : d j ≠ 0 := hj
      simp [hab]
      field_simp
    · simp [hab, hij]

end SL3

section Four

variable {K : Type} [Field K] [CharP K 2]

@[expose] def rootFour {i j : Fin 3} (h : i ≠ j) (ω : K) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 3) K) :=
  rootFourOf (fun t : K => tv h t) ω

theorem rootFour_spec {i j : Fin 3} (h : i ≠ j) {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1) :
    IsElemAbelian 2 (rootFour h ω) ∧ Nat.card (rootFour h ω) = 4 :=
  rootFourOf_spec (fun s t => (tv_mul h s t).symm) (fun _ _ e => tv_inj h e) hω hω1

theorem rootFour_normalized {i j : Fin 3} (h : i ≠ j) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : ∀ a b : Fin 3, a ≠ b → (D : Matrix (Fin 3) (Fin 3) K) a b = 0)
    (hi : ((D : Matrix (Fin 3) (Fin 3) K) i i) ^ 3 = 1)
    (hj : ((D : Matrix (Fin 3) (Fin 3) K) j j) ^ 3 = 1) :
    ∀ w ∈ rootFour h ω, D * w * D⁻¹ ∈ rootFour h ω := by
  have hj0 := diag_ne_zero hD j
  set lam : K := (D : Matrix (Fin 3) (Fin 3) K) i i * ((D : Matrix (Fin 3) (Fin 3) K) j j)⁻¹
    with hlam
  have hlam3 : lam ^ 3 = 1 := by
    rw [hlam, mul_pow, inv_pow, hi, hj]
    simp
  exact rootFourOf_normalized (g := fun t : K => tv h t) (fun s t => (tv_mul h s t).symm) hω
    hlam3 (fun t => by rw [diag_mul_tv hD h t, mul_inv_cancel_right])

theorem diag_entry_cube {D : Matrix.SpecialLinearGroup (Fin 3) K}
    (hD : ∀ a b : Fin 3, a ≠ b → (D : Matrix (Fin 3) (Fin 3) K) a b = 0) (h3 : D ^ 3 = 1)
    (a : Fin 3) : ((D : Matrix (Fin 3) (Fin 3) K) a a) ^ 3 = 1 := by
  have hdiag : (D : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal fun c => (D : Matrix _ _ K) c c := by
    ext c d
    by_cases hcd : c = d
    · subst hcd; simp
    · simp [hD c d hcd, Matrix.diagonal_apply_ne _ hcd]
  have h := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
    ((g : Matrix (Fin 3) (Fin 3) K)) a a) h3
  simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h
  rw [hdiag, Matrix.diagonal_pow] at h
  simpa using h

variable [Finite K]

theorem exists_four_sl3 {ω : K} (hω : ω ^ 2 + ω + 1 = 0) (hω1 : ω ≠ 1)
    (E : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K))
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hE9 : 9 ≤ Nat.card E) :
    ∃ W : Subgroup (Matrix.SpecialLinearGroup (Fin 3) K), IsElemAbelian 2 W ∧ Nat.card W = 4 ∧
      (∀ x ∈ E, ∀ w ∈ W, x * w * x⁻¹ ∈ W) ∧ ∃ x ∈ E, ∃ w ∈ W, x * w * x⁻¹ ≠ w := by
  classical
  obtain ⟨y, hy⟩ := CFSG.GH74.GLS.Stage2.Bender.Thm1.exists_diagonalizing_of_commuting_cube_one ω
    hω hω1 E hE3 hcomm
  have hDcube : ∀ x ∈ E, (y * x * y⁻¹) ^ 3 = 1 := by
    intro x hx
    have : (y * x * y⁻¹) ^ 3 = y * x ^ 3 * y⁻¹ := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [this, hE3 x hx]
    group
  have hnon : ∃ x ∈ E, ∃ i j : Fin 3, i ≠ j ∧
      ((y * x * y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i i ≠
        ((y * x * y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) j j := by
    by_contra hcon
    push Not at hcon
    have hscal : ∀ x ∈ E, ((y * x * y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((y * x * y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) 0 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
      intro x hx
      ext a b
      by_cases hab : a = b
      · subst hab
        by_cases ha0 : a = 0
        · subst ha0; simp
        · simp [(hcon x hx 0 a (Ne.symm ha0)).symm]
      · simp [hy x hx a b hab, Matrix.one_apply_ne hab]
    let f : E → (Polynomial.nthRoots 3 (1 : K)).toFinset := fun x =>
      ⟨((y * (x : Matrix.SpecialLinearGroup (Fin 3) K) * y⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0, by
        rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
        have h3 := hDcube x x.2
        have h4 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) K =>
          ((g : Matrix (Fin 3) (Fin 3) K)) 0 0) h3
        simp only [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one] at h4
        rw [hscal x x.2] at h4
        simpa [Matrix.smul_eq_diagonal_mul, Matrix.diagonal_pow, pow_succ] using h4⟩
    have hf : Function.Injective f := by
      intro x x' hxx'
      have h1 : ((y * (x : Matrix.SpecialLinearGroup (Fin 3) K) * y⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 =
          ((y * (x' : Matrix.SpecialLinearGroup (Fin 3) K) * y⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 0 :=
        congrArg Subtype.val hxx'
      have h2 : ((y * (x : Matrix.SpecialLinearGroup (Fin 3) K) * y⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
          ((y * (x' : Matrix.SpecialLinearGroup (Fin 3) K) * y⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
        rw [hscal x x.2, hscal x' x'.2, h1]
      have h3 : y * (x : Matrix.SpecialLinearGroup (Fin 3) K) * y⁻¹ =
          y * (x' : Matrix.SpecialLinearGroup (Fin 3) K) * y⁻¹ :=
        Subtype.ext h2
      exact Subtype.ext (mul_left_cancel (mul_right_cancel h3))
    have hcard := Nat.card_le_card_of_injective f hf
    have hroots : Nat.card (Polynomial.nthRoots 3 (1 : K)).toFinset ≤ 3 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      exact (Multiset.toFinset_card_le _).trans (Polynomial.card_nthRoots 3 1)
    omega
  obtain ⟨x₀, hx₀, i, j, hij, hne⟩ := hnon
  refine ⟨(rootFour hij ω).map (MulAut.conj y⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · exact CFSG.Open.IsElemAbelian.map (rootFour_spec hij hω hω1).1 _
  · rw [Subgroup.card_map_of_injective (show Function.Injective (MulAut.conj y⁻¹).toMonoidHom from
      (MulAut.conj y⁻¹).injective)]
    exact (rootFour_spec hij hω hω1).2
  · intro x hx w hw
    obtain ⟨w₀, hw₀, rfl⟩ := hw
    have hD := rootFour_normalized hij hω (D := y * x * y⁻¹) (hy x hx)
      (diag_entry_cube (hy x hx) (hDcube x hx) i) (diag_entry_cube (hy x hx) (hDcube x hx) j) w₀ hw₀
    refine ⟨_, hD, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · refine ⟨x₀, hx₀, y⁻¹ * tv hij (1 : K) * y,
      ⟨tv hij 1, Subgroup.subset_closure (Set.mem_insert _ _), ?_⟩, ?_⟩
    · simp [MulAut.conj_apply]
    · intro h
      have hD := diag_mul_tv (D := y * x₀ * y⁻¹) (hy x₀ hx₀) hij (1 : K)
      have h2 : y * x₀ * y⁻¹ * tv hij (1 : K) * (y * x₀ * y⁻¹)⁻¹ = tv hij 1 := by
        have : x₀ * (y⁻¹ * tv hij (1 : K) * y) * x₀⁻¹ = y⁻¹ * tv hij 1 * y := h
        calc y * x₀ * y⁻¹ * tv hij (1 : K) * (y * x₀ * y⁻¹)⁻¹
            = y * (x₀ * (y⁻¹ * tv hij (1 : K) * y) * x₀⁻¹) * y⁻¹ := by group
          _ = tv hij 1 := by rw [this]; group
      rw [hD, mul_inv_cancel_right] at h2
      have h3 := tv_inj hij h2
      apply hne
      have hjne := diag_ne_zero (hy x₀ hx₀) j
      have : ((y * x₀ * y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) i i *
          (((y * x₀ * y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
            Matrix (Fin 3) (Fin 3) K) j j)⁻¹ = 1 := by
        simpa using h3
      exact (mul_inv_eq_one₀ hjne).mp this

end Four

end CFSG.RankThree.PartTwo.Sec21.Hering214
