module

public import CFSG.Quasithin.EmptyFaithful.E22SLift
public import CFSG.RankThree.PartOne.KC.CommonEigenbasis

public section

namespace CFSG.Quasithin.E22S

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.RankThree.SubgroupLists CFSG.Open
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem exists_sl_conj (A₀ : GL (Fin 3) K) :
    ∃ g : SL(3, K), ∀ X : Matrix (Fin 3) (Fin 3) K,
      (∀ i j, i ≠ j → ((A₀ : Matrix (Fin 3) (Fin 3) K) * X *
        ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) i j = 0) →
      ∀ i j, i ≠ j → ((g : Matrix (Fin 3) (Fin 3) K) * X *
        ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K)) i j = 0 := by
  set c : K := ((Matrix.GeneralLinearGroup.det A₀ : Kˣ) : K) with hc
  have hc0 : c ≠ 0 := Units.ne_zero _
  have hdet : (A₀ : Matrix (Fin 3) (Fin 3) K).det = c := rfl
  set D : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![c⁻¹, 1, 1] with hD
  set D' : Matrix (Fin 3) (Fin 3) K := Matrix.diagonal ![c, 1, 1] with hD'
  have hDD' : D * D' = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hc0]
  have hD'D : D' * D = 1 := by
    rw [hD, hD', Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    ext i
    fin_cases i <;> simp [hc0]
  have hdetD : D.det = c⁻¹ := by
    rw [hD, Matrix.det_diagonal, Fin.prod_univ_three]
    simp
  let g : SL(3, K) := ⟨D * (A₀ : Matrix (Fin 3) (Fin 3) K), by
    rw [Matrix.det_mul, hdetD, hdet, inv_mul_cancel₀ hc0]⟩
  let h : SL(3, K) := ⟨((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * D', by
    have h1 : ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = c⁻¹ := by
      have := congrArg Matrix.det (Units.inv_mul A₀)
      rw [Matrix.det_one, Matrix.det_mul] at this
      have h2 : ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det * c = 1 := this
      exact eq_inv_of_mul_eq_one_left h2
    have h3 : D'.det = c := by
      rw [hD', Matrix.det_diagonal, Fin.prod_univ_three]
      simp
    rw [Matrix.det_mul, h1, h3, inv_mul_cancel₀ hc0]⟩
  have hgh : g * h = 1 := by
    apply Subtype.ext
    show D * (A₀ : Matrix (Fin 3) (Fin 3) K) *
      (((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * D') = 1
    have : (A₀ : Matrix (Fin 3) (Fin 3) K) * ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc D * (A₀ : Matrix (Fin 3) (Fin 3) K) *
        (((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * D')
        = D * ((A₀ : Matrix (Fin 3) (Fin 3) K) *
            ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * D' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [this, Matrix.mul_one, hDD']
  have hginv : g⁻¹ = h := inv_eq_of_mul_eq_one_right hgh
  refine ⟨g, fun X hX i j hij => ?_⟩
  have hg : ((g : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = D * (A₀ : Matrix (Fin 3) (Fin 3) K) :=
    rfl
  have hh : ((g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * D' := by rw [hginv]
  rw [hg, hh]
  have e : D * (A₀ : Matrix (Fin 3) (Fin 3) K) * X *
      (((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * D') =
      D * ((A₀ : Matrix (Fin 3) (Fin 3) K) * X *
        ((A₀⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) * D' := by
    simp only [Matrix.mul_assoc]
  rw [e, hD, hD', Matrix.mul_diagonal, Matrix.diagonal_mul, hX i j hij]
  simp

@[expose] def IsDiagIn (g x : SL(3, K)) : Prop :=
  ∀ i j, i ≠ j → ((g * x * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i j = 0

@[expose] def dg (g x : SL(3, K)) (i : Fin 3) : K :=
  ((g * x * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i i

theorem conj_eq_diagonal {g x : SL(3, K)} (h : IsDiagIn g x) :
    ((g * x * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) = Matrix.diagonal (dg g x) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [Matrix.diagonal_apply_eq]
    rfl
  · rw [Matrix.diagonal_apply_ne _ hij]
    exact h i j hij

theorem exists_frame [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    {A : Subgroup (projectiveSL 3 K)} (hA : IsElemAbelian 2 A) :
    ∃ g : SL(3, K), ∀ x ∈ invLifts A hA, IsDiagIn g x := by
  have hcomm : ∀ x ∈ invLifts A hA, ∀ y ∈ invLifts A hA, x * y = y * x := fun x hx y hy =>
    commute_of_proj_commute_two hx.2 (by
      have := hA.1.is_comm.comm ⟨proj 3 K x, hx.1⟩ ⟨proj 3 K y, hy.1⟩
      exact congrArg Subtype.val this)
  obtain ⟨A₀, hA₀⟩ := CFSG.RankThree.PartOne.exists_conj_diagonal_of_commuting_pow_eq_one
    (n := 3) (IsPrimitiveRoot.neg_one p hp2) (invLifts A hA) hcomm (fun x hx => hx.2)
  obtain ⟨g, hg⟩ := exists_sl_conj A₀
  exact ⟨g, fun x hx => hg (x : Matrix (Fin 3) (Fin 3) K) (hA₀ x hx)⟩

theorem dg_mul {g x y : SL(3, K)} (hx : IsDiagIn g x) (hy : IsDiagIn g y) (i : Fin 3) :
    dg g (x * y) i = dg g x i * dg g y i := by
  have e : g * (x * y) * g⁻¹ = (g * x * g⁻¹) * (g * y * g⁻¹) := by group
  have h1 := conj_eq_diagonal hx
  have h2 := conj_eq_diagonal hy
  unfold dg
  rw [e, Matrix.SpecialLinearGroup.coe_mul, h1, h2, Matrix.diagonal_mul_diagonal]
  simp only [Matrix.diagonal_apply_eq]

theorem dg_one (g : SL(3, K)) (i : Fin 3) : dg g 1 i = 1 := by
  unfold dg
  rw [mul_one, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  simp

theorem dg_sq {g x : SL(3, K)} (hx : IsDiagIn g x) (hx2 : x ^ 2 = 1) (i : Fin 3) :
    dg g x i * dg g x i = 1 := by
  rw [← dg_mul hx hx, ← pow_two, hx2, dg_one]

theorem dg_prod {g x : SL(3, K)} (hx : IsDiagIn g x) : ∏ i, dg g x i = 1 := by
  have h := (g * x * g⁻¹).2
  rw [conj_eq_diagonal hx, Matrix.det_diagonal] at h
  exact h

theorem dg_inj {g x y : SL(3, K)} (hx : IsDiagIn g x) (hy : IsDiagIn g y)
    (h : ∀ i, dg g x i = dg g y i) : x = y := by
  have : g * x * g⁻¹ = g * y * g⁻¹ := by
    apply Subtype.ext
    rw [conj_eq_diagonal hx, conj_eq_diagonal hy]
    congr 1
    exact funext h
  simpa using this

theorem exists_third (i j : Fin 3) (h : i ≠ j) : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
  revert i j; decide

theorem cases_three {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (l : Fin 3) :
    l = i ∨ l = j ∨ l = k := by
  revert i j k l; decide

theorem prod_three (f : Fin 3 → K) {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ∏ l, f l = f i * f j * f k := by
  have h : (Finset.univ : Finset (Fin 3)) = {i, j, k} := by
    revert i j k; decide
  rw [h, Finset.prod_insert (by simp [hij, hik]), Finset.prod_insert (by simp [hjk]),
    Finset.prod_singleton, mul_assoc]

theorem card_sign_le_two : Nat.card {e : K // e = 1 ∨ e = -1} ≤ 2 := by
  have h : {e : K | e = 1 ∨ e = -1} = {1, -1} := by
    ext e; simp
  have h2 : Nat.card {e : K // e = 1 ∨ e = -1} = ({1, -1} : Set K).ncard := by
    rw [← h, ← Nat.card_coe_set_eq]
    rfl
  rw [h2]
  calc ({1, -1} : Set K).ncard ≤ ({-1} : Set K).ncard + 1 := Set.ncard_insert_le _ _
    _ = 2 := by rw [Set.ncard_singleton]

theorem sign_vectors_eq (f g : Fin 3 → K) (hf2 : ∀ l, f l * f l = 1) (hg2 : ∀ l, g l * g l = 1)
    (hfp : ∏ l, f l = 1) (hgp : ∏ l, g l = 1) {i j : Fin 3} (hij : i ≠ j)
    (hfij : f i * f j = 1) (hgij : g i * g j = 1) (hi : f i = g i) : f = g := by
  obtain ⟨k, hki, hkj⟩ := exists_third i j hij
  have hfj : f j = f i := by
    calc f j = f j * (f i * f i) := by rw [hf2 i, mul_one]
      _ = (f i * f j) * f i := by ring
      _ = f i := by rw [hfij, one_mul]
  have hgj : g j = g i := by
    calc g j = g j * (g i * g i) := by rw [hg2 i, mul_one]
      _ = (g i * g j) * g i := by ring
      _ = g i := by rw [hgij, one_mul]
  have hfk : f k = 1 := by
    have := hfp
    rw [prod_three f hij hki.symm hkj.symm, hfij, one_mul] at this
    exact this
  have hgk : g k = 1 := by
    have := hgp
    rw [prod_three g hij hki.symm hkj.symm, hgij, one_mul] at this
    exact this
  funext l
  rcases cases_three hij hki.symm hkj.symm l with rfl | rfl | rfl
  · exact hi
  · rw [hfj, hgj, hi]
  · rw [hfk, hgk]

theorem exists_sign_neg_one [Finite K] {A : Subgroup (projectiveSL 3 K)}
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {g : SL(3, K)}
    (hg : ∀ x ∈ invLifts A hA, IsDiagIn g x) {i j : Fin 3} (hij : i ≠ j) :
    ∃ x ∈ invLifts A hA, dg g x i * dg g x j = -1 := by
  by_contra hcon
  push Not at hcon
  have hone : ∀ x ∈ invLifts A hA, dg g x i * dg g x j = 1 := by
    intro x hx
    have h2 : (dg g x i * dg g x j) * (dg g x i * dg g x j) = 1 := by
      calc (dg g x i * dg g x j) * (dg g x i * dg g x j)
          = (dg g x i * dg g x i) * (dg g x j * dg g x j) := by ring
        _ = 1 := by rw [dg_sq (hg x hx) hx.2, dg_sq (hg x hx) hx.2, one_mul]
    rcases mul_self_eq_one_iff.mp h2 with h | h
    · exact h
    · exact absurd h (hcon x hx)
  let φ : invLifts A hA → {e : K // e = 1 ∨ e = -1} := fun x =>
    ⟨dg g x i, mul_self_eq_one_iff.mp (dg_sq (hg x x.2) x.2.2 i)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hxy' : dg g x i = dg g y i := congrArg Subtype.val hxy
    apply Subtype.ext
    refine dg_inj (hg x x.2) (hg y y.2) fun l => ?_
    have := sign_vectors_eq (dg g x) (dg g y) (dg_sq (hg x x.2) x.2.2) (dg_sq (hg y y.2) y.2.2)
      (dg_prod (hg x x.2)) (dg_prod (hg y y.2)) hij (hone x x.2) (hone y y.2) hxy'
    exact congrFun this l
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 := card_le_card_invLifts hA
  have h3 : Nat.card {e : K // e = 1 ∨ e = -1} ≤ 2 := card_sign_le_two
  omega

theorem isDiagIn_of_commute [Finite K] (hK2 : (2 : K) ≠ 0) {A : Subgroup (projectiveSL 3 K)}
    (hA : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) {g : SL(3, K)}
    (hg : ∀ x ∈ invLifts A hA, IsDiagIn g x) {h : SL(3, K)}
    (hh : ∀ x ∈ invLifts A hA, h * x = x * h) : IsDiagIn g h := by
  intro i j hij
  obtain ⟨x, hx, hxij⟩ := exists_sign_neg_one hA hA4 hg hij
  have hcomm : (g * h * g⁻¹) * (g * x * g⁻¹) = (g * x * g⁻¹) * (g * h * g⁻¹) := by
    calc (g * h * g⁻¹) * (g * x * g⁻¹) = g * (h * x) * g⁻¹ := by group
      _ = g * (x * h) * g⁻¹ := by rw [hh x hx]
      _ = (g * x * g⁻¹) * (g * h * g⁻¹) := by group
  have hM0 : ((g * h * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
      ((g * x * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) =
      ((g * x * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) *
      ((g * h * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, hcomm]
  rw [conj_eq_diagonal (hg x hx)] at hM0
  have hM := congrFun (congrFun hM0 i) j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at hM
  have hdne : dg g x j - dg g x i ≠ 0 := by
    intro h0
    have hji : dg g x j = dg g x i := sub_eq_zero.mp h0
    have h1 := dg_sq (hg x hx) hx.2 i
    rw [hji] at hxij
    rw [hxij] at h1
    apply hK2
    have : (-1 : K) = 1 := h1
    linear_combination -this
  have : ((g * h * g⁻¹ : SL(3, K)) : Matrix (Fin 3) (Fin 3) K) i j * (dg g x j - dg g x i) = 0 := by
    linear_combination hM
  exact (mul_eq_zero.mp this).resolve_right hdne

end CFSG.Quasithin.E22S
