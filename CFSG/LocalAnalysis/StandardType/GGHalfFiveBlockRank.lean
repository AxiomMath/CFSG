module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveRes
public import CFSG.LocalAnalysis.StandardType.GGHalfCentSupp
public import CFSG.LocalAnalysis.StandardType.GGHalfWeylTorusCoord

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

namespace TorusSupp

theorem f2_one_add_one : (1 : F2) + 1 = 0 := by
  have h : (2 : F2) = 1 + 1 := by norm_num
  rw [← h, gf2_two]

@[expose] noncomputable def omega2 : Matrix (Fin 2) (Fin 2) F2 :=
  fun i j => if i = 0 ∧ j = 0 then 0 else 1

@[expose] noncomputable def blockEquiv : Fin 2 × Fin 3 ≃ Fin 6 where
  toFun p := ⟨2 * p.2.val + p.1.val, by omega⟩
  invFun i := (⟨i.val % 2, by omega⟩, ⟨i.val / 2, by omega⟩)
  left_inv p := by
    ext <;> simp only [Fin.val_mk] <;> omega
  right_inv i := by
    ext
    simp only [Fin.val_mk]
    omega

private theorem omega2_sq : omega2 ^ 2 = omega2 + 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega2, pow_two, Matrix.mul_apply, Fin.sum_univ_two, f2_one_add_one, gf2_two,
      Matrix.add_apply]

private theorem omega2_pow_three : omega2 ^ 3 = 1 := by
  rw [show omega2 ^ 3 = omega2 ^ 2 * omega2 by rw [pow_succ]]
  rw [omega2_sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [omega2, Matrix.mul_apply, Fin.sum_univ_two, f2_one_add_one, gf2_two, Matrix.add_apply,
      Matrix.one_apply]

private theorem omega2_ne_one : omega2 ≠ 1 := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [omega2, Matrix.one_apply] at this

private theorem omega2_sq_ne_one : omega2 ^ 2 ≠ 1 := by
  intro h
  rw [omega2_sq] at h
  have := congrFun (congrFun h 1) 1
  simp [omega2, Matrix.add_apply, Matrix.one_apply, f2_one_add_one, gf2_two] at this

theorem omega2_pow_mod (e : ℕ) : omega2 ^ e = omega2 ^ (e % 3) := by
  conv_lhs => rw [← Nat.mod_add_div e 3, pow_add, pow_mul, omega2_pow_three, one_pow, mul_one]

private theorem omega2_pow_eq_one_iff (e : ℕ) : omega2 ^ e = 1 ↔ e % 3 = 0 := by
  rw [omega2_pow_mod]
  rcases (show e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 by omega) with h | h | h
  · rw [h, pow_zero]; exact iff_of_true rfl rfl
  · rw [h, pow_one]; exact iff_of_false omega2_ne_one (by norm_num)
  · rw [h]; exact iff_of_false omega2_sq_ne_one (by norm_num)

private theorem omega2_pow_sub_one_eq_zero_iff (e : ℕ) : omega2 ^ e - 1 = 0 ↔ e % 3 = 0 := by
  rw [sub_eq_zero, omega2_pow_eq_one_iff]

private theorem isUnit_omega2 : IsUnit omega2 := by
  refine ⟨⟨omega2, omega2 ^ 2, ?_, ?_⟩, rfl⟩
  · rw [(pow_succ' omega2 2).symm, omega2_pow_three]
  · rw [(pow_succ omega2 2).symm, omega2_pow_three]

private theorem neg_one_f2 : (-1 : F2) = 1 := by
  rw [neg_eq_iff_add_eq_zero, f2_one_add_one]

private theorem neg_one_mat : (-1 : Matrix (Fin 2) (Fin 2) F2) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.one_apply, f2_one_add_one, neg_one_f2]

private theorem one_add_one_mat : (1 : Matrix (Fin 2) (Fin 2) F2) + 1 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.add_apply, Matrix.one_apply, f2_one_add_one]

private theorem omega2_sub_one_eq : omega2 - 1 = omega2 ^ 2 := by
  rw [sub_eq_add_neg, neg_one_mat]
  exact omega2_sq.symm

private theorem isUnit_omega2_sub_one : IsUnit (omega2 - 1) := by
  rw [omega2_sub_one_eq]
  exact isUnit_omega2.pow 2

private theorem omega2_sq_sub_one_eq : omega2 ^ 2 - 1 = omega2 := by
  rw [sub_eq_add_neg, neg_one_mat, omega2_sq, add_assoc, one_add_one_mat, add_zero]

private theorem isUnit_omega2_sq_sub_one : IsUnit (omega2 ^ 2 - 1) := by
  rw [omega2_sq_sub_one_eq]
  exact isUnit_omega2

theorem omega2_pow_sub_one_zero_or_isUnit (e : ℕ) :
    omega2 ^ e - 1 = 0 ∨ IsUnit (omega2 ^ e - 1) := by
  rw [omega2_pow_mod]
  rcases (show e % 3 = 0 ∨ e % 3 = 1 ∨ e % 3 = 2 by omega) with h | h | h
  · left; rw [h, pow_zero, sub_self]
  · right; rw [h, pow_one]; exact isUnit_omega2_sub_one
  · right; rw [h]; exact isUnit_omega2_sq_sub_one

private theorem toAdd_val_mod_three_eq_zero_iff (x : Multiplicative (ZMod 3)) :
    (Multiplicative.toAdd x).val % 3 = 0 ↔ x = 1 := by
  have hlt : (Multiplicative.toAdd x).val < 3 := ZMod.val_lt _
  constructor
  · intro h
    have he : (Multiplicative.toAdd x).val = 0 := by omega
    have h0 : Multiplicative.toAdd x = 0 := by
      rw [← ZMod.natCast_zmod_val (Multiplicative.toAdd x), he, Nat.cast_zero]
    have := congrArg Multiplicative.ofAdd h0
    rwa [show Multiplicative.ofAdd (Multiplicative.toAdd x) = x from rfl,
      show Multiplicative.ofAdd (0 : ZMod 3) = 1 from rfl] at this
  · intro h
    rw [h]
    simp

theorem omega2_pow_sub_one_ne_zero_iff (x : Multiplicative (ZMod 3)) :
    omega2 ^ (Multiplicative.toAdd x).val - 1 ≠ 0 ↔ x ≠ 1 := by
  rw [ne_eq, ne_eq, omega2_pow_sub_one_eq_zero_iff]
  exact not_congr (toAdd_val_mod_three_eq_zero_iff x)

theorem rank_blockDiagonal_fin2 {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F2]
    (f : ι → Matrix (Fin 2) (Fin 2) F2)
    (hinv : ∀ i, f i = 0 ∨ IsUnit (f i)) :
    (Matrix.blockDiagonal f).rank = 2 * (Finset.univ.filter fun i => f i ≠ 0).card := by
  classical
  let T : Finset ι := Finset.univ.filter fun i => f i ≠ 0
  let g : Fin 2 × T → Fin 2 × ι := fun p => (p.1, p.2.1)
  have hg : Function.Injective g := by
    intro p q h
    simp only [g, Prod.mk.injEq] at h
    exact Prod.ext h.1 (Subtype.ext h.2)
  let S : Finset (Fin 2 × ι) := (Finset.univ : Finset (Fin 2 × T)).image g
  have hS : S.card = 2 * T.card := by
    simp only [S]
    rw [Finset.card_image_of_injective _ hg, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe]
  have hsupp : Function.support (Matrix.blockDiagonal f).row ⊆ (S : Set (Fin 2 × ι)) := by
    intro x hx
    rcases x with ⟨a, i⟩
    rw [Function.mem_support] at hx
    have hi : i ∈ T := by
      by_contra hi
      have hfi : f i = 0 := by
        by_contra hne
        exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩)
      apply hx
      funext y
      rcases y with ⟨b, k⟩
      rw [Matrix.row_apply, Matrix.blockDiagonal_apply]
      by_cases hik : i = k
      · subst hik
        simp [hfi]
      · rw [if_neg (fun h => hik h)]
        simp
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(a, ⟨i, hi⟩), Finset.mem_univ _, rfl⟩)
  have hle : (Matrix.blockDiagonal f).rank ≤ 2 * T.card := by
    calc (Matrix.blockDiagonal f).rank ≤ S.card := Matrix.rank_le_card_of_support_subset _ S hsupp
      _ = 2 * T.card := hS
  have hY : (Matrix.blockDiagonal f).submatrix g g = Matrix.blockDiagonal (fun i : T => f i.1) := by
    ext p q
    rcases p with ⟨a, i⟩
    rcases q with ⟨b, j⟩
    by_cases h : i = j
    · subst h
      simp only [g, Matrix.submatrix_apply, Matrix.blockDiagonal_apply]
    · have h' : i.1 ≠ j.1 := fun hh => h (Subtype.ext hh)
      simp only [g, Matrix.submatrix_apply, Matrix.blockDiagonal_apply, h, h']
  have hdet : IsUnit (Matrix.blockDiagonal (fun i : T => f i.1)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_blockDiagonal, IsUnit.prod_iff]
    intro i _
    have hne : f i.1 ≠ 0 := (Finset.mem_filter.mp i.2).2
    exact (Matrix.isUnit_iff_isUnit_det _).mp ((hinv i.1).resolve_left hne)
  have hrank : (Matrix.blockDiagonal (fun i : T => f i.1)).rank = 2 * T.card := by
    rw [Matrix.rank_of_isUnit _ hdet, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
  have hge : 2 * T.card ≤ (Matrix.blockDiagonal f).rank := by
    calc 2 * T.card = (Matrix.blockDiagonal (fun i : T => f i.1)).rank := hrank.symm
      _ = ((Matrix.blockDiagonal f).submatrix g g).rank := by rw [hY]
      _ ≤ (Matrix.blockDiagonal f).rank := Matrix.rank_submatrix_le _ _ _
  exact le_antisymm hle hge

end TorusSupp

end CFSG.StandardType.GGHalf

end
