module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2dAuxForm

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.ModelFacts

private theorem levTwoS2d_dot_single {n : ℕ} (p q : Fin n) (s t : ℤ) :
    ∑ k, (((Pi.single p s : Fin n → ℤ) k : ℚ) * ((Pi.single q t : Fin n → ℤ) k : ℚ))
      = if p = q then (s : ℚ) * (t : ℚ) else 0 := by
  by_cases h : p = q
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single p]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hp; exact absurd (Finset.mem_univ p) hp
  · rw [if_neg h, Finset.sum_eq_zero]
    intro k _
    by_cases hk : k = p
    · subst hk; simp [Pi.single_eq_of_ne h]
    · simp [Pi.single_eq_of_ne hk]

private theorem levTwoS2d_gram (n : ℕ) (hn : 4 ≤ n) (a b : Fin n) :
    ∑ k, ((toStdD n (Pi.single a 1) k : ℚ) * (toStdD n (Pi.single b 1) k : ℚ))
      = (cartanD n a b : ℚ) := by
  by_cases ha : a.val + 1 < n
  · by_cases hb : b.val + 1 < n
    · rw [toStdD_single_of_lt n ha, toStdD_single_of_lt n hb]
      simp only [Pi.sub_apply, Int.cast_sub, sub_mul, mul_sub,
        Finset.sum_sub_distrib]
      rw [levTwoS2d_dot_single a b, levTwoS2d_dot_single a ⟨b.val + 1, hb⟩,
        levTwoS2d_dot_single ⟨a.val + 1, ha⟩ b,
        levTwoS2d_dot_single ⟨a.val + 1, ha⟩ ⟨b.val + 1, hb⟩]
      rw [cartanD, Matrix.of_apply]
      simp only [Fin.ext_iff]
      split_ifs <;> norm_num at * <;> omega
    · rw [toStdD_single_of_lt n ha,
        toStdD_single_of_not_lt n hb (by omega : 2 ≤ n)]
      simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add, sub_mul, 
        mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [levTwoS2d_dot_single a ⟨n - 2, by omega⟩, levTwoS2d_dot_single a b,
        levTwoS2d_dot_single ⟨a.val + 1, ha⟩ ⟨n - 2, by omega⟩,
        levTwoS2d_dot_single ⟨a.val + 1, ha⟩ b]
      rw [cartanD, Matrix.of_apply]
      simp only [Fin.ext_iff]
      split_ifs <;> norm_num at * <;> omega
  · by_cases hb : b.val + 1 < n
    · rw [toStdD_single_of_not_lt n ha (by omega : 2 ≤ n), toStdD_single_of_lt n hb]
      simp only [Pi.sub_apply, Pi.add_apply, Int.cast_sub, Int.cast_add, mul_sub,
        add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      rw [levTwoS2d_dot_single ⟨n - 2, by omega⟩ b, levTwoS2d_dot_single a b,
        levTwoS2d_dot_single ⟨n - 2, by omega⟩ ⟨b.val + 1, hb⟩,
        levTwoS2d_dot_single a ⟨b.val + 1, hb⟩]
      rw [cartanD, Matrix.of_apply]
      simp only [Fin.ext_iff]
      split_ifs <;> norm_num at * <;> omega
    · rw [toStdD_single_of_not_lt n ha (by omega : 2 ≤ n),
        toStdD_single_of_not_lt n hb (by omega : 2 ≤ n)]
      simp only [Pi.add_apply, Int.cast_add, add_mul, mul_add, Finset.sum_add_distrib]
      rw [levTwoS2d_dot_single ⟨n - 2, by omega⟩ ⟨n - 2, by omega⟩,
        levTwoS2d_dot_single ⟨n - 2, by omega⟩ b, levTwoS2d_dot_single a ⟨n - 2, by omega⟩,
        levTwoS2d_dot_single a b]
      rw [cartanD, Matrix.of_apply]
      simp only [Fin.ext_iff]
      split_ifs <;> norm_num at * <;> omega



private theorem levTwoS2d_gram_gen (n : ℕ) (hn : 4 ≤ n) (u v : Fin n → ℤ) :
    (∑ k, (toStdD n u k : ℚ) * (toStdD n v k : ℚ)) =
      ∑ a, ∑ b, (u a : ℚ) * (v b : ℚ) * (cartanD n a b : ℚ) := by
  have hbasis : ∀ a : Fin n,
      (∑ k, (toStdD n (Pi.single a 1) k : ℚ) * (toStdD n v k : ℚ)) =
        ∑ b, (v b : ℚ) * (cartanD n a b : ℚ) := by
    intro a
    let Fv : (Fin n → ℤ) →+ ℚ :=
      { toFun := fun v => ∑ k, (toStdD n (Pi.single a 1) k : ℚ) * (toStdD n v k : ℚ)
        map_zero' := by simp [toStdD_zero]
        map_add' := fun v w => by
          simp only [toStdD_add, Pi.add_apply, Int.cast_add, mul_add, Finset.sum_add_distrib] }
    let Gv : (Fin n → ℤ) →+ ℚ :=
      { toFun := fun v => ∑ b, (v b : ℚ) * (cartanD n a b : ℚ)
        map_zero' := by simp
        map_add' := fun v w => by
          simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib] }
    have hFG : Fv = Gv := by
      refine AddMonoidHom.functions_ext _ Fv Gv fun b x => ?_
      change (∑ k, (toStdD n (Pi.single a 1) k : ℚ) * (toStdD n (Pi.single b x) k : ℚ)) =
        ∑ b', ((Pi.single b x : Fin n → ℤ) b' : ℚ) * (cartanD n a b' : ℚ)
      have hs : (Pi.single b x : Fin n → ℤ) = x • Pi.single b 1 := by
        funext k; simp [Pi.single_apply]
      rw [hs, toStdD_smul]
      simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
      rw [show (∑ k, (toStdD n (Pi.single a 1) k : ℚ) * ((x : ℚ) * (toStdD n (Pi.single b 1) k : ℚ))) =
          (x : ℚ) * ∑ k, (toStdD n (Pi.single a 1) k : ℚ) *
            (toStdD n (Pi.single b 1) k : ℚ) from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
      rw [levTwoS2d_gram n hn a b]
      rw [Finset.sum_eq_single b]
      · simp
      · intro b' _ hb'; simp [Pi.single_eq_of_ne hb']
      · intro hb; exact absurd (Finset.mem_univ b) hb
    exact DFunLike.congr_fun hFG v
  let F : (Fin n → ℤ) →+ ℚ :=
    { toFun := fun u => ∑ k, (toStdD n u k : ℚ) * (toStdD n v k : ℚ)
      map_zero' := by simp [toStdD_zero]
      map_add' := fun u w => by
        simp only [toStdD_add, Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib] }
  let G : (Fin n → ℤ) →+ ℚ :=
    { toFun := fun u => ∑ a, ∑ b, (u a : ℚ) * (v b : ℚ) * (cartanD n a b : ℚ)
      map_zero' := by simp
      map_add' := fun u w => by
        simp only [Pi.add_apply, Int.cast_add, add_mul, Finset.sum_add_distrib] }
  have hFG : F = G := by
    refine AddMonoidHom.functions_ext _ F G fun a x => ?_
    change (∑ k, (toStdD n (Pi.single a x) k : ℚ) * (toStdD n v k : ℚ)) =
      ∑ a', ∑ b, ((Pi.single a x : Fin n → ℤ) a' : ℚ) * (v b : ℚ) * (cartanD n a' b : ℚ)
    have hs : (Pi.single a x : Fin n → ℤ) = x • Pi.single a 1 := by
      funext k; simp [Pi.single_apply]
    rw [hs, toStdD_smul]
    simp only [Pi.smul_apply, smul_eq_mul, Int.cast_mul]
    rw [show (∑ k, (x : ℚ) * (toStdD n (Pi.single a 1) k : ℚ) * (toStdD n v k : ℚ)) =
        (x : ℚ) * ∑ k, (toStdD n (Pi.single a 1) k : ℚ) * (toStdD n v k : ℚ) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring]
    rw [hbasis a]
    rw [show (∑ a', ∑ b, (x : ℚ) * ((Pi.single a 1 : Fin n → ℤ) a' : ℚ) * (v b : ℚ) *
          (cartanD n a' b : ℚ)) =
        (x : ℚ) * ∑ b, (v b : ℚ) * (cartanD n a b : ℚ) from by
      rw [Finset.sum_eq_single a]
      · simp only [Pi.single_eq_same, Int.cast_one]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro b _; ring
      · intro a' _ ha'
        simp [Pi.single_eq_of_ne ha']
      · intro ha; exact absurd (Finset.mem_univ a) ha]
  exact DFunLike.congr_fun hFG u



theorem levTwoS2d_form_coord (n : ℕ) (hn : 4 ≤ n) :
    ∃ κ : ℚ, 0 < κ ∧ ∀ u v : Fin n → ℤ,
      form (isFiniteType_cartanD n) (toRat u) (toRat v) =
        κ * ((∑ k, toStdD n u k * toStdD n v k : ℤ) : ℚ) := by
  refine ⟨symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩, symmetrizer_pos _ _, fun u v => ?_⟩
  have hcast : ((∑ k, toStdD n u k * toStdD n v k : ℤ) : ℚ) =
      ∑ k, (toStdD n u k : ℚ) * (toStdD n v k : ℚ) := by
    rw [Int.cast_sum]; congr 1; ext k; rw [Int.cast_mul]
  have hper : ∀ l : Fin n, form (isFiniteType_cartanD n) (toRat u) (Pi.single l 1) =
      symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩ *
        ∑ k, (cartanD n l k : ℚ) * (u k : ℚ) := by
    intro l
    rw [form_single_right, levTwoS2d_symmetrizer_const n hn l]
    simp only [toRat_apply]
  rw [hcast, levTwoS2d_gram_gen n hn u v, form_eq_sum]
  simp only [hper, toRat_apply]
  rw [show (∑ l, (v l : ℚ) * (symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩ *
        ∑ k, (cartanD n l k : ℚ) * (u k : ℚ))) =
      symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩ *
      ∑ l, ∑ k, (v l : ℚ) * (cartanD n l k : ℚ) * (u k : ℚ) from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro l _
    rw [show (v l : ℚ) * (symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩ *
          ∑ k, (cartanD n l k : ℚ) * (u k : ℚ)) =
        symmetrizer (isFiniteType_cartanD n) ⟨0, by omega⟩ *
          ((v l : ℚ) * ∑ k, (cartanD n l k : ℚ) * (u k : ℚ)) by ring]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro k _; ring]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro k _
  apply Finset.sum_congr rfl; intro l _
  rw [show (cartanD n l k : ℚ) = (cartanD n k l : ℚ) by rw [cartanD_symm]]
  ring

end CFSG.StandardType.LevTwo
