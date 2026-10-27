module

public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import Mathlib.FieldTheory.Finite.GaloisField

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429F

open Matrix
open scoped MatrixGroups

@[expose] def rhoM : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![0, 1; 1, 1]

@[expose] def rep3M : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  !![0, 1, 0, 0, 0, 0;
     1, 1, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 1, 0, 0;
     0, 0, 0, 0, 0, 1;
     0, 0, 0, 0, 1, 1]

theorem natCard_gf4 : Nat.card (GaloisField 2 2) = 4 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

theorem two_eq_zero_gf4 : (2 : GaloisField 2 2) = 0 := by
  exact_mod_cast CharP.cast_eq_zero (GaloisField 2 2) 2

theorem pow_four_gf4 (x : GaloisField 2 2) : x ^ 4 = x := by
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have h := FiniteField.pow_card x
  rw [← Nat.card_eq_fintype_card, natCard_gf4] at h
  exact h

theorem exists_omega : ∃ ω : GaloisField 2 2, ω ≠ 0 ∧ ω ≠ 1 := by
  classical
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  by_contra hcon
  have hcon' : ∀ ω : GaloisField 2 2, ω ≠ 0 → ω = 1 := fun ω h0 => by
    by_contra h1
    exact hcon ⟨ω, h0, h1⟩
  have hsub : (Finset.univ : Finset (GaloisField 2 2)) ⊆ {0, 1} := by
    intro x _
    by_cases hx : x = 0
    · simp [hx]
    · simp [hcon' x hx]
  have h1 := Finset.card_le_card hsub
  have h2 : ({0, 1} : Finset (GaloisField 2 2)).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, natCard_gf4] at h1
  omega

@[expose] noncomputable def omega4 : GaloisField 2 2 := exists_omega.choose

theorem omega4_ne_zero : omega4 ≠ 0 := exists_omega.choose_spec.1

theorem omega4_ne_one : omega4 ≠ 1 := exists_omega.choose_spec.2

theorem omega4_cube : omega4 ^ 3 = 1 := by
  have h4 : omega4 ^ 4 = omega4 := pow_four_gf4 omega4
  apply mul_left_cancel₀ omega4_ne_zero
  calc omega4 * omega4 ^ 3 = omega4 ^ 4 := by ring
    _ = omega4 := h4
    _ = omega4 * 1 := by ring

theorem omega4_spec : omega4 ^ 2 + omega4 + 1 = 0 := by
  have h3 : (omega4 - 1) * (omega4 ^ 2 + omega4 + 1) = 0 := by
    linear_combination omega4_cube
  rcases mul_eq_zero.1 h3 with h | h
  · exact absurd (sub_eq_zero.1 h) omega4_ne_one
  · exact h

theorem omega4_sq : omega4 * omega4 = omega4 + 1 := by
  linear_combination omega4_spec - (omega4 + 1) * two_eq_zero_gf4

theorem linIndep_one_omega : LinearIndependent (ZMod 2) ![(1 : GaloisField 2 2), omega4] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have hs : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hs s with rfl | rfl <;> rcases hs t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · rw [zero_smul, one_smul, zero_add] at hst
    exact absurd hst omega4_ne_zero
  · rw [one_smul, zero_smul, add_zero] at hst
    exact absurd hst one_ne_zero
  · rw [one_smul, one_smul] at hst
    exact absurd (by linear_combination hst - two_eq_zero_gf4) omega4_ne_one

@[expose] noncomputable def basisGF4 : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
  basisOfLinearIndependentOfCardEqFinrank linIndep_one_omega
    (by rw [Fintype.card_fin, GaloisField.finrank 2 (by norm_num)])

theorem basisGF4_zero : basisGF4 0 = 1 := by simp [basisGF4]

theorem basisGF4_one : basisGF4 1 = omega4 := by simp [basisGF4]

@[expose] noncomputable def gf4Emb : GaloisField 2 2 →+* Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  (Algebra.leftMulMatrix basisGF4).toRingHom

theorem gf4Emb_omega : gf4Emb omega4 = rhoM := by
  ext i j
  show Algebra.leftMulMatrix basisGF4 omega4 i j = rhoM i j
  rw [Algebra.leftMulMatrix_eq_repr_mul]
  fin_cases j
  · have h : omega4 * basisGF4 0 = basisGF4 1 := by
      rw [basisGF4_zero, basisGF4_one, mul_one]
    fin_cases i <;> simp [h, rhoM, Module.Basis.repr_self, Finsupp.single_apply]
  · have h : omega4 * basisGF4 1 = basisGF4 1 + basisGF4 0 := by
      rw [basisGF4_zero, basisGF4_one, omega4_sq, add_comm]
    fin_cases i <;> simp [h, rhoM, map_add, Module.Basis.repr_self, Finsupp.single_apply]

theorem gf4Emb_injective : Function.Injective gf4Emb := gf4Emb.injective

theorem exists_gf4Emb_of_commute (A : Matrix (Fin 2) (Fin 2) (ZMod 2)) (h : A * rhoM = rhoM * A) :
    ∃ x : GaloisField 2 2, gf4Emb x = A := by
  have key : ∀ B : Matrix (Fin 2) (Fin 2) (ZMod 2), B * rhoM = rhoM * B →
      B = 0 ∨ B = 1 ∨ B = rhoM ∨ B = rhoM * rhoM := by
    decide +kernel
  rcases key A h with rfl | rfl | rfl | rfl
  · exact ⟨0, map_zero gf4Emb⟩
  · exact ⟨1, map_one gf4Emb⟩
  · exact ⟨omega4, gf4Emb_omega⟩
  · exact ⟨omega4 * omega4, by rw [map_mul, gf4Emb_omega]⟩

@[expose] noncomputable def blockM (Y : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) :
    Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) (ZMod 2) :=
  fun p q => gf4Emb (Y p.1 q.1) p.2 q.2

theorem blockM_zero : blockM 0 = 0 := by
  ext p q
  simp [blockM]

theorem blockM_add (Y Z : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) :
    blockM (Y + Z) = blockM Y + blockM Z := by
  ext p q
  simp [blockM]

theorem blockM_one : blockM 1 = 1 := by
  ext ⟨a, b⟩ ⟨c, d⟩
  by_cases hac : a = c
  · subst hac
    by_cases hbd : b = d
    · subst hbd
      simp [blockM]
    · simp [blockM, hbd]
  · simp [blockM, hac]

theorem blockM_mul (Y Z : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) :
    blockM (Y * Z) = blockM Y * blockM Z := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp only [blockM, Matrix.mul_apply, Fintype.sum_prod_type, map_sum, map_mul, Matrix.sum_apply]

@[expose] noncomputable def blockRingHom :
    Matrix (Fin 3) (Fin 3) (GaloisField 2 2) →+*
      Matrix (Fin 3 × Fin 2) (Fin 3 × Fin 2) (ZMod 2) where
  toFun := blockM
  map_one' := blockM_one
  map_mul' := blockM_mul
  map_zero' := blockM_zero
  map_add' := blockM_add

@[expose] noncomputable def ros :
    Matrix (Fin 3) (Fin 3) (GaloisField 2 2) →+* Matrix (Fin 6) (Fin 6) (ZMod 2) :=
  (Matrix.reindexAlgEquiv (ZMod 2) (ZMod 2) finProdFinEquiv).toRingHom.comp blockRingHom

theorem ros_apply (Y : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) (a c : Fin 3) (b d : Fin 2) :
    ros Y (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d)) = gf4Emb (Y a c) b d := by
  simp [ros, blockRingHom, blockM, Matrix.reindexAlgEquiv_apply, Matrix.reindex_apply,
    Matrix.submatrix_apply]

theorem ros_injective : Function.Injective ros := by
  intro Y Z h
  ext a c
  apply gf4Emb_injective
  ext b d
  have h1 := congrFun (congrFun h (finProdFinEquiv (a, b))) (finProdFinEquiv (c, d))
  rw [ros_apply, ros_apply] at h1
  exact h1

theorem rep3M_block : ∀ e c : Fin 3, ∀ f d : Fin 2,
    rep3M (finProdFinEquiv (e, f)) (finProdFinEquiv (c, d)) = if e = c then rhoM f d else 0 := by
  decide +kernel

theorem ros_scalar_omega : ros (Matrix.diagonal fun _ => omega4) = rep3M := by
  ext i j
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).surjective i
  obtain ⟨⟨c, d⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).surjective j
  rw [ros_apply, rep3M_block]
  by_cases hac : a = c
  · subst hac
    simp [gf4Emb_omega, rhoM]
  · simp [hac, Matrix.diagonal_apply]

theorem sum_fin6 (F : Fin 6 → ZMod 2) :
    ∑ k : Fin 6, F k = ∑ e : Fin 3, ∑ f : Fin 2, F (finProdFinEquiv (e, f)) := by
  have h1 := Equiv.sum_comp (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6) F
  rw [Fintype.sum_prod_type] at h1
  exact h1.symm

@[expose] def gfBlock (X : Matrix (Fin 6) (Fin 6) (ZMod 2)) (a c : Fin 3) :
    Matrix (Fin 2) (Fin 2) (ZMod 2) :=
  fun b d => X (finProdFinEquiv (a, b)) (finProdFinEquiv (c, d))

theorem gfBlock_commute (X : Matrix (Fin 6) (Fin 6) (ZMod 2)) (h : X * rep3M = rep3M * X)
    (a c : Fin 3) : gfBlock X a c * rhoM = rhoM * gfBlock X a c := by
  have hL : ∀ b d : Fin 2,
      ∑ k : Fin 6, X (finProdFinEquiv (a, b)) k * rep3M k (finProdFinEquiv (c, d))
        = ∑ f : Fin 2, X (finProdFinEquiv (a, b)) (finProdFinEquiv (c, f)) * rhoM f d := by
    intro b d
    rw [sum_fin6]
    simp only [rep3M_block, mul_ite, mul_zero]
    rw [Finset.sum_comm]
    simp
  have hR : ∀ b d : Fin 2,
      ∑ k : Fin 6, rep3M (finProdFinEquiv (a, b)) k * X k (finProdFinEquiv (c, d))
        = ∑ f : Fin 2, rhoM b f * X (finProdFinEquiv (a, f)) (finProdFinEquiv (c, d)) := by
    intro b d
    rw [sum_fin6]
    simp only [rep3M_block, ite_mul, zero_mul]
    rw [Finset.sum_comm]
    simp
  ext b d
  have h1 := congrFun (congrFun h (finProdFinEquiv (a, b))) (finProdFinEquiv (c, d))
  rw [Matrix.mul_apply, Matrix.mul_apply, hL b d, hR b d] at h1
  rw [Matrix.mul_apply, Matrix.mul_apply]
  exact h1

theorem exists_ros_of_commute (X : Matrix (Fin 6) (Fin 6) (ZMod 2)) (h : X * rep3M = rep3M * X) :
    ∃ Y : Matrix (Fin 3) (Fin 3) (GaloisField 2 2), ros Y = X := by
  have hblk : ∀ a c : Fin 3, ∃ x : GaloisField 2 2, gf4Emb x = gfBlock X a c :=
    fun a c => exists_gf4Emb_of_commute _ (gfBlock_commute X h a c)
  choose Y hY using hblk
  refine ⟨Matrix.of fun a c => Y a c, ?_⟩
  ext i j
  obtain ⟨⟨a, b⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).surjective i
  obtain ⟨⟨c, d⟩, rfl⟩ := (finProdFinEquiv : Fin 3 × Fin 2 ≃ Fin 6).surjective j
  rw [ros_apply]
  exact congrFun (congrFun (hY a c) b) d

theorem commute_rep3M_of_inv {P Q : Matrix (Fin 6) (Fin 6) (ZMod 2)} (hPQ : P * Q = 1)
    (hQP : Q * P = 1) (hP : P * rep3M = rep3M * P) : Q * rep3M = rep3M * Q := by
  have h : rep3M * Q = Q * rep3M := by
    calc rep3M * Q = (Q * P) * (rep3M * Q) := by rw [hQP, one_mul]
      _ = Q * ((P * rep3M) * Q) := by simp only [mul_assoc]
      _ = Q * ((rep3M * P) * Q) := by rw [hP]
      _ = Q * (rep3M * (P * Q)) := by simp only [mul_assoc]
      _ = Q * rep3M := by rw [hPQ, mul_one]
  exact h.symm

theorem det_ros_eq_one (A : SL(3, GaloisField 2 2)) :
    (ros (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2))).det = 1 := by
  have hA : (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)).det = 1 :=
    Matrix.SpecialLinearGroup.det_coe A
  have h1 : ros (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)).adjugate *
      ros (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) = 1 := by
    rw [← map_mul, Matrix.adjugate_mul, hA, one_smul, map_one]
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  have key : ∀ x y : ZMod 2, x * y = 1 → y = 1 := by decide
  exact key _ _ h2

@[expose] noncomputable def rosSL : SL(3, GaloisField 2 2) →* SL(6, ZMod 2) where
  toFun A := ⟨ros (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)), det_ros_eq_one A⟩
  map_one' := Subtype.ext (by simp)
  map_mul' A B := Subtype.ext (by
    show ros ((A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) * (B : Matrix (Fin 3) (Fin 3) (GaloisField 2 2))) =
      ros (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) * ros (B : Matrix (Fin 3) (Fin 3) (GaloisField 2 2))
    exact map_mul ros _ _)

theorem coe_rosSL (A : SL(3, GaloisField 2 2)) :
    ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
      ros (A : Matrix (Fin 3) (Fin 3) (GaloisField 2 2)) :=
  rfl

theorem rosSL_injective : Function.Injective rosSL := by
  intro A B h
  apply Subtype.ext
  apply ros_injective
  have h' := congrArg (fun M : SL(6, ZMod 2) => (M : Matrix (Fin 6) (Fin 6) (ZMod 2))) h
  simpa only [coe_rosSL] using h'

theorem card_SL3_gf4 : Nat.card SL(3, GaloisField 2 2) = 60480 := by
  have h : Nat.card SL(3, GaloisField 2 2) = Nat.card (GaloisField 2 2) ^ (3 * (3 - 1) / 2) *
      ∏ j ∈ Finset.Icc (2 : ℕ) 3, (Nat.card (GaloisField 2 2) ^ j - 1) :=
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num)
  rw [h, natCard_gf4]
  decide

theorem isPerfect_SL3_gf4 : Group.IsPerfect SL(3, GaloisField 2 2) :=
  CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (by norm_num)

theorem exists_rosSL_of_commute {X X' Y Y' : Matrix (Fin 6) (Fin 6) (ZMod 2)}
    (hX : X * X' = 1) (hX' : X' * X = 1) (hY : Y * Y' = 1) (hY' : Y' * Y = 1)
    (hXc : X * rep3M = rep3M * X) (hYc : Y * rep3M = rep3M * Y) :
    ∃ A : SL(3, GaloisField 2 2),
      ((rosSL A : SL(6, ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = X * Y * X' * Y' := by
  have hX'c : X' * rep3M = rep3M * X' := commute_rep3M_of_inv hX hX' hXc
  have hY'c : Y' * rep3M = rep3M * Y' := commute_rep3M_of_inv hY hY' hYc
  obtain ⟨P, rfl⟩ := exists_ros_of_commute X hXc
  obtain ⟨P', rfl⟩ := exists_ros_of_commute X' hX'c
  obtain ⟨Q, rfl⟩ := exists_ros_of_commute Y hYc
  obtain ⟨Q', rfl⟩ := exists_ros_of_commute Y' hY'c
  have hPP' : P * P' = 1 := ros_injective (by rw [map_mul, hX, map_one])
  have hQQ' : Q * Q' = 1 := ros_injective (by rw [map_mul, hY, map_one])
  have hdP : P.det * P'.det = 1 := by rw [← Matrix.det_mul, hPP', Matrix.det_one]
  have hdQ : Q.det * Q'.det = 1 := by rw [← Matrix.det_mul, hQQ', Matrix.det_one]
  have hdet : (P * Q * P' * Q').det = 1 := by
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_mul]
    calc P.det * Q.det * P'.det * Q'.det = (P.det * P'.det) * (Q.det * Q'.det) := by ring
      _ = 1 := by rw [hdP, hdQ, mul_one]
  refine ⟨⟨P * Q * P' * Q', hdet⟩, ?_⟩
  show ros (P * Q * P' * Q') = _
  simp only [map_mul]

end CFSG.RankThree.PartTwo.Sec4.RonanK429F
