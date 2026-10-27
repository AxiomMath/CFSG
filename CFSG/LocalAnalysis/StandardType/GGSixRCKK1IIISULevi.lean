module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIISUCoordRoot

public section

namespace CFSG.StandardType.RCKK1IIISU

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Universal.SpecialLinear CFSG.Open

variable {k : ℕ}

private theorem rckSUl_sI0_ne_sI1 (hk : 4 ≤ k) : sI0 hk ≠ sI1 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, sI1] at hv

private theorem rckSUl_sI1_ne_sI0 (hk : 4 ≤ k) : sI1 hk ≠ sI0 hk :=
  (rckSUl_sI0_ne_sI1 hk).symm

private theorem rckSUl_rev_sI0_ne_sI0 (hk : 4 ≤ k) : Fin.rev (sI0 hk) ≠ sI0 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, Fin.val_rev] at hv
  omega

private theorem rckSUl_rev_sI0_ne_sI1 (hk : 4 ≤ k) : Fin.rev (sI0 hk) ≠ sI1 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, sI1, Fin.val_rev] at hv
  omega

private theorem rckSUl_rev_sI1_ne_sI0 (hk : 4 ≤ k) : Fin.rev (sI1 hk) ≠ sI0 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI0, sI1, Fin.val_rev] at hv
  omega

private theorem rckSUl_rev_sI1_ne_sI1 (hk : 4 ≤ k) : Fin.rev (sI1 hk) ≠ sI1 hk := by
  intro h
  have hv := congrArg Fin.val h
  simp [sI1, Fin.val_rev] at hv
  omega

private theorem rckSUl_rev_sI0_ne_rev_sI1 (hk : 4 ≤ k) :
    Fin.rev (sI0 hk) ≠ Fin.rev (sI1 hk) :=
  fun h => rckSUl_sI0_ne_sI1 hk (Fin.rev_injective h)

private theorem rckSUl_sI0_ne_rev_sI0 (hk : 4 ≤ k) : sI0 hk ≠ Fin.rev (sI0 hk) :=
  (rckSUl_rev_sI0_ne_sI0 hk).symm

private theorem rckSUl_sI0_ne_rev_sI1 (hk : 4 ≤ k) : sI0 hk ≠ Fin.rev (sI1 hk) :=
  (rckSUl_rev_sI1_ne_sI0 hk).symm

private theorem rckSUl_sI1_ne_rev_sI0 (hk : 4 ≤ k) : sI1 hk ≠ Fin.rev (sI0 hk) :=
  (rckSUl_rev_sI0_ne_sI1 hk).symm

private theorem rckSUl_sI1_ne_rev_sI1 (hk : 4 ≤ k) : sI1 hk ≠ Fin.rev (sI1 hk) :=
  (rckSUl_rev_sI1_ne_sI1 hk).symm

private theorem rckSUl_card : Nat.card SUF = 4 := by
  rw [GaloisField.card 2 (2 * 1) (by norm_num)]
  norm_num

private theorem rckSUl_card_sq : Nat.card SUF = (2 ^ 1) ^ 2 := by
  rw [rckSUl_card]
  norm_num

private theorem rckSUl_sigma_involutive : ∀ c : SUF, SUσ (SUσ c) = c :=
  CFSG.LieType.BorelTits.unitaryInvolution_involutive rckSUl_card_sq

private theorem rckSUl_neg_eq (x : SUF) : -x = x := by
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  have hxx : x + x = 0 := by rw [← two_mul, h2, zero_mul]
  exact neg_eq_of_add_eq_zero_left hxx

private theorem rckSUl_sigma_apply (c : SUF) : SUσ c = c ^ 2 := by
  rw [SUσ, unitaryInvolution_apply]
  norm_num

private theorem rckSUl_add_self (x : SUF) : x + x = 0 := by
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  rw [← two_mul, h2, zero_mul]

private theorem rckSUl_nsmul2 (x : SUF) : (2 : ℕ) • x = 0 := by
  rw [two_nsmul, rckSUl_add_self]

private theorem rckSUl_nsmul3 (x : SUF) : (3 : ℕ) • x = x := by
  rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, rckSUl_nsmul2, one_nsmul, zero_add]

private theorem rckSUl_nsmul6 (x : SUF) : (6 : ℕ) • x = 0 := by
  rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_nsmul, rckSUl_nsmul3, rckSUl_nsmul2]

private theorem rckSUl_add_sq (x y : SUF) : (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
  have hxy : x * y + y * x = 0 := by
    rw [mul_comm y x, rckSUl_add_self]
  calc (x + y) ^ 2 = x * x + x * y + y * x + y * y := by ring
    _ = x ^ 2 + (x * y + y * x) + y ^ 2 := by ring
    _ = x ^ 2 + y ^ 2 := by rw [hxy]; ring

private theorem rckSUl_omega_add_sq : suOmega + suOmega ^ 2 = 1 := by
  have h1 : suOmega ^ 2 + suOmega + 1 = 0 := suOmega_spec
  have hx : suOmega + suOmega ^ 2 + 1 = 0 := by rw [add_comm suOmega (suOmega ^ 2)]; exact h1
  have hy : suOmega + suOmega ^ 2 = -1 := eq_neg_of_add_eq_zero_left hx
  rwa [rckSUl_neg_eq] at hy

private theorem rckSUl_algebraMap_sq (z : ZMod 2) :
    (algebraMap (ZMod 2) SUF z) ^ 2 = algebraMap (ZMod 2) SUF z := by
  rw [← map_pow]
  congr 1
  exact (by decide : ∀ z : ZMod 2, z ^ 2 = z) z

private theorem rckSUl_sigma_algebraMap (z : ZMod 2) :
    SUσ (algebraMap (ZMod 2) SUF z) = algebraMap (ZMod 2) SUF z := by
  rw [rckSUl_sigma_apply]
  exact rckSUl_algebraMap_sq z

private noncomputable def rckSUl_b (v : Fin 4 → ZMod 2) : SUF :=
  algebraMap (ZMod 2) SUF (v 1) + algebraMap (ZMod 2) SUF (v 2) * suOmega

private theorem rckSUl_b_add_sigma (v : Fin 4 → ZMod 2) :
    rckSUl_b v + SUσ (rckSUl_b v) = algebraMap (ZMod 2) SUF (v 2) := by
  set A := algebraMap (ZMod 2) SUF (v 1)
  set B := algebraMap (ZMod 2) SUF (v 2)
  have hA : A ^ 2 = A := rckSUl_algebraMap_sq (v 1)
  have hB : B ^ 2 = B := rckSUl_algebraMap_sq (v 2)
  rw [rckSUl_b, rckSUl_sigma_apply, rckSUl_add_sq, mul_pow, hA, hB]
  calc A + B * suOmega + (A + B * suOmega ^ 2)
      = (A + A) + (B * suOmega + B * suOmega ^ 2) := by ring
    _ = B * suOmega + B * suOmega ^ 2 := by rw [rckSUl_add_self, zero_add]
    _ = B * (suOmega + suOmega ^ 2) := by rw [mul_add]
    _ = B := by rw [rckSUl_omega_add_sq, mul_one]

private theorem rckSUl_sigma_add (x y : SUF) : SUσ (x + y) = SUσ x + SUσ y :=
  map_add SUσ x y

private theorem rckSUl_sigma_mul (x y : SUF) : SUσ (x * y) = SUσ x * SUσ y :=
  map_mul SUσ x y

private noncomputable def rckSUl_K (hk : 4 ≤ k) : Matrix (Fin k) (Fin k) SUF :=
  Matrix.single (sI0 hk) (sI1 hk) 1 +
    Matrix.single (Fin.rev (sI1 hk)) (Fin.rev (sI0 hk)) 1

private noncomputable def rckSUl_M (hk : 4 ≤ k) (a b bσ c : SUF) :
    Matrix (Fin k) (Fin k) SUF :=
  Matrix.single (sI0 hk) (Fin.rev (sI0 hk)) a +
    Matrix.single (sI0 hk) (Fin.rev (sI1 hk)) b +
    Matrix.single (sI1 hk) (Fin.rev (sI0 hk)) bσ +
    Matrix.single (sI1 hk) (Fin.rev (sI1 hk)) c

private theorem rckSUl_suCorner_eq (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    suCorner hk v = 1 + rckSUl_M hk (algebraMap (ZMod 2) SUF (v 0)) (rckSUl_b v)
      (SUσ (rckSUl_b v)) (algebraMap (ZMod 2) SUF (v 3)) := by
  simp only [suCorner, rckSUl_M, rckSUl_b]
  abel

private theorem rckSUl_K_mul_K (hk : 4 ≤ k) : rckSUl_K hk * rckSUl_K hk = 0 := by
  have h10 := rckSUl_sI1_ne_sI0 hk
  have h1r := rckSUl_sI1_ne_rev_sI1 hk
  have hr0 := rckSUl_rev_sI0_ne_sI0 hk
  have hr1 := rckSUl_rev_sI0_ne_rev_sI1 hk
  simp only [rckSUl_K, Matrix.add_mul, Matrix.mul_add, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, single_mul_single_of_ne _ _ _ _ h10,
    single_mul_single_of_ne _ _ _ _ h1r, single_mul_single_of_ne _ _ _ _ hr0,
    single_mul_single_of_ne _ _ _ _ hr1]

private theorem rckSUl_M_mul_M (hk : 4 ≤ k) (a b bσ c a' b' bσ' c' : SUF) :
    rckSUl_M hk a b bσ c * rckSUl_M hk a' b' bσ' c' = 0 := by
  have hr0u0 := rckSUl_rev_sI0_ne_sI0 hk
  have hr0u1 := rckSUl_rev_sI0_ne_sI1 hk
  have hr1u0 := rckSUl_rev_sI1_ne_sI0 hk
  have hr1u1 := rckSUl_rev_sI1_ne_sI1 hk
  simp only [rckSUl_M, Matrix.add_mul, Matrix.mul_add, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, single_mul_single_of_ne _ _ _ _ hr0u0,
    single_mul_single_of_ne _ _ _ _ hr0u1, single_mul_single_of_ne _ _ _ _ hr1u0,
    single_mul_single_of_ne _ _ _ _ hr1u1]

private theorem rckSUl_K_mul_M (hk : 4 ≤ k) (a b bσ c : SUF) :
    rckSUl_K hk * rckSUl_M hk a b bσ c =
      Matrix.single (sI0 hk) (Fin.rev (sI0 hk)) bσ +
        Matrix.single (sI0 hk) (Fin.rev (sI1 hk)) c := by
  have hu1u0 := rckSUl_sI1_ne_sI0 hk
  have hr0u0 := rckSUl_rev_sI0_ne_sI0 hk
  have hr0u1 := rckSUl_rev_sI0_ne_sI1 hk
  simp only [rckSUl_K, rckSUl_M, Matrix.add_mul, Matrix.mul_add, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, single_mul_single_same, mul_one, one_mul,
    single_mul_single_of_ne _ _ _ _ hu1u0, single_mul_single_of_ne _ _ _ _ hr0u0,
    single_mul_single_of_ne _ _ _ _ hr0u1]

private theorem rckSUl_M_mul_K (hk : 4 ≤ k) (a b bσ c : SUF) :
    rckSUl_M hk a b bσ c * rckSUl_K hk =
      Matrix.single (sI0 hk) (Fin.rev (sI0 hk)) b +
        Matrix.single (sI1 hk) (Fin.rev (sI0 hk)) c := by
  have hu0r0 := rckSUl_rev_sI0_ne_sI0 hk
  have hu0r1 := rckSUl_rev_sI1_ne_sI0 hk
  have hr0r1 := rckSUl_rev_sI0_ne_rev_sI1 hk
  simp only [rckSUl_K, rckSUl_M, Matrix.add_mul, Matrix.mul_add, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, single_mul_single_same, mul_one, one_mul,
    single_mul_single_of_ne _ _ _ _ hu0r0, single_mul_single_of_ne _ _ _ _ hu0r1,
    single_mul_single_of_ne _ _ _ _ hr0r1]

private theorem rckSUl_K_mul_M_mul_K (hk : 4 ≤ k) (a b bσ c : SUF) :
    rckSUl_K hk * rckSUl_M hk a b bσ c * rckSUl_K hk =
      Matrix.single (sI0 hk) (Fin.rev (sI0 hk)) c := by
  have hr0u0 := rckSUl_rev_sI0_ne_sI0 hk
  have hr0r1 := rckSUl_rev_sI0_ne_rev_sI1 hk
  have hr1u0 := rckSUl_rev_sI1_ne_sI0 hk
  rw [rckSUl_K_mul_M]
  simp only [rckSUl_K, Matrix.add_mul, Matrix.mul_add, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add, single_mul_single_same, mul_one, one_mul,
    single_mul_single_of_ne _ _ _ _ hr0u0, single_mul_single_of_ne _ _ _ _ hr0r1,
    single_mul_single_of_ne _ _ _ _ hr1u0]

private theorem rckSUl_c1_one_sided (hk : 4 ≤ k) (a b bσ c : SUF) :
    (1 + rckSUl_K hk) * (1 + rckSUl_M hk a b bσ c) =
      (1 + rckSUl_M hk (a + b + bσ + c) (b + c) (bσ + c) c) *
        (1 + rckSUl_K hk) := by
  have hKM := rckSUl_K_mul_M hk a b bσ c
  have hMK := rckSUl_M_mul_K hk (a + b + bσ + c) (b + c) (bσ + c) c
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hKM,
    Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, hMK]
  have h2 : (2 : SUF) = 0 := CharP.cast_eq_zero SUF 2
  have h3 : (3 : SUF) = 1 := by rw [show (3 : SUF) = 2 + 1 by norm_num, h2, zero_add]
  have h4 : (4 : SUF) = 0 := by rw [show (4 : SUF) = 2 * 2 by norm_num, h2, zero_mul]
  have h5 : (5 : SUF) = 1 := by
    rw [show (5 : SUF) = 2 + 2 + 1 by norm_num, h2]
    norm_num
  have h6 : (6 : SUF) = 0 := by rw [show (6 : SUF) = 2 * 3 by norm_num, h2, zero_mul]
  apply Matrix.ext
  intro i j
  simp only [rckSUl_M, rckSUl_K, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  split_ifs
  all_goals (try ring_nf)
  all_goals (repeat (first | rw [h2] | rw [h3] | rw [h4] | rw [h5] | rw [h6]))
  all_goals ring

private noncomputable def rckSUl_h1 (v : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  (s5h1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v

private noncomputable def rckSUl_h2 (v : Fin 4 → ZMod 2) : Fin 4 → ZMod 2 :=
  (s5h2 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v

private theorem rckSUl_h1_0 (v : Fin 4 → ZMod 2) : rckSUl_h1 v 0 = v 0 + v 2 + v 3 := by
  simp [rckSUl_h1, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h1, s5h1Mat]

private theorem rckSUl_h1_1 (v : Fin 4 → ZMod 2) : rckSUl_h1 v 1 = v 1 + v 3 := by
  simp [rckSUl_h1, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h1, s5h1Mat]

private theorem rckSUl_h1_2 (v : Fin 4 → ZMod 2) : rckSUl_h1 v 2 = v 2 := by
  simp [rckSUl_h1, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h1, s5h1Mat]

private theorem rckSUl_h1_3 (v : Fin 4 → ZMod 2) : rckSUl_h1 v 3 = v 3 := by
  simp [rckSUl_h1, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h1, s5h1Mat]

private theorem rckSUl_h2_0 (v : Fin 4 → ZMod 2) : rckSUl_h2 v 0 = v 3 := by
  simp [rckSUl_h2, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h2, s5h2Mat]

private theorem rckSUl_h2_1 (v : Fin 4 → ZMod 2) : rckSUl_h2 v 1 = v 1 + v 2 := by
  simp [rckSUl_h2, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h2, s5h2Mat]

private theorem rckSUl_h2_2 (v : Fin 4 → ZMod 2) : rckSUl_h2 v 2 = v 2 := by
  simp [rckSUl_h2, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h2, s5h2Mat]

private theorem rckSUl_h2_3 (v : Fin 4 → ZMod 2) : rckSUl_h2 v 3 = v 0 := by
  simp [rckSUl_h2, Matrix.mulVec, dotProduct, Fin.sum_univ_four, s5h2, s5h2Mat]

private theorem rckSUl_omega_sq : suOmega ^ 2 = suOmega + 1 := by
  have h := rckSUl_omega_add_sq
  have hL : suOmega + (suOmega + suOmega ^ 2) = suOmega ^ 2 := by
    rw [← add_assoc, rckSUl_add_self, zero_add]
  have hω : suOmega + (suOmega + suOmega ^ 2) = suOmega + 1 := by rw [h]
  rwa [hL] at hω

private theorem rckSUl_b_h1 (v : Fin 4 → ZMod 2) :
    rckSUl_b (rckSUl_h1 v) = rckSUl_b v + algebraMap (ZMod 2) SUF (v 3) := by
  rw [rckSUl_b, rckSUl_h1_1, rckSUl_h1_2, map_add, rckSUl_b]
  ring

private theorem rckSUl_b_h2 (v : Fin 4 → ZMod 2) :
    rckSUl_b (rckSUl_h2 v) = SUσ (rckSUl_b v) := by
  rw [rckSUl_b, rckSUl_h2_1, rckSUl_h2_2, map_add, rckSUl_b, rckSUl_sigma_add,
    rckSUl_sigma_mul, rckSUl_sigma_algebraMap, rckSUl_sigma_algebraMap, rckSUl_sigma_apply]
  rw [rckSUl_omega_sq]
  ring

private theorem rckSUl_h1_a (v : Fin 4 → ZMod 2) :
    algebraMap (ZMod 2) SUF (rckSUl_h1 v 0) =
      algebraMap (ZMod 2) SUF (v 0) + rckSUl_b v + SUσ (rckSUl_b v) +
        algebraMap (ZMod 2) SUF (v 3) := by
  simp only [rckSUl_h1_0, map_add]
  rw [← rckSUl_b_add_sigma v]
  ring

private theorem rckSUl_sigma_b_h1 (v : Fin 4 → ZMod 2) :
    SUσ (rckSUl_b (rckSUl_h1 v)) =
      SUσ (rckSUl_b v) + algebraMap (ZMod 2) SUF (v 3) := by
  rw [rckSUl_b_h1, rckSUl_sigma_add, rckSUl_sigma_algebraMap]

private noncomputable def rckSUl_pi (hk : 4 ≤ k) : Equiv.Perm (Fin k) :=
  Equiv.swap (sI0 hk) (sI1 hk) * Equiv.swap (Fin.rev (sI0 hk)) (Fin.rev (sI1 hk))

private theorem rckSUl_pi_sI0 (hk : 4 ≤ k) : rckSUl_pi hk (sI0 hk) = sI1 hk := by
  rw [rckSUl_pi, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (rckSUl_sI0_ne_rev_sI0 hk) (rckSUl_sI0_ne_rev_sI1 hk)]
  exact Equiv.swap_apply_left _ _

private theorem rckSUl_pi_sI1 (hk : 4 ≤ k) : rckSUl_pi hk (sI1 hk) = sI0 hk := by
  rw [rckSUl_pi, Equiv.Perm.mul_apply,
    Equiv.swap_apply_of_ne_of_ne (rckSUl_sI1_ne_rev_sI0 hk) (rckSUl_sI1_ne_rev_sI1 hk)]
  exact Equiv.swap_apply_right _ _

private theorem rckSUl_pi_rev_sI0 (hk : 4 ≤ k) :
    rckSUl_pi hk (Fin.rev (sI0 hk)) = Fin.rev (sI1 hk) := by
  rw [rckSUl_pi, Equiv.Perm.mul_apply, Equiv.swap_apply_left,
    Equiv.swap_apply_of_ne_of_ne (rckSUl_rev_sI1_ne_sI0 hk) (rckSUl_rev_sI1_ne_sI1 hk)]

private theorem rckSUl_pi_rev_sI1 (hk : 4 ≤ k) :
    rckSUl_pi hk (Fin.rev (sI1 hk)) = Fin.rev (sI0 hk) := by
  rw [rckSUl_pi, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
    Equiv.swap_apply_of_ne_of_ne (rckSUl_rev_sI0_ne_sI0 hk) (rckSUl_rev_sI0_ne_sI1 hk)]

private theorem rckSUl_pi_mul_M_aux (hk : 4 ≤ k) (a b bσ c : SUF) :
    signedPerm (rckSUl_pi hk) (fun _ => 1) * rckSUl_M hk a b bσ c =
      rckSUl_M hk c bσ b a * signedPerm (rckSUl_pi hk) (fun _ => 1) := by
  rw [rckSUl_M, Matrix.mul_add, Matrix.mul_add, Matrix.mul_add,
    signedPerm_mul_single_eq (rckSUl_pi hk) (sI0 hk) (Fin.rev (sI0 hk)) (by simp) a,
    signedPerm_mul_single_eq (rckSUl_pi hk) (sI0 hk) (Fin.rev (sI1 hk)) (by simp) b,
    signedPerm_mul_single_eq (rckSUl_pi hk) (sI1 hk) (Fin.rev (sI0 hk)) (by simp) bσ,
    signedPerm_mul_single_eq (rckSUl_pi hk) (sI1 hk) (Fin.rev (sI1 hk)) (by simp) c,
    rckSUl_pi_sI0 hk, rckSUl_pi_sI1 hk, rckSUl_pi_rev_sI0 hk, rckSUl_pi_rev_sI1 hk]
  simp only [Pi.one_apply, one_mul, inv_one, mul_one]
  rw [rckSUl_M]
  simp only [Matrix.add_mul]
  abel

private theorem rckSUl_pi_mul_M (hk : 4 ≤ k) (a b bσ c : SUF) :
    signedPerm (rckSUl_pi hk) (fun _ => 1) * (1 + rckSUl_M hk a b bσ c) =
      (1 + rckSUl_M hk c bσ b a) * signedPerm (rckSUl_pi hk) (fun _ => 1) := by
  rw [Matrix.mul_add, Matrix.mul_one, rckSUl_pi_mul_M_aux, Matrix.add_mul, Matrix.one_mul]

private noncomputable def rckSUl_rootH01 (hk : 4 ≤ k) : Multiplicative SUF →* SUG k :=
  rootHom SUσ rckSUl_sigma_involutive (rckSUl_sI0_ne_sI1 hk) (rckSUl_sI0_ne_rev_sI0 hk)
    (rckSUl_sI1_ne_rev_sI1 hk)

private noncomputable def rckSUl_rootH10 (hk : 4 ≤ k) : Multiplicative SUF →* SUG k :=
  rootHom SUσ rckSUl_sigma_involutive (rckSUl_sI1_ne_sI0 hk) (rckSUl_sI1_ne_rev_sI1 hk)
    (rckSUl_sI0_ne_rev_sI0 hk)

private noncomputable def rckSUl_c1 (hk : 4 ≤ k) : SUG k :=
  rckSUl_rootH01 hk (Multiplicative.ofAdd (1 : SUF))

private noncomputable def rckSUl_c2 (hk : 4 ≤ k) : SUG k :=
  rckSUl_rootH01 hk (Multiplicative.ofAdd (1 : SUF)) *
    rckSUl_rootH10 hk (Multiplicative.ofAdd (1 : SUF)) *
    rckSUl_rootH01 hk (Multiplicative.ofAdd (1 : SUF))

private theorem rckSUl_rootH01_val (hk : 4 ≤ k) :
    ((rckSUl_rootH01 hk (Multiplicative.ofAdd (1 : SUF)) : SUG k) :
        GL (Fin k) SUF).1 = rootMatrix SUσ (sI0 hk) (sI1 hk) 1 := by
  rw [rckSUl_rootH01, coe_rootHom, toAdd_ofAdd]

private theorem rckSUl_rootH10_val (hk : 4 ≤ k) :
    ((rckSUl_rootH10 hk (Multiplicative.ofAdd (1 : SUF)) : SUG k) :
        GL (Fin k) SUF).1 = rootMatrix SUσ (sI1 hk) (sI0 hk) 1 := by
  rw [rckSUl_rootH10, coe_rootHom, toAdd_ofAdd]

private theorem rckSUl_c1_val (hk : 4 ≤ k) :
    ((rckSUl_c1 hk : SUG k) : GL (Fin k) SUF).1 = 1 + rckSUl_K hk := by
  rw [rckSUl_c1, rckSUl_rootH01_val, rootMatrix, map_one, rckSUl_K, sub_eq_add_neg,
    Matrix.single_neg, rckSUl_neg_eq]
  abel

private theorem rckSUl_c2_val (hk : 4 ≤ k) :
    ((rckSUl_c2 hk : SUG k) : GL (Fin k) SUF).1 =
      signedPerm (rckSUl_pi hk) (fun _ => 1) := by
  rw [rckSUl_c2, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul,
    rckSUl_rootH01_val, rckSUl_rootH10_val]
  have hweyl := rootMatrix_weyl (σ := SUσ) (a := sI0 hk) (b := sI1 hk)
    (rckSUl_sI0_ne_sI1 hk) (rckSUl_sI0_ne_rev_sI0 hk) (rckSUl_sI1_ne_rev_sI1 hk)
    (rckSUl_sI1_ne_rev_sI0 hk) (c := (1 : SUF)) (by norm_num)
  rw [show -(1 : SUF)⁻¹ = 1 from by rw [inv_one, rckSUl_neg_eq]] at hweyl
  rw [hweyl]
  congr 1
  funext s
  simp [shortSign, rckSUl_neg_eq, inv_one, map_one]

private theorem rckSUl_c1_mul_suCorner (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    (1 + rckSUl_K hk) * suCorner hk v =
      suCorner hk (rckSUl_h1 v) * (1 + rckSUl_K hk) := by
  rw [rckSUl_suCorner_eq hk v, rckSUl_suCorner_eq hk (rckSUl_h1 v)]
  have h1a : algebraMap (ZMod 2) SUF (rckSUl_h1 v 0) =
      algebraMap (ZMod 2) SUF (v 0) + rckSUl_b v + SUσ (rckSUl_b v) +
        algebraMap (ZMod 2) SUF (v 3) := rckSUl_h1_a v
  have h1s : SUσ (rckSUl_b (rckSUl_h1 v)) =
      SUσ (rckSUl_b v) + algebraMap (ZMod 2) SUF (v 3) := rckSUl_sigma_b_h1 v
  have h1b : rckSUl_b (rckSUl_h1 v) = rckSUl_b v +
      algebraMap (ZMod 2) SUF (v 3) := rckSUl_b_h1 v
  have h1c : algebraMap (ZMod 2) SUF (rckSUl_h1 v 3) =
      algebraMap (ZMod 2) SUF (v 3) := by rw [rckSUl_h1_3]
  rw [h1a, h1s, h1b, h1c]
  exact rckSUl_c1_one_sided hk _ _ _ _

private theorem rckSUl_c2_mul_suCorner (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    signedPerm (rckSUl_pi hk) (fun _ => 1) * suCorner hk v =
      suCorner hk (rckSUl_h2 v) * signedPerm (rckSUl_pi hk) (fun _ => 1) := by
  rw [rckSUl_suCorner_eq hk v, rckSUl_suCorner_eq hk (rckSUl_h2 v)]
  have h2a : algebraMap (ZMod 2) SUF (rckSUl_h2 v 0) =
      algebraMap (ZMod 2) SUF (v 3) := by rw [rckSUl_h2_0]
  have h2b : rckSUl_b (rckSUl_h2 v) = SUσ (rckSUl_b v) := rckSUl_b_h2 v
  have h2s : SUσ (rckSUl_b (rckSUl_h2 v)) = rckSUl_b v := by
    rw [rckSUl_b_h2, rckSUl_sigma_involutive]
  have h2c : algebraMap (ZMod 2) SUF (rckSUl_h2 v 3) =
      algebraMap (ZMod 2) SUF (v 0) := by rw [rckSUl_h2_3]
  rw [h2a, h2s, h2b, h2c]
  exact rckSUl_pi_mul_M hk _ _ _ _

private theorem rckSUl_conj_of_mul (hk : 4 ≤ k) {c : SUG k} {v w : Fin 4 → ZMod 2}
    (h : ((c : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF) * suCorner hk v =
      suCorner hk w * ((c : GL (Fin k) SUF) : Matrix (Fin k) (Fin k) SUF)) :
    c * suZ hk v * c⁻¹ = suZ hk w := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  simpa only [Subgroup.coe_mul, Units.val_mul, suZ_val] using h

private theorem rckSUl_c1_conj_formula (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    rckSUl_c1 hk * suZ hk v * (rckSUl_c1 hk)⁻¹ = suZ hk (rckSUl_h1 v) := by
  apply rckSUl_conj_of_mul hk
  rw [rckSUl_c1_val]
  exact rckSUl_c1_mul_suCorner hk v

private theorem rckSUl_c2_conj_formula (hk : 4 ≤ k) (v : Fin 4 → ZMod 2) :
    rckSUl_c2 hk * suZ hk v * (rckSUl_c2 hk)⁻¹ = suZ hk (rckSUl_h2 v) := by
  apply rckSUl_conj_of_mul hk
  rw [rckSUl_c2_val]
  exact rckSUl_c2_mul_suCorner hk v

private theorem rckSUl_h1_fix : rckSUl_h1 ![0, 1, 0, 0] = ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [rckSUl_h1_0, rckSUl_h1_1, rckSUl_h1_2, rckSUl_h1_3]

private theorem rckSUl_h2_fix : rckSUl_h2 ![0, 1, 0, 0] = ![0, 1, 0, 0] := by
  funext i
  fin_cases i <;>
    simp [rckSUl_h2_0, rckSUl_h2_1, rckSUl_h2_2, rckSUl_h2_3]

theorem rckSU_levi (hk : 4 ≤ k) :
    ∃ c₁ c₂ : SUG k, c₁ * suR hk = suR hk * c₁ ∧ c₂ * suR hk = suR hk * c₂ ∧
      (∀ v : Fin 4 → ZMod 2,
        c₁ * suZ hk v * c₁⁻¹ =
          suZ hk ((s5h1 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)) ∧
      (∀ v : Fin 4 → ZMod 2,
        c₂ * suZ hk v * c₂⁻¹ =
          suZ hk ((s5h2 : Matrix (Fin 4) (Fin 4) (ZMod 2)).mulVec v)) := by
  refine ⟨rckSUl_c1 hk, rckSUl_c2 hk, ?_, ?_, ?_, ?_⟩
  · have hconj := rckSUl_c1_conj_formula hk ![0, 1, 0, 0]
    rw [rckSUl_h1_fix] at hconj
    simp only [suR]
    rwa [mul_inv_eq_iff_eq_mul] at hconj
  · have hconj := rckSUl_c2_conj_formula hk ![0, 1, 0, 0]
    rw [rckSUl_h2_fix] at hconj
    simp only [suR]
    rwa [mul_inv_eq_iff_eq_mul] at hconj
  · intro v
    exact rckSUl_c1_conj_formula hk v
  · intro v
    exact rckSUl_c2_conj_formula hk v

end CFSG.StandardType.RCKK1IIISU
