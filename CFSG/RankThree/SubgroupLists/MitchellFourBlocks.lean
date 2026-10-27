module

public import CFSG.RankThree.SubgroupLists.MitchellFourBasic
public import CFSG.RankThree.SubgroupLists.SymplecticTwoRotations

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

theorem one_ne_neg_one_matTwo (h2 : (2 : K) ≠ 0) : (1 : Matrix (Fin 2) (Fin 2) K) ≠ -1 := by
  intro h
  exact one_ne_neg_one_of_two h2 (by simpa using congrFun (congrFun h 0) 0)

theorem sq_ne_smul_one_of_pow_four (h2 : (2 : K) ≠ 0) {A : Matrix (Fin 2) (Fin 2) K}
    (hA : A.det = 1) (hA4 : A ^ 4 = -1) (c : K) : A ^ 2 ≠ c • 1 := by
  intro h
  have hc : c * c = 1 := by
    have := congrArg Matrix.det h
    rw [Matrix.det_pow, hA, one_pow, Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one,
      sq] at this
    exact this.symm
  apply one_ne_neg_one_matTwo h2
  rw [← hA4, show (4 : ℕ) = 2 + 2 from rfl, pow_add, h, smul_mul_smul_comm, one_mul, hc, one_smul]

theorem commute_of_sq_commute (h2 : (2 : K) ≠ 0) {A B : Matrix (Fin 2) (Fin 2) K}
    (hA : A.det = 1) (hB : B.det = 1) (hA4 : A ^ 4 = -1) (hB4 : B ^ 4 = -1)
    (h : A ^ 2 * B ^ 2 = B ^ 2 * A ^ 2) : A * B = B * A := by
  have h1 : A ^ 2 * B = B * A ^ 2 :=
    commute_of_commute_of_ne_scalar (sq_ne_smul_one_of_pow_four h2 hB hB4) h
      (Commute.self_pow B 2).eq
  exact commute_of_commute_of_ne_scalar (sq_ne_smul_one_of_pow_four h2 hA hA4)
    (Commute.self_pow A 2).eq h1.symm

theorem sq_mul_sq_comm_of_mul_eq_smul {A B : Matrix (Fin 2) (Fin 2) K} {ε : K} (hε : ε * ε = 1)
    (h : A * B = ε • (B * A)) : A ^ 2 * B ^ 2 = B ^ 2 * A ^ 2 := by
  have h1 : A ^ 2 * B = B * A ^ 2 := by
    calc A ^ 2 * B = A * (A * B) := by rw [sq, Matrix.mul_assoc]
      _ = A * (ε • (B * A)) := by rw [h]
      _ = ε • (A * B * A) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
      _ = ε • (ε • (B * A) * A) := by rw [h]
      _ = (ε * ε) • (B * A * A) := by rw [Matrix.smul_mul, smul_smul]
      _ = B * A ^ 2 := by rw [hε, one_smul, sq, Matrix.mul_assoc]
  exact ((show Commute (A ^ 2) B from h1).pow_right 2).eq

theorem sq_commutator_eq_one_of_commutator {a b : SL(2, K)}
    (h : ((a * b * a⁻¹ * b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = 1 ∨
      ((a * b * a⁻¹ * b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = -1) :
    a ^ 2 * b ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ = 1 := by
  obtain ⟨ε, hε, hw⟩ : ∃ ε : K, ε * ε = 1 ∧
      ((a * b * a⁻¹ * b⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) = ε • 1 := by
    rcases h with h | h
    · exact ⟨1, mul_one 1, by rw [h, one_smul]⟩
    · exact ⟨-1, by rw [mul_neg, mul_one, neg_neg], by rw [h, neg_one_smul]⟩
  have hab : (a : Matrix (Fin 2) (Fin 2) K) * b = ε • ((b : Matrix (Fin 2) (Fin 2) K) * a) := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul,
      show a * b = a * b * a⁻¹ * b⁻¹ * (b * a) by group, Matrix.SpecialLinearGroup.coe_mul, hw,
      Matrix.smul_mul, Matrix.one_mul]
  rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm]
  apply Subtype.ext
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using
    sq_mul_sq_comm_of_mul_eq_smul hε hab

theorem commutator_eq_one_of_sq_commutator (h2 : (2 : K) ≠ 0) {a b : SL(2, K)}
    (ha4 : (a : Matrix (Fin 2) (Fin 2) K) ^ 4 = -1) (hb4 : (b : Matrix (Fin 2) (Fin 2) K) ^ 4 = -1)
    (h : a ^ 2 * b ^ 2 * (a ^ 2)⁻¹ * (b ^ 2)⁻¹ = 1) : a * b * a⁻¹ * b⁻¹ = 1 := by
  rw [← commutatorElement_def, commutatorElement_eq_one_iff_mul_comm] at h ⊢
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  refine commute_of_sq_commute h2 (Matrix.SpecialLinearGroup.det_coe a)
    (Matrix.SpecialLinearGroup.det_coe b) ha4 hb4 ?_
  simpa only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_pow] using
    congrArg Subtype.val h

theorem pow_ne_one_of_pow_three_eq_neg_one (h2 : (2 : K) ≠ 0) {m : Matrix (Fin 2) (Fin 2) K}
    (h3 : m ^ 3 = -1) (h1 : m ≠ 1) (hm1 : m ≠ -1) {j : ℕ} (hj1 : 1 ≤ j) (hj6 : j < 6) :
    m ^ j ≠ 1 := by
  intro hj
  obtain rfl | rfl | rfl | rfl | rfl : j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 := by omega
  · exact h1 (by rwa [pow_one] at hj)
  · exact hm1 (by rw [← h3, pow_succ, hj, one_mul])
  · exact one_ne_neg_one_matTwo h2 (hj.symm.trans h3)
  · exact hm1 (neg_eq_iff_eq_neg.mp (by rw [← hj, pow_succ, h3, neg_one_mul]))
  · have hsq : m ^ 2 = -1 :=
      neg_eq_iff_eq_neg.mp (by rw [← hj, show (5 : ℕ) = 3 + 2 from rfl, pow_add, h3, neg_one_mul])
    exact h1 (neg_inj.mp (by rw [← h3, pow_succ, hsq, neg_one_mul]))

theorem plusBlock_neg_one : plusBlock (-1 : Matrix V₄ V₄ K) = -1 := by
  rw [← neg_one_smul K (1 : Matrix V₄ V₄ K), plusBlock_smul, plusBlock_one, neg_one_smul]

theorem plusBlock_pow_four_of (h2 : (2 : K) ≠ 0) {x : GL V₄ K}
    (hxt : (x : Matrix V₄ V₄ K) * tStdMat = tStdMat * (x : Matrix V₄ V₄ K)) (hx4 : x ^ 4 = -1) :
    plusBlock (x : Matrix V₄ V₄ K) ^ 4 = -1 := by
  rw [← plusBlock_pow h2 hxt, ← Units.val_pow_eq_pow_val, hx4, Units.val_neg, Units.val_one,
    plusBlock_neg_one]

theorem plusHom_pow (h2 : (2 : K) ≠ 0) {x : GL V₄ K} (hxC : x ∈ stdCent K) (n : ℕ) :
    plusHom h2 ⟨x ^ n, pow_mem hxC n⟩ = plusHom h2 ⟨x, hxC⟩ ^ n :=
  map_pow (plusHom h2) ⟨x, hxC⟩ n

theorem plusBlock_commutator_eq (h2 : (2 : K) ≠ 0) {x y : GL V₄ K} (hxC : x ∈ stdCent K)
    (hyC : y ∈ stdCent K) :
    plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) =
      ((plusHom h2 ⟨x, hxC⟩ * plusHom h2 ⟨y, hyC⟩ * (plusHom h2 ⟨x, hxC⟩)⁻¹ *
        (plusHom h2 ⟨y, hyC⟩)⁻¹ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) := by
  rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, coe_plusHom]
  rfl

theorem plusBlock_commutator_eq_one_of_sq (h2 : (2 : K) ≠ 0) {x y : GL V₄ K}
    (hxC : x ∈ stdCent K) (hyC : y ∈ stdCent K) (hx4 : x ^ 4 = -1) (hy4 : y ^ 4 = -1)
    (h : plusBlock ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1) :
    plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 := by
  rw [plusBlock_commutator_eq h2 (pow_mem hxC 2) (pow_mem hyC 2), plusHom_pow h2 hxC,
    plusHom_pow h2 hyC] at h
  have ha4 : ((plusHom h2 ⟨x, hxC⟩ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 4 = -1 := by
    rw [coe_plusHom]
    exact plusBlock_pow_four_of h2 (mem_stdCent.mp hxC).2 hx4
  have hb4 : ((plusHom h2 ⟨y, hyC⟩ : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) ^ 4 = -1 := by
    rw [coe_plusHom]
    exact plusBlock_pow_four_of h2 (mem_stdCent.mp hyC).2 hy4
  rw [plusBlock_commutator_eq h2 hxC hyC,
    commutator_eq_one_of_sq_commutator h2 ha4 hb4 (Subtype.ext h),
    Matrix.SpecialLinearGroup.coe_one]

section Finite

variable [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem orderOf_plusBar_of_pow_four (h2 : (2 : K) ≠ 0) {G : Subgroup (GL V₄ K)} {x : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) (hx4 : x ^ 4 = -1) :
    orderOf (plusBar h2 hxG hxC) = 4 := by
  have hxt := (mem_stdCent.mp hxC).2
  have hP4 := plusBlock_pow_four_of h2 hxt hx4
  have hne := one_ne_neg_one_matTwo h2
  refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
  · rw [pow_one, plusBar_pow, plusBar_eq_one_iff, Units.val_pow_eq_pow_val, plusBlock_pow h2 hxt]
    rintro (h | h)
    · exact hne (by rw [← hP4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, one_pow])
    · exact hne (by rw [← hP4, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h, neg_one_sq])
  · rw [plusBar_pow, plusBar_eq_one_iff, show 2 ^ (1 + 1) = 4 from rfl, hx4, Units.val_neg,
      Units.val_one, plusBlock_neg_one]
    exact Or.inr rfl

variable (hp2 : p ≠ 2) {G : Subgroup (GL V₄ K)} (hU0 : ∀ x ∈ G, IsSqZero x → x = 1)
  (hneg : (-1 : GL V₄ K) ∈ G)
include hp2 hU0 hneg

theorem plusBlock_sq_commutator_eq_one_or_neg {x y : GL V₄ K}
    (hxG : x ∈ G) (hxC : x ∈ stdCent K) (hyG : y ∈ G) (hyC : y ∈ stdCent K)
    (hx4 : x ^ 4 = -1) (hy4 : y ^ 4 = -1) :
    plusBlock ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = 1 ∨
      plusBlock ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = -1 := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  obtain ⟨f, hF⟩ := card_eq_pow_of_finite (K := K) (p := p) hp2
  have hcomm := sq_mul_sq_comm_of_orderOf_four hF _ (not_dvd_card_plusImage hp2 hU0 hneg)
    (orderOf_plusBar_of_pow_four h2 hxG hxC hx4) (orderOf_plusBar_of_pow_four h2 hyG hyC hy4)
  have hcG : x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem (G.mul_mem (G.pow_mem hxG 2) (G.pow_mem hyG 2))
      (G.inv_mem (G.pow_mem hxG 2))) (G.inv_mem (G.pow_mem hyG 2))
  have hcC : x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ ∈ stdCent K :=
    mul_mem (mul_mem (mul_mem (pow_mem hxC 2) (pow_mem hyC 2)) (inv_mem (pow_mem hxC 2)))
      (inv_mem (pow_mem hyC 2))
  refine (plusBar_eq_one_iff h2 hcG hcC).mp ?_
  have e : plusBar h2 hcG hcC = plusBar h2 hxG hxC ^ 2 * plusBar h2 hyG hyC ^ 2 *
      (plusBar h2 hxG hxC ^ 2)⁻¹ * (plusBar h2 hyG hyC ^ 2)⁻¹ := by
    rw [plusBar_pow, plusBar_pow, plusBar_inv hp2 hU0 hneg, plusBar_inv hp2 hU0 hneg, plusBar_mul,
      plusBar_mul, plusBar_mul]
  rw [e, hcomm]
  group

theorem plusBlock_commutator_cube {x y : GL V₄ K} (hxG : x ∈ G)
    (hxC : x ∈ stdCent K) (hyG : y ∈ G) (hyC : y ∈ stdCent K) (hx4 : x ^ 4 = -1)
    (hy4 : y ^ 4 = -1)
    (h : plusBlock ((x ^ 2 * y ^ 2 * (x ^ 2)⁻¹ * (y ^ 2)⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) = -1) :
    (plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) ^ 3 = 1 ∨
      plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) ^ 3 = -1) ∧
      plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) ≠ 1 ∧
      plusBlock ((x * y * x⁻¹ * y⁻¹ : GL V₄ K) : Matrix V₄ V₄ K) ≠ -1 := by
  have h2 := two_ne_zero_of_charP (K := K) hp2
  obtain ⟨f, hF⟩ := card_eq_pow_of_finite (K := K) (p := p) hp2
  have hwG : x * y * x⁻¹ * y⁻¹ ∈ G :=
    G.mul_mem (G.mul_mem (G.mul_mem hxG hyG) (G.inv_mem hxG)) (G.inv_mem hyG)
  have hwC : x * y * x⁻¹ * y⁻¹ ∈ stdCent K :=
    mul_mem (mul_mem (mul_mem hxC hyC) (inv_mem hxC)) (inv_mem hyC)
  have e : plusBar h2 hwG hwC = plusBar h2 hxG hxC * plusBar h2 hyG hyC *
      (plusBar h2 hxG hxC)⁻¹ * (plusBar h2 hyG hyC)⁻¹ := by
    rw [plusBar_inv hp2 hU0 hneg, plusBar_inv hp2 hU0 hneg, plusBar_mul, plusBar_mul, plusBar_mul]
  have hxy : plusBar h2 hxG hxC * plusBar h2 hyG hyC ≠
      plusBar h2 hyG hyC * plusBar h2 hxG hxC := by
    intro hc
    have hw := (plusBar_eq_one_iff h2 hwG hwC).mp (by rw [e, hc]; group)
    rw [plusBlock_commutator_eq h2 hxC hyC] at hw
    rw [plusBlock_commutator_eq h2 (pow_mem hxC 2) (pow_mem hyC 2), plusHom_pow h2 hxC,
      plusHom_pow h2 hyC, sq_commutator_eq_one_of_commutator hw,
      Matrix.SpecialLinearGroup.coe_one] at h
    exact one_ne_neg_one_matTwo h2 h
  obtain ⟨h3, h1⟩ := commutator_pow_three_of_orderOf_four hF _
    (not_dvd_card_plusImage hp2 hU0 hneg) (orderOf_plusBar_of_pow_four h2 hxG hxC hx4)
    (orderOf_plusBar_of_pow_four h2 hyG hyC hy4) hxy
  rw [← e, plusBar_pow, plusBar_eq_one_iff, Units.val_pow_eq_pow_val,
    plusBlock_pow h2 (mem_stdCent.mp hwC).2] at h3
  rw [← e, ne_eq, plusBar_eq_one_iff, not_or] at h1
  exact ⟨h3, h1⟩

end Finite

end CFSG.RankThree.SubgroupLists
