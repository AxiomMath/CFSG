module

public import CFSG.RankThree.PartOne.SEITZ3.LongRoot

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3
open scoped commutatorElement

variable {K : Type} [Field K]

theorem xp_inv [CharP K 2] (p : ℕ) (c : K) : (xp p c)⁻¹ = xp p c :=
  inv_eq_of_mul_eq_one_right (xp_mul_self p c)

theorem cast_neg_one_eq [CharP K 2] : ((-1 : ℤ) : K) = 1 := by simp [CharTwo.neg_eq]

theorem cast_neg_two_eq [CharP K 2] : ((-2 : ℤ) : K) = 0 := by simp [CharTwo.two_eq_zero]

theorem cast_two_eq [CharP K 2] : ((2 : ℤ) : K) = 0 := by simp [CharTwo.two_eq_zero]

theorem cast_neg_three_eq [CharP K 2] : ((-3 : ℤ) : K) = 1 := by
  have : ((3 : ℤ) : K) = 1 := by
    have h : ((3 : ℤ) : K) = ((2 : ℤ) : K) + 1 := by push_cast; ring
    rw [h, cast_two_eq, zero_add]
  rw [Int.cast_neg, this, CharTwo.neg_eq]

theorem cast_three_eq [CharP K 2] : ((3 : ℤ) : K) = 1 := by
  have h : ((3 : ℤ) : K) = ((2 : ℤ) : K) + 1 := by push_cast; ring
  rw [h, cast_two_eq, zero_add]

theorem swap_of_comm {G : Type*} [Group G] (g h z : G) (hz : ⁅g, h⁆ = z) : g * h = z * (h * g) := by
  rw [← hz, commutatorElement_def]
  group

theorem swap_10 [CharP K 2] (a s : K) :
    xp 1 a * xp 0 s = xp 4 (a * s) * xp 8 (a ^ 2 * s) * xp 3 (a ^ 3 * s) * (xp 0 s * xp 1 a) := by
  have h : RootOps.repCheck .G2 1 0 [(1, 1, 4, -1), (2, 1, 8, 1), (3, 1, 3, 1), (3, 2, 7, 2)] =
      true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h a s
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  simp only [cast_neg_one_eq, Int.cast_one, Int.cast_ofNat, CharTwo.two_eq_zero, zero_mul,
    one_mul] at this
  refine swap_of_comm _ _ _ ?_
  rw [this]
  have h0 : xPar (rootOperatorFamily .G2) ((Tag.rootCertificate .G2).root 7) (0 : K) = 1 :=
    xp_zero 7
  rw [h0, mul_one]
  simp only [pow_one]
  exact (mul_assoc _ _ _).symm

theorem swap_14 [CharP K 2] (a u : K) :
    xp 1 a * xp 4 u = xp 7 (a * u ^ 2) * xp 3 (a ^ 2 * u) * (xp 4 u * xp 1 a) := by
  have h : RootOps.repCheck .G2 1 4 [(1, 1, 8, -2), (1, 2, 7, -3), (2, 1, 3, -3)] = true := by
    decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h a u
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  simp only [cast_neg_two_eq, cast_neg_three_eq, zero_mul, one_mul] at this
  refine swap_of_comm _ _ _ ?_
  rw [this]
  have h0 : xPar (rootOperatorFamily .G2) ((Tag.rootCertificate .G2).root 8) (0 : K) = 1 :=
    xp_zero 8
  rw [h0, one_mul]
  simp only [pow_one]

theorem swap_18 [CharP K 2] (a r : K) :
    xp 1 a * xp 8 r = xp 3 (a * r) * (xp 8 r * xp 1 a) := by
  have h : RootOps.repCheck .G2 1 8 [(1, 1, 3, 3)] = true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h a r
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  simp only [cast_three_eq, one_mul] at this
  refine swap_of_comm _ _ _ ?_
  rw [this]
  simp only [pow_one]

theorem swap_03 [CharP K 2] (s d : K) :
    xp 0 s * xp 3 d = xp 7 (s * d) * (xp 3 d * xp 0 s) := by
  have h : RootOps.repCheck .G2 0 3 [(1, 1, 7, 1)] = true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h s d
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  simp only [Int.cast_one, one_mul] at this
  refine swap_of_comm _ _ _ ?_
  rw [this]
  simp only [pow_one]

theorem swap_48 [CharP K 2] (u r : K) :
    xp 4 u * xp 8 r = xp 7 (u * r) * (xp 8 r * xp 4 u) := by
  have h : RootOps.repCheck .G2 4 8 [(1, 1, 7, 3)] = true := by decide +kernel
  have := Timmesfeld.RankTwo.commutator_xPar_of_repCheck (τ := .G2) (K := K) h u r
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at this
  simp only [cast_three_eq, one_mul] at this
  refine swap_of_comm _ _ _ ?_
  rw [this]
  simp only [pow_one]

theorem commute_check [CharP K 2] {a b : ℕ} (ha : a < 12) (hb : b < 12)
    (h : RootOps.repCheck .G2 a b [] = true) (x y : K) : Commute (xp a x) (xp b y) :=
  commute_of_check ha hb h _ ((mem_Xp_iff ha _).2 ⟨x, rfl⟩) _ ((mem_Xp_iff hb _).2 ⟨y, rfl⟩)

theorem commute_04 [CharP K 2] (x y : K) : Commute (xp 0 x) (xp 4 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_08 [CharP K 2] (x y : K) : Commute (xp 0 x) (xp 8 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_07 [CharP K 2] (x y : K) : Commute (xp 0 x) (xp 7 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_13 [CharP K 2] (x y : K) : Commute (xp 1 x) (xp 3 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_17 [CharP K 2] (x y : K) : Commute (xp 1 x) (xp 7 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_43 [CharP K 2] (x y : K) : Commute (xp 4 x) (xp 3 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_47 [CharP K 2] (x y : K) : Commute (xp 4 x) (xp 7 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_83 [CharP K 2] (x y : K) : Commute (xp 8 x) (xp 3 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_87 [CharP K 2] (x y : K) : Commute (xp 8 x) (xp 7 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

theorem commute_37 [CharP K 2] (x y : K) : Commute (xp 3 x) (xp 7 y) :=
  commute_check (by norm_num) (by norm_num) (by decide +kernel) x y

section Collection

theorem xp_merge (p : ℕ) (c d : K) (z : adjointGroup .G2 K) :
    xp p c * (xp p d * z) = xp p (c + d) * z := by
  rw [← mul_assoc, ← xp_add]

theorem xp_merge' (p : ℕ) (c d : K) : xp p c * xp p d = xp p (c + d) := (xp_add p c d).symm

theorem comm_tail {p q : ℕ} {x y : K} (h : Commute (xp p x) (xp q y))
    (z : adjointGroup .G2 K) : xp p x * (xp q y * z) = xp q y * (xp p x * z) := by
  rw [← mul_assoc, h.eq, mul_assoc]

theorem swap_inv {G : Type*} [Group G] (g h z : G) (hz : g * h = z * (h * g)) :
    h * g = z⁻¹ * (g * h) := (inv_mul_eq_iff_eq_mul.2 hz).symm

variable [CharP K 2]

theorem xp_cancel (p : ℕ) (c : K) (z : adjointGroup .G2 K) : xp p c * (xp p c * z) = z := by
  rw [xp_merge, CharTwo.add_self_eq_zero, xp_zero, one_mul]

theorem xp_cancel' (p : ℕ) (c : K) : xp p c * xp p c = 1 := xp_mul_self p c

theorem tail_40 (x y : K) (z : adjointGroup .G2 K) :
    xp 4 x * (xp 0 y * z) = xp 0 y * (xp 4 x * z) := comm_tail (commute_04 y x).symm z
theorem tail_80 (x y : K) (z : adjointGroup .G2 K) :
    xp 8 x * (xp 0 y * z) = xp 0 y * (xp 8 x * z) := comm_tail (commute_08 y x).symm z
theorem tail_70 (x y : K) (z : adjointGroup .G2 K) :
    xp 7 x * (xp 0 y * z) = xp 0 y * (xp 7 x * z) := comm_tail (commute_07 y x).symm z
theorem tail_31 (x y : K) (z : adjointGroup .G2 K) :
    xp 3 x * (xp 1 y * z) = xp 1 y * (xp 3 x * z) := comm_tail (commute_13 y x).symm z
theorem tail_71 (x y : K) (z : adjointGroup .G2 K) :
    xp 7 x * (xp 1 y * z) = xp 1 y * (xp 7 x * z) := comm_tail (commute_17 y x).symm z
theorem tail_34 (x y : K) (z : adjointGroup .G2 K) :
    xp 3 x * (xp 4 y * z) = xp 4 y * (xp 3 x * z) := comm_tail (commute_43 y x).symm z
theorem tail_74 (x y : K) (z : adjointGroup .G2 K) :
    xp 7 x * (xp 4 y * z) = xp 4 y * (xp 7 x * z) := comm_tail (commute_47 y x).symm z
theorem tail_38 (x y : K) (z : adjointGroup .G2 K) :
    xp 3 x * (xp 8 y * z) = xp 8 y * (xp 3 x * z) := comm_tail (commute_83 y x).symm z
theorem tail_78 (x y : K) (z : adjointGroup .G2 K) :
    xp 7 x * (xp 8 y * z) = xp 8 y * (xp 7 x * z) := comm_tail (commute_87 y x).symm z
theorem tail_73 (x y : K) (z : adjointGroup .G2 K) :
    xp 7 x * (xp 3 y * z) = xp 3 y * (xp 7 x * z) := comm_tail (commute_37 y x).symm z

theorem end_40 (x y : K) : xp 4 x * xp 0 y = xp 0 y * xp 4 x := (commute_04 y x).symm.eq
theorem end_80 (x y : K) : xp 8 x * xp 0 y = xp 0 y * xp 8 x := (commute_08 y x).symm.eq
theorem end_70 (x y : K) : xp 7 x * xp 0 y = xp 0 y * xp 7 x := (commute_07 y x).symm.eq
theorem end_31 (x y : K) : xp 3 x * xp 1 y = xp 1 y * xp 3 x := (commute_13 y x).symm.eq
theorem end_71 (x y : K) : xp 7 x * xp 1 y = xp 1 y * xp 7 x := (commute_17 y x).symm.eq
theorem end_34 (x y : K) : xp 3 x * xp 4 y = xp 4 y * xp 3 x := (commute_43 y x).symm.eq
theorem end_74 (x y : K) : xp 7 x * xp 4 y = xp 4 y * xp 7 x := (commute_47 y x).symm.eq
theorem end_38 (x y : K) : xp 3 x * xp 8 y = xp 8 y * xp 3 x := (commute_83 y x).symm.eq
theorem end_78 (x y : K) : xp 7 x * xp 8 y = xp 8 y * xp 7 x := (commute_87 y x).symm.eq
theorem end_73 (x y : K) : xp 7 x * xp 3 y = xp 3 y * xp 7 x := (commute_37 y x).symm.eq

theorem swap_41 (u a : K) :
    xp 4 u * xp 1 a = xp 7 (a * u ^ 2) * xp 3 (a ^ 2 * u) * (xp 1 a * xp 4 u) := by
  have h := swap_inv _ _ _ (swap_14 a u)
  rw [h]
  congr 1
  rw [mul_inv_rev, xp_inv, xp_inv]
  exact (commute_37 (a ^ 2 * u) (a * u ^ 2)).eq

theorem swap_81 (a r : K) : xp 8 r * xp 1 a = xp 3 (a * r) * (xp 1 a * xp 8 r) := by
  have h := swap_inv _ _ _ (swap_18 a r)
  rw [h, xp_inv]

theorem swap_30 (s d : K) : xp 3 d * xp 0 s = xp 7 (s * d) * (xp 0 s * xp 3 d) := by
  have h := swap_inv _ _ _ (swap_03 s d)
  rw [h, xp_inv]

theorem swap_84 (u r : K) : xp 8 r * xp 4 u = xp 7 (u * r) * (xp 4 u * xp 8 r) := by
  have h := swap_inv _ _ _ (swap_48 u r)
  rw [h, xp_inv]

theorem tail_10 (a s : K) (z : adjointGroup .G2 K) :
    xp 1 a * (xp 0 s * z) =
      xp 4 (a * s) * (xp 8 (a ^ 2 * s) * (xp 3 (a ^ 3 * s) * (xp 0 s * (xp 1 a * z)))) := by
  rw [← mul_assoc, swap_10]
  simp only [mul_assoc]

theorem tail_41 (u a : K) (z : adjointGroup .G2 K) :
    xp 4 u * (xp 1 a * z) =
      xp 7 (a * u ^ 2) * (xp 3 (a ^ 2 * u) * (xp 1 a * (xp 4 u * z))) := by
  rw [← mul_assoc, swap_41]
  simp only [mul_assoc]

theorem tail_81 (a r : K) (z : adjointGroup .G2 K) :
    xp 8 r * (xp 1 a * z) = xp 3 (a * r) * (xp 1 a * (xp 8 r * z)) := by
  rw [← mul_assoc, swap_81]
  simp only [mul_assoc]

theorem tail_30 (s d : K) (z : adjointGroup .G2 K) :
    xp 3 d * (xp 0 s * z) = xp 7 (s * d) * (xp 0 s * (xp 3 d * z)) := by
  rw [← mul_assoc, swap_30]
  simp only [mul_assoc]

theorem tail_84 (u r : K) (z : adjointGroup .G2 K) :
    xp 8 r * (xp 4 u * z) = xp 7 (u * r) * (xp 4 u * (xp 8 r * z)) := by
  rw [← mul_assoc, swap_84]
  simp only [mul_assoc]

theorem end_10 (a s : K) :
    xp 1 a * xp 0 s =
      xp 4 (a * s) * (xp 8 (a ^ 2 * s) * (xp 3 (a ^ 3 * s) * (xp 0 s * xp 1 a))) := by
  have := tail_10 a s 1
  simpa using this

theorem end_41 (u a : K) :
    xp 4 u * xp 1 a = xp 7 (a * u ^ 2) * (xp 3 (a ^ 2 * u) * (xp 1 a * xp 4 u)) := by
  have := tail_41 u a 1
  simpa using this

theorem end_81 (a r : K) : xp 8 r * xp 1 a = xp 3 (a * r) * (xp 1 a * xp 8 r) := by
  have := tail_81 a r 1
  simpa using this

theorem end_30 (s d : K) : xp 3 d * xp 0 s = xp 7 (s * d) * (xp 0 s * xp 3 d) := by
  have := tail_30 s d 1
  simpa using this

theorem end_84 (u r : K) : xp 8 r * xp 4 u = xp 7 (u * r) * (xp 4 u * xp 8 r) := by
  have := tail_84 u r 1
  simpa using this

end Collection

end CFSG.RankThree.PartOne.SEITZ6
