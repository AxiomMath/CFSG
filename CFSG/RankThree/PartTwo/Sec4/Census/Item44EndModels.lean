module

public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

section Homs

variable {T : Type*} [Group T]

private theorem pow_val_add_of_pow_eq_one {n : ℕ} [NeZero n] {x : T} (hx : x ^ n = 1)
    (i j : ZMod n) : x ^ (i + j).val = x ^ i.val * x ^ j.val := by
  rw [ZMod.val_add, ← pow_eq_pow_mod _ hx, pow_add]

private theorem pow_val_mul_eq_of_conj {n : ℕ} [NeZero n] {x s : T} (hx : x ^ n = 1)
    (hs : s * x * s⁻¹ = x⁻¹) (k : ZMod n) : x ^ k.val * s = s * x ^ (-k).val := by
  have h : s * x ^ (-k).val * s⁻¹ = x ^ k.val := by
    rw [← conj_pow, hs, inv_pow]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_val_add_of_pow_eq_one hx, neg_add_cancel, ZMod.val_zero, pow_zero]
  rw [← h, inv_mul_cancel_right]

private theorem pow_val_mul_mul_pow_val {n : ℕ} [NeZero n] {x s : T} (hx : x ^ n = 1)
    (hs : s * x * s⁻¹ = x⁻¹) (i j : ZMod n) :
    x ^ i.val * (s * x ^ j.val) = s * x ^ (j - i).val := by
  rw [← mul_assoc, pow_val_mul_eq_of_conj hx hs, mul_assoc, ← pow_val_add_of_pow_eq_one hx,
    neg_add_eq_sub]

private theorem mul_pow_val_mul_mul_pow_val {n : ℕ} [NeZero n] {x s : T} (hx : x ^ n = 1)
    (hs : s * x * s⁻¹ = x⁻¹) (i j : ZMod n) :
    s * x ^ i.val * (s * x ^ j.val) = s * s * x ^ (j - i).val := by
  rw [mul_assoc, pow_val_mul_mul_pow_val hx hs, ← mul_assoc]

private theorem pow_four_eq_one {x t : T} (hx : x ^ 4 = 1) (ht : t ^ 2 = x ^ 2) : t ^ 4 = 1 := by
  rw [show 4 = 2 * 2 from rfl, pow_mul, ht, ← pow_mul]
  exact hx

private def zmodFourHom {t : T} (ht : t ^ 4 = 1) : Multiplicative (ZMod 4) →* T where
  toFun k := t ^ k.toAdd.val
  map_one' := pow_zero t
  map_mul' a b := pow_val_add_of_pow_eq_one ht a.toAdd b.toAdd

private def quaternionHom {x y : T} (hx : x ^ 4 = 1) (hy : y ^ 2 = x ^ 2)
    (hyx : y * x * y⁻¹ = x⁻¹) : QuaternionGroup 2 →* T where
  toFun
    | .a i => x ^ i.val
    | .xa i => y * x ^ i.val
  map_one' := pow_zero x
  map_mul' := by
    have hx' : x ^ (2 * 2) = 1 := hx
    rintro (i | i) (j | j)
    · exact pow_val_add_of_pow_eq_one hx' i j
    · exact (pow_val_mul_mul_pow_val hx' hyx i j).symm
    · change y * x ^ (i + j).val = y * x ^ i.val * x ^ j.val
      rw [mul_assoc, pow_val_add_of_pow_eq_one hx']
    · change x ^ (((2 : ℕ) : ZMod (2 * 2)) + j - i).val = y * x ^ i.val * (y * x ^ j.val)
      rw [mul_pow_val_mul_mul_pow_val hx' hyx, ← sq y, hy, add_sub_assoc,
        pow_val_add_of_pow_eq_one hx', ZMod.val_natCast]

private def dihedralHom {w s : T} (hw : w ^ 4 = 1) (hs : s * s = 1)
    (hsw : s * w * s⁻¹ = w⁻¹) : DihedralGroup 4 →* T where
  toFun
    | .r i => w ^ i.val
    | .sr i => s * w ^ i.val
  map_one' := pow_zero w
  map_mul' := by
    rintro (i | i) (j | j)
    · exact pow_val_add_of_pow_eq_one hw i j
    · exact (pow_val_mul_mul_pow_val hw hsw i j).symm
    · change s * w ^ (i + j).val = s * w ^ i.val * w ^ j.val
      rw [mul_assoc, pow_val_add_of_pow_eq_one hw]
    · change w ^ (j - i).val = s * w ^ i.val * (s * w ^ j.val)
      rw [mul_pow_val_mul_mul_pow_val hw hsw, hs, one_mul]

private theorem commute_quaternionHom {x y t : T} (hx : x ^ 4 = 1) (hy : y ^ 2 = x ^ 2)
    (hyx : y * x * y⁻¹ = x⁻¹) (hxt : Commute x t) (hyt : Commute y t) (q : QuaternionGroup 2) :
    Commute (quaternionHom hx hy hyx q) t := by
  cases q with
  | a i => exact hxt.pow_left _
  | xa i => exact hyt.mul_left (hxt.pow_left _)

private theorem commute_dihedralHom {w s t : T} (hw : w ^ 4 = 1) (hs : s * s = 1)
    (hsw : s * w * s⁻¹ = w⁻¹) (hwt : Commute w t) (hst : Commute s t) (d : DihedralGroup 4) :
    Commute (dihedralHom hw hs hsw d) t := by
  cases d with
  | r i => exact hwt.pow_left _
  | sr i => exact hst.mul_left (hwt.pow_left _)

private theorem nonempty_mulEquiv_quotient {G : Type*} [Group G] [Finite G] {N : Subgroup G}
    [N.Normal] {Φ : G →* T} (hN : N ≤ Φ.ker) (hΦ : Function.Surjective Φ)
    (hcard : Nat.card G ≤ Nat.card T * Nat.card N) : Nonempty (T ≃* G ⧸ N) := by
  have hle : Nat.card (G ⧸ N) ≤ Nat.card T := by
    refine Nat.le_of_mul_le_mul_right ?_ (Nat.card_pos (α := N))
    rw [← Subgroup.card_eq_card_quotient_mul_card_subgroup]
    exact hcard
  exact ⟨(MulEquiv.ofBijective _
    ((QuotientGroup.lift_surjective_of_surjective N Φ hΦ hN).bijective_of_nat_card_le hle)).symm⟩

private theorem four_le_card {G : Type*} [Group G] [Finite G] [DecidableEq G] {H : Subgroup G}
    {a b : G} (ha : a ∈ H) (hb : b ∈ H) (hd : ({1, a, b, a * b} : Finset G).card = 4) :
    4 ≤ Nat.card H := by
  calc 4 = (({1, a, b, a * b} : Finset G) : Set G).ncard := by rw [Set.ncard_coe_finset, hd]
    _ ≤ (H : Set G).ncard := Set.ncard_le_ncard (by
          intro g hg
          simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
            Set.mem_singleton_iff] at hg
          rcases hg with rfl | rfl | rfl | rfl
          exacts [H.one_mem, ha, hb, H.mul_mem ha hb])
    _ = Nat.card H := (Nat.card_coe_set_eq _).symm

end Homs

theorem nonempty_mulEquiv_q8D8 {T : Type*} [Group T] [Finite T] (hT : Nat.card T = 32)
    {u v x y : T} (hu : u * u = 1) (hv : v * v = 1) (huv : (u * v) ^ 2 = x ^ 2)
    (hx4 : x ^ 4 = 1) (hx2 : x ^ 2 ≠ 1) (hy : y ^ 2 = x ^ 2) (hyx : y * x * y⁻¹ = x⁻¹)
    (hux : u * x = x * u) (huy : u * y = y * u) (hvx : v * x = x * v) (hvy : v * y = y * v)
    (hgen : Subgroup.closure {u, v, x, y} = ⊤) : Nonempty (T ≃* Q8D8) := by
  have _ := hx2
  have hw4 := pow_four_eq_one hx4 huv
  have huw : u * (u * v) * u⁻¹ = (u * v)⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hu, inv_eq_of_mul_eq_one_right hv, ← mul_assoc,
      hu, one_mul]
  let φ := quaternionHom hx4 hy hyx
  let ψ := dihedralHom hw4 hu huw
  have hcomm : ∀ q d, Commute (φ q) (ψ d) := fun q d =>
    commute_quaternionHom hx4 hy hyx
      (commute_dihedralHom hw4 hu huw (Commute.mul_left hux hvx) hux d).symm
      (commute_dihedralHom hw4 hu huw (Commute.mul_left huy hvy) huy d).symm q
  let Φ := φ.noncommCoprod ψ hcomm
  have hker : q8D8Kernel ≤ Φ.ker := by
    rw [q8D8Kernel, Subgroup.zpowers_le, MonoidHom.mem_ker]
    change x ^ 2 * (u * v) ^ 2 = 1
    rw [huv, ← pow_add]
    exact hx4
  have hsurj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      MonoidHom.mem_range]
    refine ⟨⟨(1, .sr 0), ?_⟩, ⟨(1, .sr 1), ?_⟩, ⟨(.a 1, 1), ?_⟩, ⟨(.xa 0, 1), ?_⟩⟩
    · change φ 1 * (u * (u * v) ^ 0) = u
      simp only [map_one, pow_zero, mul_one, one_mul]
    · change φ 1 * (u * (u * v) ^ 1) = v
      rw [map_one, one_mul, pow_one, ← mul_assoc, hu, one_mul]
    · change x ^ 1 * ψ 1 = x
      simp only [map_one, pow_one, mul_one]
    · change y * x ^ 0 * ψ 1 = y
      simp only [map_one, pow_zero, mul_one]
  have hG : Nat.card (QuaternionGroup 2 × DihedralGroup 4) = 64 := by
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card, DihedralGroup.card]
  have hN : Nat.card q8D8Kernel = 2 := by
    rw [q8D8Kernel, Nat.card_zpowers]
    exact orderOf_eq_prime (by decide) (by decide)
  exact nonempty_mulEquiv_quotient hker hsurj (by rw [hG, hT, hN])

theorem nonempty_mulEquiv_z4Q8Q8 {T : Type*} [Group T] [Finite T] (hT : Nat.card T = 64)
    {i x₁ y₁ x₂ y₂ : T} (hi : ∀ t : T, i * t = t * i) (hi2 : i ^ 2 = x₁ ^ 2)
    (hx₁ : x₁ ^ 4 = 1) (hx₁2 : x₁ ^ 2 ≠ 1) (hy₁ : y₁ ^ 2 = x₁ ^ 2) (hy₁x₁ : y₁ * x₁ * y₁⁻¹ = x₁⁻¹)
    (hx₂ : x₂ ^ 2 = x₁ ^ 2) (hy₂ : y₂ ^ 2 = x₁ ^ 2) (hy₂x₂ : y₂ * x₂ * y₂⁻¹ = x₂⁻¹)
    (h11 : x₁ * x₂ = x₂ * x₁) (h12 : x₁ * y₂ = y₂ * x₁) (h21 : y₁ * x₂ = x₂ * y₁)
    (h22 : y₁ * y₂ = y₂ * y₁)
    (hgen : Subgroup.closure {i, x₁, y₁, x₂, y₂} = ⊤) : Nonempty (T ≃* Z4Q8Q8) := by
  have _ := hx₁2
  have hx₂4 := pow_four_eq_one hx₁ hx₂
  have hy₂' : y₂ ^ 2 = x₂ ^ 2 := hy₂.trans hx₂.symm
  let ζ := zmodFourHom (pow_four_eq_one hx₁ hi2)
  let φ₁ := quaternionHom hx₁ hy₁ hy₁x₁
  let φ₂ := quaternionHom hx₂4 hy₂' hy₂x₂
  have hc : ∀ q q', Commute (φ₁ q) (φ₂ q') := fun q q' =>
    commute_quaternionHom hx₁ hy₁ hy₁x₁
      (commute_quaternionHom hx₂4 hy₂' hy₂x₂ (Commute.symm h11) (Commute.symm h12) q').symm
      (commute_quaternionHom hx₂4 hy₂' hy₂x₂ (Commute.symm h21) (Commute.symm h22) q').symm q
  let Φ₁₂ := φ₁.noncommCoprod φ₂ hc
  let Φ := ζ.noncommCoprod Φ₁₂ fun k p => (show Commute i (Φ₁₂ p) from hi _).pow_left _
  have hker : z4Q8Q8Kernel ≤ Φ.ker := by
    rw [z4Q8Q8Kernel, Subgroup.closure_le, Set.insert_subset_iff, Set.singleton_subset_iff]
    simp only [SetLike.mem_coe, MonoidHom.mem_ker]
    constructor
    · change i ^ 2 * (x₁ ^ 2 * φ₂ 1) = 1
      rw [map_one, mul_one, hi2, ← pow_add]
      exact hx₁
    · change i ^ 2 * (φ₁ 1 * x₂ ^ 2) = 1
      rw [map_one, one_mul, hi2, hx₂, ← pow_add]
      exact hx₁
  have hsurj : Function.Surjective Φ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hgen, Subgroup.closure_le]
    simp only [Set.insert_subset_iff, Set.singleton_subset_iff, SetLike.mem_coe,
      MonoidHom.mem_range]
    refine ⟨⟨(Multiplicative.ofAdd 1, 1), ?_⟩, ⟨(1, .a 1, 1), ?_⟩, ⟨(1, .xa 0, 1), ?_⟩,
      ⟨(1, 1, .a 1), ?_⟩, ⟨(1, 1, .xa 0), ?_⟩⟩
    · change i ^ 1 * Φ₁₂ 1 = i
      simp only [map_one, pow_one, mul_one]
    · change ζ 1 * (x₁ ^ 1 * φ₂ 1) = x₁
      simp only [map_one, pow_one, mul_one, one_mul]
    · change ζ 1 * (y₁ * x₁ ^ 0 * φ₂ 1) = y₁
      simp only [map_one, pow_zero, mul_one, one_mul]
    · change ζ 1 * (φ₁ 1 * x₂ ^ 1) = x₂
      simp only [map_one, pow_one, one_mul]
    · change ζ 1 * (φ₁ 1 * (y₂ * x₂ ^ 0)) = y₂
      simp only [map_one, pow_zero, mul_one, one_mul]
  have hG : Nat.card (Multiplicative (ZMod 4) × QuaternionGroup 2 × QuaternionGroup 2) = 256 := by
    simp [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hN : 4 ≤ Nat.card z4Q8Q8Kernel := by
    refine four_le_card (a := (Multiplicative.ofAdd 2, .a 2, 1))
      (b := (Multiplicative.ofAdd 2, 1, .a 2)) ?_ ?_ (by decide) <;>
      rw [z4Q8Q8Kernel] <;> exact Subgroup.subset_closure (by simp)
  exact nonempty_mulEquiv_quotient hker hsurj (by rw [hG, hT]; omega)

end CFSG.RankThree.PartTwo.Sec4.Census
