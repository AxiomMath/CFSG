module

public import CFSG.RankThree.Asc83Table.Extraspecial
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.Extraspecial

open Subgroup CFSG.ABGLocalTools
open CFSG.RankThree.Asc83Table (commutator_ne_one_of_card commutator_pow_three
  eq_of_le_of_card_eq_nine y_pow_mul_x_pow)
open scoped commutatorElement

variable {G : Type*} [Group G] {x y : G}

theorem normalForm_mul_normalForm (hx : x ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x)
    (hzy : Commute ⁅x, y⁆ y) (i j k i' j' k' : ℕ) :
    x ^ i * y ^ j * ⁅x, y⁆ ^ k * (x ^ i' * y ^ j' * ⁅x, y⁆ ^ k') =
      x ^ (i + i') * y ^ (j + j') * ⁅x, y⁆ ^ (k + k' + 2 * i' * j) := by
  have hc : Commute (⁅x, y⁆ ^ k) (x ^ i' * y ^ j') :=
    (hzx.pow_left _).pow_right _ |>.mul_right ((hzy.pow_left _).pow_right _)
  have hc2 : Commute (⁅x, y⁆ ^ (2 * i' * j)) (y ^ j') := (hzy.pow_left _).pow_right _
  calc x ^ i * y ^ j * ⁅x, y⁆ ^ k * (x ^ i' * y ^ j' * ⁅x, y⁆ ^ k')
      = x ^ i * y ^ j * (⁅x, y⁆ ^ k * (x ^ i' * y ^ j')) * ⁅x, y⁆ ^ k' := by
        simp only [mul_assoc]
    _ = x ^ i * (y ^ j * x ^ i') * y ^ j' * (⁅x, y⁆ ^ k * ⁅x, y⁆ ^ k') := by
        rw [hc.eq]; simp only [mul_assoc]
    _ = x ^ i * x ^ i' * y ^ j * (⁅x, y⁆ ^ (2 * i' * j) * y ^ j') *
          (⁅x, y⁆ ^ k * ⁅x, y⁆ ^ k') := by
        rw [y_pow_mul_x_pow hx hzx hzy]; simp only [mul_assoc]
    _ = x ^ (i + i') * y ^ (j + j') * ⁅x, y⁆ ^ (k + k' + 2 * i' * j) := by
        rw [hc2.eq, show k + k' + 2 * i' * j = 2 * i' * j + (k + k') by ring, pow_add x,
          pow_add y, pow_add ⁅x, y⁆ (2 * i' * j), pow_add ⁅x, y⁆ k]
        simp only [mul_assoc]

section Subgroups

variable (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
  (hcard : Nat.card (closure ({x, y} : Set G)) = 27)
include hx hy hzx hzy hcard

theorem not_commute_normalForm {i j k i' j' k' : ℕ} (h : (i * j' : ZMod 3) ≠ i' * j) :
    ¬ Commute (x ^ i * y ^ j * ⁅x, y⁆ ^ k) (x ^ i' * y ^ j' * ⁅x, y⁆ ^ k') := by
  intro hc
  have he := hc.eq
  rw [normalForm_mul_normalForm hx hzx hzy, normalForm_mul_normalForm hx hzx hzy, add_comm i',
    add_comm j'] at he
  have hord : orderOf ⁅x, y⁆ = 3 := orderOf_eq_prime (commutator_pow_three hx hzx)
    (commutator_ne_one_of_card hx hy hzx hzy hcard)
  have hm := pow_eq_pow_iff_modEq.1 (mul_left_cancel he)
  rw [hord, ← ZMod.natCast_eq_natCast_iff] at hm
  push_cast at hm
  have h2 : (2 : ZMod 3) * i' * j = 2 * i * j' := by linear_combination hm
  have key : ∀ a b c d : ZMod 3, 2 * c * b = 2 * a * d → a * d = c * b := by decide
  exact h (key _ _ _ _ h2)

theorem exists_mem_conj_not_mem {h : G} {a b c d k l : ℕ}
    (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l)
    (hlines : ∀ i j : ZMod 3, i * (i * b + j * d) = j * (i * a + j * c) → i = 0 ∧ j = 0)
    {B : Subgroup G} (hB : B ≤ closure {x, y}) (hB9 : Nat.card B = 9) :
    ∃ q ∈ B, h * q * h⁻¹ ∉ B := by
  have hnc := @not_commute_normalForm G _ x y hx hy hzx hzy hcard
  have h10 : (1 : ZMod 3) ≠ 0 := by decide
  have hxy : h * (x * y) * h⁻¹ = h * x * h⁻¹ * (h * y * h⁻¹) := by group
  have hxy2 : h * (x * y ^ 2) * h⁻¹ = h * x * h⁻¹ * (h * y * h⁻¹) * (h * y * h⁻¹) := by
    simp only [sq, mul_assoc, inv_mul_cancel_left]
  have nf := normalForm_mul_normalForm hx hzx hzy
  have hcomm : ∀ {u v : G}, Commute ⁅x, y⁆ u → v ∈ closure ({⁅x, y⁆, u} : Set G) →
      Commute u v := fun {u _} hzu hv =>
    mem_centralizer_iff.1 (closure_le_centralizer_centralizer _ hv) u
      (mem_centralizer_iff.2 (by rintro w (rfl | rfl); exacts [hzu.eq, rfl]))
  rcases eq_of_le_of_card_eq_nine hx hy hzx hzy hcard hB hB9 with rfl | rfl | rfl | rfl
  · refine ⟨x, subset_closure (by simp), fun hm => ?_⟩
    have := @hnc 1 0 0 a b k
      (fun he => h10 (hlines 1 0 (by push_cast at he ⊢; linear_combination he)).1)
    simp only [pow_one, pow_zero, mul_one] at this
    exact this (hhx ▸ hcomm hzx hm)
  · refine ⟨y, subset_closure (by simp), fun hm => ?_⟩
    have := @hnc 0 1 0 c d l
      (fun he => h10 (hlines 0 1 (by push_cast at he ⊢; linear_combination he)).2)
    simp only [pow_one, pow_zero, mul_one, one_mul] at this
    exact this (hhy ▸ hcomm hzy hm)
  · refine ⟨x * y, subset_closure (by simp), fun hm => ?_⟩
    have hc := hcomm (hzx.mul_right hzy) hm
    rw [hxy, hhx, hhy, nf] at hc
    have := @hnc 1 1 0 (a + c) (b + d) (k + l + 2 * c * b)
      (fun he => h10 (hlines 1 1 (by push_cast at he ⊢; linear_combination he)).1)
    simp only [pow_one, pow_zero, mul_one] at this
    exact this hc
  · refine ⟨x * y ^ 2, subset_closure (by simp), fun hm => ?_⟩
    have hc := hcomm (hzx.mul_right (hzy.pow_right 2)) hm
    rw [hxy2, hhx, hhy, nf, nf] at hc
    have := @hnc 1 2 0 (a + c + c) (b + d + d) (k + l + 2 * c * b + l + 2 * c * (b + d))
      (fun he => h10 (hlines 1 2 (by push_cast at he ⊢; linear_combination he)).1)
    simp only [pow_one, pow_zero, mul_one] at this
    exact this hc

end Subgroups

theorem exists_normalizer_not_mem_of_isSylowOf [Finite G] {p n : ℕ} [Fact p.Prime]
    {P : Subgroup G} (hP : IsSylowOf p P ⊤)
    (hmove : ∀ Q : Subgroup G, Q ≤ P → Nat.card Q = n →
      ∃ g ∈ normalizer (P : Set G), ∃ q ∈ Q, g⁻¹ * q * g ∉ Q)
    {S Q : Subgroup G} (hS : IsSylowOf p S ⊤) (hQS : Q ≤ S) (hQ : Nat.card Q = n) :
    ∃ g ∈ normalizer (S : Set G), ∃ q ∈ Q, g⁻¹ * q * g ∉ Q := by
  let P' : Sylow p G := Sylow.ofCard P (by rw [hP.card_eq, card_top])
  let S' : Sylow p G := Sylow.ofCard S (by rw [hS.card_eq, card_top])
  obtain ⟨k, hkS⟩ := MulAction.exists_smul_eq G P' S'
  have hk : ∀ w, w ∈ S ↔ k⁻¹ * w * k ∈ P := fun w => by
    have hS' : S = ((k • P' : Sylow p G) : Subgroup G) := by rw [hkS]; rfl
    rw [hS', Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      MulAut.smul_def, MulAut.conj_inv_apply]
    rfl
  set Q' := Q.map (MulAut.conj k⁻¹).toMonoidHom
  have hmem : ∀ w, w ∈ Q' ↔ k * w * k⁻¹ ∈ Q := fun w => by
    rw [mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
  have hQ'P : Q' ≤ P := fun w hw => by
    simpa [mul_assoc] using (hk _).1 (hQS ((hmem w).1 hw))
  obtain ⟨g', hg', q', hq', hnot⟩ := hmove Q' hQ'P
    (by rw [card_map_of_injective (MulAut.conj k⁻¹).injective, hQ])
  refine ⟨k * g' * k⁻¹, mem_normalizer_iff.2 fun w => ?_, k * q' * k⁻¹, (hmem q').1 hq', ?_⟩
  · rw [hk, hk, show k⁻¹ * (k * g' * k⁻¹ * w * (k * g' * k⁻¹)⁻¹) * k =
      g' * (k⁻¹ * w * k) * g'⁻¹ by group]
    exact mem_normalizer_iff.1 hg' _
  · rw [show (k * g' * k⁻¹)⁻¹ * (k * q' * k⁻¹) * (k * g' * k⁻¹) =
      k * (g'⁻¹ * q' * g') * k⁻¹ by group, ← hmem]
    exact hnot

theorem exists_normalizer_not_mem_of_cubic [Finite G] {h : G} {a b c d k l m : ℕ}
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcard : Nat.card (closure ({x, y} : Set G)) = 3 ^ 3) (hG : Nat.card G = 3 ^ 3 * m)
    (hm : ¬ 3 ∣ m) (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l)
    (hlines : ∀ i j : ZMod 3, i * (i * b + j * d) = j * (i * a + j * c) → i = 0 ∧ j = 0)
    (S Q : Subgroup G) (hS : IsSylowOf 3 S ⊤) (hQS : Q ≤ S) (hQ : Nat.card Q = 9) :
    ∃ g ∈ normalizer (S : Set G), ∃ q ∈ Q, g⁻¹ * q * g ∉ Q := by
  set P := closure ({x, y} : Set G)
  have hfac : (3 ^ 3 * m).factorization 3 = 3 := by
    rw [Nat.factorization_mul (by positivity) (by rintro rfl; exact hm (dvd_zero 3)),
      Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, Nat.factorization_eq_zero_of_not_dvd hm]
  have hP : IsSylowOf 3 P ⊤ := isSylowOf_of_card le_top (by rw [hcard, card_top, hG, hfac])
  have hxP : x ∈ P := subset_closure (by simp)
  have hyP : y ∈ P := subset_closure (by simp)
  have hzP : ⁅x, y⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem hxP hyP) (P.inv_mem hxP)) (P.inv_mem hyP)
  have hconj : P.map (MulAut.conj h).toMonoidHom ≤ P := by
    rw [MonoidHom.map_closure, closure_le, Set.image_pair]
    rintro _ (rfl | rfl)
    · change h * x * h⁻¹ ∈ P
      rw [hhx]
      exact P.mul_mem (P.mul_mem (P.pow_mem hxP _) (P.pow_mem hyP _)) (P.pow_mem hzP _)
    · change h * y * h⁻¹ ∈ P
      rw [hhy]
      exact P.mul_mem (P.mul_mem (P.pow_mem hxP _) (P.pow_mem hyP _)) (P.pow_mem hzP _)
  have hN : h⁻¹ ∈ normalizer (P : Set G) :=
    inv_mem (mem_normalizer_fintype fun w hw => hconj (mem_map_of_mem _ hw))
  refine exists_normalizer_not_mem_of_isSylowOf hP (fun B hBP hB9 => ?_) hS hQS hQ
  obtain ⟨q, hq, hnot⟩ := exists_mem_conj_not_mem hx hy hzx hzy (hcard.trans (by norm_num)) hhx
    hhy hlines hBP hB9
  exact ⟨h⁻¹, hN, q, hq, by rwa [inv_inv]⟩

theorem exists_normalizer_not_mem_of_mulEquiv {X Y : Type*} [Group X] [Finite X] [Group Y]
    (e : X ≃* Y) {x y h : Y} {a b c d k l m : ℕ} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y)
    (hcard : Nat.card (closure ({x, y} : Set Y)) = 3 ^ 3) (hY : Nat.card Y = 3 ^ 3 * m)
    (hm : ¬ 3 ∣ m) (hhx : h * x * h⁻¹ = x ^ a * y ^ b * ⁅x, y⁆ ^ k)
    (hhy : h * y * h⁻¹ = x ^ c * y ^ d * ⁅x, y⁆ ^ l)
    (hlines : ∀ i j : ZMod 3, i * (i * b + j * d) = j * (i * a + j * c) → i = 0 ∧ j = 0)
    (S Q : Subgroup X) (hS : IsSylowOf 3 S ⊤) (hQS : Q ≤ S) (hQ : Nat.card Q = 9) :
    ∃ g ∈ normalizer (S : Set X), ∃ q ∈ Q, g⁻¹ * q * g ∉ Q := by
  have hcl : closure ({e.symm x, e.symm y} : Set X) =
      (closure ({x, y} : Set Y)).map e.symm.toMonoidHom := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hconj : ∀ w : Y, e.symm h * e.symm w * (e.symm h)⁻¹ = e.symm (h * w * h⁻¹) := fun w => by
    simp only [map_mul, map_inv]
  refine exists_normalizer_not_mem_of_cubic (x := e.symm x) (y := e.symm y) (h := e.symm h)
    (k := k) (l := l)
    (by rw [← map_pow, hx, map_one]) (by rw [← map_pow, hy, map_one])
    (by rw [← map_commutatorElement]; exact hzx.map e.symm)
    (by rw [← map_commutatorElement]; exact hzy.map e.symm)
    (by rw [hcl, card_map_of_injective e.symm.injective, hcard])
    ((Nat.card_congr e.toEquiv).trans hY) hm ?_ ?_ hlines S Q hS hQS hQ
  · rw [hconj, hhx, ← map_commutatorElement]
    simp only [map_mul, map_pow]
  · rw [hconj, hhy, ← map_commutatorElement]
    simp only [map_mul, map_pow]

end CFSG.Extraspecial
