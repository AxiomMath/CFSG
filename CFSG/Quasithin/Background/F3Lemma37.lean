module

public import CFSG.Quasithin.Background.F3Polygon
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

namespace Lemma37

variable (s t : H) (x l c : V)

@[expose] def base (i : ℤ) : V :=
  if i = 0 then x else if i = 1 then l else if i = 2 then t • x else t • c

@[expose] def seq (k : ℤ) : V := (t * s) ^ (k / 4) • base t x l c (k % 4)

theorem seq_block (j i : ℤ) (h0 : 0 ≤ i) (h4 : i < 4) :
    seq s t x l c (4 * j + i) = (t * s) ^ j • base t x l c i := by
  unfold seq
  rw [show (4 * j + i) / 4 = j by omega, show (4 * j + i) % 4 = i by omega]

theorem seq_0 (j : ℤ) : seq s t x l c (4 * j) = (t * s) ^ j • x := by
  have := seq_block s t x l c j 0 le_rfl (by norm_num)
  simpa [base] using this

theorem seq_1 (j : ℤ) : seq s t x l c (4 * j + 1) = (t * s) ^ j • l := by
  have := seq_block s t x l c j 1 (by norm_num) (by norm_num)
  simpa [base] using this

theorem seq_2 (j : ℤ) : seq s t x l c (4 * j + 2) = (t * s) ^ j • t • x := by
  have := seq_block s t x l c j 2 (by norm_num) (by norm_num)
  simpa [base] using this

theorem seq_3 (j : ℤ) : seq s t x l c (4 * j + 3) = (t * s) ^ j • t • c := by
  have := seq_block s t x l c j 3 (by norm_num) (by norm_num)
  simpa [base] using this

variable {s t x l c}

theorem exists_block (k : ℤ) :
    ∃ j : ℤ, k = 4 * j ∨ k = 4 * j + 1 ∨ k = 4 * j + 2 ∨ k = 4 * j + 3 :=
  ⟨k / 4, by omega⟩

theorem rot_smul (j : ℤ) (y : V) : (t * s) • (t * s) ^ j • y = (t * s) ^ (j + 1) • y := by
  rw [← mul_smul, ← zpow_one_add, add_comm]

theorem zpow_smul_comm (hs : s * s = 1) (ht : t * t = 1) (j : ℤ) (y : V) :
    s • (t * s) ^ j • y = (t * s) ^ (-j) • s • y := by
  rw [← mul_smul, s_mul_zpow hs ht, mul_smul]

theorem zpow_pred_smul (j : ℤ) (y : V) :
    (t * s) ^ (-j - 1) • y = (t * s) ^ (-j) • (t * s)⁻¹ • y := by
  rw [← mul_smul, ← zpow_neg_one, ← zpow_add]
  congr 2

theorem zpow_pred_pred_smul (j : ℤ) (y : V) :
    (t * s) ^ (-j - 2) • y = (t * s) ^ (-j) • (t * s)⁻¹ • (t * s)⁻¹ • y := by
  rw [← mul_smul, ← mul_smul, ← zpow_neg_one, ← zpow_add, ← zpow_add]
  congr 2
  ring

variable (hs : s * s = 1) (ht : t * t = 1) (hxl : Γ.Adj x l) (hxc : Γ.Adj x c) (hlc : l ≠ c)
  (hsc : s • c = c) (htl : t • l = l) (hsx : s • x ≠ x) (htx : t • x ≠ x)

include hs ht hxl hxc hlc hsc htl hsx htx in
theorem dihedralSeq : DihedralSeq Γ s t (seq s t x l c) 4 (-2) where
  adj k := by
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ := exists_block k
    · rw [seq_0, seq_1]
      exact (GraphAction.adj_smul _ _ _).mpr hxl
    · rw [seq_1, show 4 * j + 1 + 1 = 4 * j + 2 by ring, seq_2]
      refine (GraphAction.adj_smul _ _ _).mpr ?_
      have := (GraphAction.adj_smul t x l).mpr hxl
      rw [htl] at this
      exact this.symm
    · rw [seq_2, show 4 * j + 2 + 1 = 4 * j + 3 by ring, seq_3]
      exact (GraphAction.adj_smul _ _ _).mpr ((GraphAction.adj_smul t x c).mpr hxc)
    · rw [seq_3, show 4 * j + 3 + 1 = 4 * (j + 1) by ring, seq_0, zpow_add_one, mul_smul,
        mul_smul t s x]
      refine (GraphAction.adj_smul _ _ _).mpr ((GraphAction.adj_smul t c (s • x)).mpr ?_)
      have := (GraphAction.adj_smul s x c).mpr hxc
      rw [hsc] at this
      exact this.symm
  nb k := by
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ := exists_block k
    · rw [seq_0, seq_2]
      intro h
      exact htx (smul_left_cancel _ h).symm
    · rw [show 4 * j + 1 + 2 = 4 * j + 3 by ring, seq_1, seq_3]
      intro h
      have h1 := smul_left_cancel _ h
      apply hlc
      have h2 : t • l = t • t • c := congrArg (fun v => t • v) h1
      rw [htl, ← mul_smul, ht, one_smul] at h2
      exact h2
    · rw [show 4 * j + 2 + 2 = 4 * (j + 1) by ring, seq_2, seq_0, zpow_add_one, mul_smul,
        mul_smul t s x]
      intro h
      exact hsx (smul_left_cancel _ (smul_left_cancel _ h)).symm
    · rw [show 4 * j + 3 + 2 = 4 * (j + 1) + 1 by ring, seq_3, seq_1, zpow_add_one, mul_smul,
        mul_smul t s l]
      intro h
      have h1 := smul_left_cancel _ (smul_left_cancel _ h)
      apply hlc
      have h2 : s • c = s • s • l := congrArg (fun v => s • v) h1
      rw [hsc, ← mul_smul, hs, one_smul] at h2
      exact h2.symm
  rot k := by
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ := exists_block k
    · rw [seq_0, rot_smul, show 4 * j + ((4 : ℕ) : ℤ) = 4 * (j + 1) by push_cast; ring, seq_0]
    · rw [seq_1, rot_smul, show 4 * j + 1 + ((4 : ℕ) : ℤ) = 4 * (j + 1) + 1 by push_cast; ring,
        seq_1]
    · rw [seq_2, rot_smul, show 4 * j + 2 + ((4 : ℕ) : ℤ) = 4 * (j + 1) + 2 by push_cast; ring,
        seq_2]
    · rw [seq_3, rot_smul, show 4 * j + 3 + ((4 : ℕ) : ℤ) = 4 * (j + 1) + 3 by push_cast; ring,
        seq_3]
  refl k := by
    have e0 : s • x = (t * s)⁻¹ • t • x := by
      rw [inv_rot_eq hs ht, mul_smul, ← mul_smul t t, ht, one_smul]
    have e1 : s • l = (t * s)⁻¹ • l := by
      rw [inv_rot_eq hs ht, mul_smul, htl]
    have e2 : s • t • x = (t * s)⁻¹ • x := by
      rw [inv_rot_eq hs ht, mul_smul]
    have e3 : s • t • c = (t * s)⁻¹ • (t * s)⁻¹ • t • c := by
      have h : (s * t) • t • c = c := by rw [mul_smul, ← mul_smul t t, ht, one_smul, hsc]
      rw [inv_rot_eq hs ht, h, mul_smul]
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ := exists_block k
    · rw [seq_0, zpow_smul_comm hs ht, e0, show (-2 : ℤ) - 4 * j = 4 * (-j - 1) + 2 by ring,
        seq_2, zpow_pred_smul]
    · rw [seq_1, zpow_smul_comm hs ht, e1, show (-2 : ℤ) - (4 * j + 1) = 4 * (-j - 1) + 1 by ring,
        seq_1, zpow_pred_smul]
    · rw [seq_2, zpow_smul_comm hs ht, e2, show (-2 : ℤ) - (4 * j + 2) = 4 * (-j - 1) by ring,
        seq_0, zpow_pred_smul]
    · rw [seq_3, zpow_smul_comm hs ht, e3, show (-2 : ℤ) - (4 * j + 3) = 4 * (-j - 2) + 3 by ring,
        seq_3, zpow_pred_pred_smul]

theorem rot_zpow_smul_eq {n : ℕ} {y : V} (hs : s * s = 1) (ht : t * t = 1)
    (hy : (s * t) ^ n • y = y) : (t * s) ^ (n : ℤ) • y = y := by
  rw [zpow_natCast, rot_pow_eq_inv hs ht, inv_smul_eq_iff]
  exact hy.symm

theorem rot_zpow_smul_t_eq {n : ℕ} {y : V} (hs : s * s = 1) (ht : t * t = 1)
    (hy : (s * t) ^ n • y = y) : (t * s) ^ (n : ℤ) • t • y = t • y := by
  have h1 : (t * s) ^ (-(n : ℤ)) • y = y := by
    rw [zpow_neg, inv_smul_eq_iff]
    exact (rot_zpow_smul_eq hs ht hy).symm
  rw [← mul_smul, ← neg_neg (n : ℤ), ← t_mul_zpow hs ht, mul_smul, h1]

include hs ht hxl hxc hlc hsc htl hsx htx in
theorem lemma_F37 {col : V → Bool} (hΓ : Γ.Connected) (hcol : ∀ a b, Γ.Adj a b → col a ≠ col b)
    {m : ℕ} (hm4 : 4 ≤ m) (hmeven : Even m) (hU : UniqueGeod Γ m) {n : ℕ} (hn : 0 < n)
    (hnm : n ≤ m / 2) (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l)
    (hcc : (s * t) ^ n • c = c) :
    n = m / 2 ∧
      IsPolygon Γ (MulAction.orbit (Subgroup.closure {s, t}) x ∪
        MulAction.orbit (Subgroup.closure {s, t}) l ∪
        MulAction.orbit (Subgroup.closure {s, t}) c) (2 * m) ∧
      (∀ w ∈ Subgroup.closure {s, t},
        (∀ v ∈ MulAction.orbit (Subgroup.closure {s, t}) x ∪
          MulAction.orbit (Subgroup.closure {s, t}) l ∪
          MulAction.orbit (Subgroup.closure {s, t}) c, w • v = v) ↔
          w ∈ Subgroup.zpowers ((s * t) ^ n)) ∧
      (Subgroup.zpowers ((s * t) ^ n)).relIndex (Subgroup.closure {s, t}) = 2 * n := by
  have D := dihedralSeq hs ht hxl hxc hlc hsc htl hsx htx
  obtain ⟨h, rfl⟩ := hmeven
  have hper : ∀ n : ℕ, (s * t) ^ n • x = x → (s * t) ^ n • l = l → (s * t) ^ n • c = c →
      ∀ k : ℤ, seq s t x l c (k + ((4 * n : ℕ) : ℤ)) = seq s t x l c k := by
    intro n hx hl hcc k
    obtain ⟨j, rfl | rfl | rfl | rfl⟩ := exists_block k
    · rw [show 4 * j + ((4 * n : ℕ) : ℤ) = 4 * (j + n) by push_cast; ring, seq_0, seq_0, zpow_add,
        mul_smul, rot_zpow_smul_eq hs ht hx]
    · rw [show 4 * j + 1 + ((4 * n : ℕ) : ℤ) = 4 * (j + n) + 1 by push_cast; ring, seq_1, seq_1,
        zpow_add, mul_smul, rot_zpow_smul_eq hs ht hl]
    · rw [show 4 * j + 2 + ((4 * n : ℕ) : ℤ) = 4 * (j + n) + 2 by push_cast; ring, seq_2, seq_2,
        zpow_add, mul_smul, rot_zpow_smul_t_eq hs ht hx]
    · rw [show 4 * j + 3 + ((4 * n : ℕ) : ℤ) = 4 * (j + n) + 3 by push_cast; ring, seq_3, seq_3,
        zpow_add, mul_smul, rot_zpow_smul_t_eq hs ht hcc]
  have hnm' : n = (h + h) / 2 := by
    have h2n := GPath.two_mul_le_of_periodic hΓ hcol hU (fun i : ℕ => seq s t x l c (i : ℤ))
      D.adj_nat D.nb_nat (M := 4 * n) (by omega)
      (DihedralSeq.per_nat (hper n hx hl hcc))
    omega
  have hnh : n = h := by omega
  have hperm : ∀ k : ℤ, seq s t x l c (k + ((2 * (h + h) : ℕ) : ℤ)) = seq s t x l c k := by
    intro k
    rw [show ((2 * (h + h) : ℕ) : ℤ) = ((4 * n : ℕ) : ℤ) by congr 1; omega]
    exact hper n hx hl hcc k
  set W := Subgroup.closure {s, t} with hW
  have hs' : s ∈ W := Subgroup.subset_closure (by simp)
  have ht' : t ∈ W := Subgroup.subset_closure (by simp)
  have hr : t * s ∈ W := Subgroup.mul_mem _ ht' hs'
  have h0 : seq s t x l c 0 = x := by simpa using seq_0 s t x l c 0
  have h1 : seq s t x l c 1 = l := by simpa using seq_1 s t x l c 0
  have hm1 : seq s t x l c (-1) = c := by
    have := seq_3 s t x l c (-1)
    rw [show 4 * (-1 : ℤ) + 3 = -1 by norm_num, zpow_neg_one, inv_rot_eq hs ht] at this
    rw [this, mul_smul, ← mul_smul t t, ht, one_smul, hsc]
  have hrange : Set.range (seq s t x l c) = MulAction.orbit W x ∪ MulAction.orbit W l ∪
      MulAction.orbit W c := by
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨j, rfl | rfl | rfl | rfl⟩ := exists_block k
      · left; left
        rw [seq_0]
        exact ⟨⟨(t * s) ^ j, Subgroup.zpow_mem _ hr j⟩, rfl⟩
      · left; right
        rw [seq_1]
        exact ⟨⟨(t * s) ^ j, Subgroup.zpow_mem _ hr j⟩, rfl⟩
      · left; left
        rw [seq_2, ← mul_smul]
        exact ⟨⟨(t * s) ^ j * t, Subgroup.mul_mem _ (Subgroup.zpow_mem _ hr j) ht'⟩, rfl⟩
      · right
        rw [seq_3, ← mul_smul]
        exact ⟨⟨(t * s) ^ j * t, Subgroup.mul_mem _ (Subgroup.zpow_mem _ hr j) ht'⟩, rfl⟩
    · rintro ((⟨⟨w, hw⟩, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩) | ⟨⟨w, hw⟩, rfl⟩)
      · obtain ⟨k', hk'⟩ := D.smul_mem_range hs ht hw 0
        rw [h0] at hk'
        exact ⟨k', hk'.symm⟩
      · obtain ⟨k', hk'⟩ := D.smul_mem_range hs ht hw 1
        rw [h1] at hk'
        exact ⟨k', hk'.symm⟩
      · obtain ⟨k', hk'⟩ := D.smul_mem_range hs ht hw (-1)
        rw [hm1] at hk'
        exact ⟨k', hk'.symm⟩
  have hu := fun i j => D.u_eq_iff hΓ hcol (by omega) hU hperm i j
  have hzp : Subgroup.zpowers ((s * t) ^ n) = Subgroup.zpowers ((t * s) ^ (n : ℤ)) := by
    have e : (s * t) ^ n = ((t * s) ^ n)⁻¹ := by
      rw [rot_pow_eq_inv hs ht, inv_inv]
    rw [e, Subgroup.zpowers_inv, zpow_natCast]
  refine ⟨hnm', ?_, ?_, ?_⟩
  · rw [← hrange]
    exact D.isPolygon hΓ hcol (by omega) hU hperm
  · intro w hw
    have key := D.fixes_iff_mem_zpowers hs ht (N := 2 * (h + h)) (n := n) (by norm_num)
      (by push_cast; omega) (by omega) hu hw
    rw [← hrange, Set.forall_mem_range, key, hzp]
  · rw [hzp]
    exact D.relIndex_eq hs ht (N := 2 * (h + h)) (n := n) hn (by norm_num)
      (by push_cast; omega) (by omega) hu

end Lemma37

end CFSG.Quasithin
