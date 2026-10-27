module

public import CFSG.Quasithin.Background.F3Polygon
public import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Quasithin

universe u

variable {V : Type u} {Γ : SimpleGraph V} {H : Type*} [Group H] [MulAction H V] [GraphAction H Γ]

namespace Lemma36

variable (s t : H) (x l : V)

@[expose] def seq (k : ℤ) : V := (t * s) ^ (k / 2) • (if k % 2 = 0 then x else l)

theorem seq_even (j : ℤ) : seq s t x l (2 * j) = (t * s) ^ j • x := by
  unfold seq
  rw [show 2 * j / 2 = j by omega]
  simp [show 2 * j % 2 = 0 by omega]

theorem seq_odd (j : ℤ) : seq s t x l (2 * j + 1) = (t * s) ^ j • l := by
  unfold seq
  rw [show (2 * j + 1) / 2 = j by omega]
  simp

variable {s t x l}

theorem rot_smul (j : ℤ) (y : V) : (t * s) • (t * s) ^ j • y = (t * s) ^ (j + 1) • y := by
  rw [← mul_smul, ← zpow_one_add, add_comm]

theorem zpow_smul_comm (hs : s * s = 1) (ht : t * t = 1) (j : ℤ) (y : V) :
    s • (t * s) ^ j • y = (t * s) ^ (-j) • s • y := by
  rw [← mul_smul, s_mul_zpow hs ht, mul_smul]

variable (hs : s * s = 1) (ht : t * t = 1) (hxl : Γ.Adj x l) (hsx : s • x = x) (htl : t • l = l)
  (hsl : s • l ≠ l) (htx : t • x ≠ x)

include hxl htl in
theorem adj_aux : Γ.Adj l (t • x) := by
  have := (GraphAction.adj_smul t x l).mpr hxl
  rw [htl] at this
  exact this.symm

include hs ht hxl hsx htl hsl htx in
theorem dihedralSeq : DihedralSeq Γ s t (seq s t x l) 2 0 where
  adj k := by
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [seq_even, seq_odd]
      exact (GraphAction.adj_smul _ _ _).mpr hxl
    · rw [seq_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, seq_even, zpow_add_one, mul_smul]
      have h1 : (t * s) • x = t • x := by rw [mul_smul, hsx]
      rw [h1]
      exact (GraphAction.adj_smul _ _ _).mpr (adj_aux hxl htl)
  nb k := by
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [show 2 * j + 2 = 2 * (j + 1) by ring, seq_even, seq_even, zpow_add_one, mul_smul]
      have h1 : (t * s) • x = t • x := by rw [mul_smul, hsx]
      rw [h1]
      intro h
      exact htx (smul_left_cancel _ h).symm
    · rw [show 2 * j + 1 + 2 = 2 * (j + 1) + 1 by ring, seq_odd, seq_odd, zpow_add_one, mul_smul]
      have h1 : (t * s) • l ≠ l := by
        intro h
        apply hsl
        have h2 : t • (t * s) • l = t • l := congrArg (fun v => t • v) h
        rw [htl, ← mul_smul, ← mul_assoc, ht, one_mul] at h2
        exact h2
      intro h
      exact h1 (smul_left_cancel _ h).symm
  rot k := by
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [seq_even, rot_smul, show 2 * j + (2 : ℕ) = 2 * (j + 1) by push_cast; ring, seq_even]
    · rw [seq_odd, rot_smul, show 2 * j + 1 + (2 : ℕ) = 2 * (j + 1) + 1 by push_cast; ring,
        seq_odd]
  refl k := by
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [seq_even, zpow_smul_comm hs ht, hsx, show (0 : ℤ) - 2 * j = 2 * (-j) by ring, seq_even]
    · rw [seq_odd, zpow_smul_comm hs ht, show (0 : ℤ) - (2 * j + 1) = 2 * (-j - 1) + 1 by ring,
        seq_odd]
      have h1 : s • l = (t * s)⁻¹ • l := by
        rw [inv_rot_eq hs ht, mul_smul, htl]
      rw [h1, ← mul_smul, ← zpow_neg_one, ← zpow_add]
      congr 2

theorem rot_pow_smul_eq {n : ℕ} {y : V} (hs : s * s = 1) (ht : t * t = 1)
    (hy : (s * t) ^ n • y = y) : (t * s) ^ n • y = y := by
  rw [rot_pow_eq_inv hs ht, inv_smul_eq_iff]
  exact hy.symm

include hs ht hxl hsx htl hsl htx in
theorem lemma_F36 {c : V → Bool} (hΓ : Γ.Connected) (hc : ∀ a b, Γ.Adj a b → c a ≠ c b) {m : ℕ}
    (hm : 1 < m) (hU : UniqueGeod Γ m) {n : ℕ} (hn : 0 < n) (hnm : n ≤ m)
    (hx : (s * t) ^ n • x = x) (hl : (s * t) ^ n • l = l) :
    n = m ∧
      IsPolygon Γ (MulAction.orbit (Subgroup.closure {s, t}) x ∪
        MulAction.orbit (Subgroup.closure {s, t}) l) (2 * m) ∧
      (∀ w ∈ Subgroup.closure {s, t},
        (∀ v ∈ MulAction.orbit (Subgroup.closure {s, t}) x ∪
          MulAction.orbit (Subgroup.closure {s, t}) l, w • v = v) ↔
          w ∈ Subgroup.zpowers ((s * t) ^ m)) ∧
      (Subgroup.zpowers ((s * t) ^ m)).relIndex (Subgroup.closure {s, t}) = 2 * m := by
  have D := dihedralSeq hs ht hxl hsx htl hsl htx
  have hxr : (t * s) ^ n • x = x := rot_pow_smul_eq hs ht hx
  have hlr : (t * s) ^ n • l = l := rot_pow_smul_eq hs ht hl
  have hper : ∀ n : ℕ, (t * s) ^ n • x = x → (t * s) ^ n • l = l →
      ∀ k : ℤ, seq s t x l (k + ((2 * n : ℕ) : ℤ)) = seq s t x l k := by
    intro n hxr hlr k
    obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
    · rw [show 2 * j + ((2 * n : ℕ) : ℤ) = 2 * (j + n) by push_cast; ring, seq_even, seq_even,
        zpow_add, mul_smul, zpow_natCast, hxr]
    · rw [show 2 * j + 1 + ((2 * n : ℕ) : ℤ) = 2 * (j + n) + 1 by push_cast; ring, seq_odd,
        seq_odd, zpow_add, mul_smul, zpow_natCast, hlr]
  have hnm' : n = m := by
    have h2n := GPath.two_mul_le_of_periodic hΓ hc hU (fun i : ℕ => seq s t x l (i : ℤ))
      D.adj_nat D.nb_nat (M := 2 * n) (by omega) (DihedralSeq.per_nat (hper n hxr hlr))
    omega
  subst hnm'
  have hperm := hper n hxr hlr
  have hr : t * s ∈ Subgroup.closure {s, t} :=
    Subgroup.mul_mem _ (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
  have h0 : seq s t x l 0 = x := by simpa using seq_even s t x l 0
  have h1 : seq s t x l 1 = l := by simpa using seq_odd s t x l 0
  have hrange : Set.range (seq s t x l) = MulAction.orbit (Subgroup.closure {s, t}) x ∪
      MulAction.orbit (Subgroup.closure {s, t}) l := by
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      obtain ⟨j, rfl | rfl⟩ := Int.even_or_odd' k
      · left
        rw [seq_even]
        exact ⟨⟨(t * s) ^ j, Subgroup.zpow_mem _ hr j⟩, rfl⟩
      · right
        rw [seq_odd]
        exact ⟨⟨(t * s) ^ j, Subgroup.zpow_mem _ hr j⟩, rfl⟩
    · rintro (⟨⟨w, hw⟩, rfl⟩ | ⟨⟨w, hw⟩, rfl⟩)
      · obtain ⟨k', hk'⟩ := D.smul_mem_range hs ht hw 0
        rw [h0] at hk'
        exact ⟨k', hk'.symm⟩
      · obtain ⟨k', hk'⟩ := D.smul_mem_range hs ht hw 1
        rw [h1] at hk'
        exact ⟨k', hk'.symm⟩
  have hu := fun i j => D.u_eq_iff hΓ hc (by omega) hU hperm i j
  have hzp : Subgroup.zpowers ((s * t) ^ n) = Subgroup.zpowers ((t * s) ^ (n : ℤ)) := by
    have e : (s * t) ^ n = ((t * s) ^ n)⁻¹ := by
      rw [rot_pow_eq_inv hs ht, inv_inv]
    rw [e, Subgroup.zpowers_inv, zpow_natCast]
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [← hrange]
    exact D.isPolygon hΓ hc (by omega) hU hperm
  · intro w hw
    have key := D.fixes_iff_mem_zpowers hs ht (N := 2 * n) (n := n) (by norm_num)
      (by push_cast; ring) (by omega) hu hw
    rw [← hrange, Set.forall_mem_range, key, hzp]
  · rw [hzp]
    exact D.relIndex_eq hs ht (N := 2 * n) (n := n) hn (by norm_num) (by push_cast; ring)
      (by omega) hu

end Lemma36

end CFSG.Quasithin
