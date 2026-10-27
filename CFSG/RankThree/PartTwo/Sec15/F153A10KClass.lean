module

public import CFSG.RankThree.PartTwo.Sec15.F153A10KDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

open Equiv

private theorem cls_t0 : tZero 0 = 1 := by decide +kernel

private theorem cls_t1 : tZero 1 = 0 := by decide +kernel

private theorem cls_t2 : tZero 2 = 3 := by decide +kernel

private theorem cls_t3 : tZero 3 = 2 := by decide +kernel

private theorem cls_tZero_hi : ∀ w : Fin 10, 4 ≤ w.val → tZero w = w := by
  decide +kernel

private theorem cls_tZero_lo : ∀ w : Fin 10, w.val < 4 → tZero w ≠ w := by
  decide +kernel

private theorem cls_A_val : ∀ z : Fin 10, z.val < 4 → z = 0 ∨ z = 1 ∨ z = 2 ∨ z = 3 := by
  decide +kernel

private theorem cls_filter_A {g g' : Perm (Fin 10)}
    (h : ∀ z : Fin 10, z.val < 4 → g z = g' z) :
    (Finset.univ.filter (fun z => g z ≠ z)).filter (fun z => z.val < 4) =
      (Finset.univ.filter (fun z => g' z ≠ z)).filter (fun z => z.val < 4) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hz : z.val < 4
  · rw [h z hz]
  · exact ⟨fun h' => absurd h'.2 hz, fun h' => absurd h'.2 hz⟩

private theorem cls_filter_C {b : Perm (Fin 10)}
    (hCC : ∀ z : Fin 10, 4 ≤ z.val → 4 ≤ (b z).val) :
    (Finset.univ.filter (fun z => (tZero * b) z ≠ z)).filter (fun z => ¬ z.val < 4) =
      (Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4) := by
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hz : z.val < 4
  · exact ⟨fun h' => absurd hz h'.2, fun h' => absurd hz h'.2⟩
  · have hz4 : 4 ≤ z.val := by omega
    have h1 : (tZero * b) z = b z := by
      rw [Equiv.Perm.mul_apply, cls_tZero_hi (b z) (hCC z hz4)]
    rw [h1]

private theorem cls_counts {b f : Perm (Fin 10)} {m m' : ℕ}
    (hf : ∀ z : Fin 10, z.val < 4 → b z = f z)
    (hm : ((Finset.univ.filter (fun z => f z ≠ z)).filter (fun z => z.val < 4)).card = m)
    (hm' : ((Finset.univ.filter (fun z => (tZero * f) z ≠ z)).filter
      (fun z => z.val < 4)).card = m')
    (hb4 : (Finset.univ.filter (fun z => b z ≠ z)).card = 4)
    (hab4 : (Finset.univ.filter (fun z => (tZero * b) z ≠ z)).card = 4)
    (hCC : ∀ z : Fin 10, 4 ≤ z.val → 4 ≤ (b z).val) :
    m + ((Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4)).card = 4 ∧
      m' + ((Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4)).card = 4 := by
  have hS : ((Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => z.val < 4)).card +
      ((Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4)).card =
        (Finset.univ.filter (fun z => b z ≠ z)).card :=
    Finset.card_filter_add_card_filter_not (fun z : Fin 10 => z.val < 4)
  have hT : ((Finset.univ.filter (fun z => (tZero * b) z ≠ z)).filter (fun z => z.val < 4)).card +
      ((Finset.univ.filter (fun z => (tZero * b) z ≠ z)).filter (fun z => ¬ z.val < 4)).card =
        (Finset.univ.filter (fun z => (tZero * b) z ≠ z)).card :=
    Finset.card_filter_add_card_filter_not (fun z : Fin 10 => z.val < 4)
  have hA1 := congrArg Finset.card (cls_filter_A hf)
  have hA2 := congrArg Finset.card
    (cls_filter_A (g := tZero * b) (g' := tZero * f)
      (fun z hz => by rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hf z hz]))
  have hC := congrArg Finset.card (cls_filter_C hCC)
  rw [hb4] at hS
  rw [hab4] at hT
  rw [hm] at hA1
  rw [hm'] at hA2
  omega

private theorem cls_two {b f : Perm (Fin 10)} (hinv : ∀ z, b (b z) = z)
    (hCC : ∀ z : Fin 10, 4 ≤ z.val → 4 ≤ (b z).val)
    (hf : ∀ z : Fin 10, z.val < 4 → b z = f z)
    (hfC : ∀ z : Fin 10, 4 ≤ z.val → f z = z)
    (hk : ((Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4)).card = 2) :
    ∃ x y : Fin 10, 4 ≤ x.val ∧ 4 ≤ y.val ∧ x ≠ y ∧ b = f * swap x y := by
  obtain ⟨x, y, hxy, hD⟩ := Finset.card_eq_two.mp hk
  have hmem : ∀ z : Fin 10, 4 ≤ z.val → (b z ≠ z ↔ z = x ∨ z = y) := by
    intro z hz
    have h := Finset.ext_iff.mp hD z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at h
    exact ⟨fun hbz => h.mp ⟨hbz, by omega⟩, fun hzxy => (h.mpr hzxy).1⟩
  have hx4 : 4 ≤ x.val := by
    have h : x ∈ (Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4) := by
      rw [hD]
      exact Finset.mem_insert_self x {y}
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    have := h.2
    omega
  have hy4 : 4 ≤ y.val := by
    have h : y ∈ (Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4) := by
      rw [hD]
      exact Finset.mem_insert_of_mem (Finset.mem_singleton_self y)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h
    have := h.2
    omega
  have hxne : b x ≠ x := (hmem x hx4).mpr (Or.inl rfl)
  have hyne : b y ≠ y := (hmem y hy4).mpr (Or.inr rfl)
  have hbx : b x = y := by
    have h1 : b (b x) ≠ b x := by
      rw [hinv x]
      exact fun h => hxne h.symm
    rcases (hmem (b x) (hCC x hx4)).mp h1 with h | h
    · exact absurd h hxne
    · exact h
  have hby : b y = x := by
    have h1 : b (b y) ≠ b y := by
      rw [hinv y]
      exact fun h => hyne h.symm
    rcases (hmem (b y) (hCC y hy4)).mp h1 with h | h
    · exact h
    · exact absurd h hyne
  refine ⟨x, y, hx4, hy4, hxy, ?_⟩
  refine Equiv.ext fun z => ?_
  rw [Equiv.Perm.mul_apply]
  by_cases hz : z.val < 4
  · have hzx : z ≠ x := fun h => by
      rw [h] at hz
      omega
    have hzy : z ≠ y := fun h => by
      rw [h] at hz
      omega
    rw [Equiv.swap_apply_of_ne_of_ne hzx hzy, hf z hz]
  · have hz4 : 4 ≤ z.val := by omega
    by_cases hzx : z = x
    · rw [hzx, Equiv.swap_apply_left, hbx, hfC y hy4]
    by_cases hzy : z = y
    · rw [hzy, Equiv.swap_apply_right, hby, hfC x hx4]
    have hbz : b z = z := by
      by_contra h
      rcases (hmem z hz4).mp h with h' | h'
      · exact hzx h'
      · exact hzy h'
    rw [Equiv.swap_apply_of_ne_of_ne hzx hzy, hbz, hfC z hz4]

private theorem cls_zero {b f : Perm (Fin 10)}
    (hf : ∀ z : Fin 10, z.val < 4 → b z = f z)
    (hfC : ∀ z : Fin 10, 4 ≤ z.val → f z = z)
    (hk : ((Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4)).card = 0) :
    b = f := by
  refine Equiv.ext fun z => ?_
  by_cases hz : z.val < 4
  · exact hf z hz
  · have hz4 : 4 ≤ z.val := by omega
    have hbz : b z = z := by
      by_contra h
      have hmem : z ∈ (Finset.univ.filter (fun z => b z ≠ z)).filter (fun z => ¬ z.val < 4) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨h, hz⟩
      rw [Finset.card_eq_zero.mp hk] at hmem
      simp at hmem
    rw [hbz, hfC z hz4]

theorem classify_comm_tZero {b : Perm (Fin 10)} (hb2 : b ^ 2 = 1) (hbc : b * tZero = tZero * b)
    (hb4 : b.support.card = 4) (hab4 : (tZero * b).support.card = 4) (hne : b ≠ tZero) :
    b = taA ∨ b = swap 0 3 * swap 1 2 ∨
      ∃ x y : Fin 10, 4 ≤ x.val ∧ 4 ≤ y.val ∧ x ≠ y ∧
        (b = swap 0 1 * swap x y ∨ b = swap 2 3 * swap x y) := by
  have hcomm : ∀ z, b (tZero z) = tZero (b z) := fun z => by
    simpa [Equiv.Perm.mul_apply] using DFunLike.congr_fun hbc z
  have hb2' : b * b = 1 := by
    rw [← pow_two]
    exact hb2
  have hinv : ∀ z, b (b z) = z := fun z => by
    simpa [Equiv.Perm.mul_apply] using DFunLike.congr_fun hb2' z
  have hSup : ∀ g : Perm (Fin 10), g.support = Finset.univ.filter (fun z => g z ≠ z) := by
    intro g
    ext z
    simp [Equiv.Perm.mem_support]
  rw [hSup b] at hb4
  rw [hSup (tZero * b)] at hab4
  have hAA : ∀ z : Fin 10, z.val < 4 → (b z).val < 4 := by
    intro z hz
    by_contra hbz
    have h1 : tZero (b z) = b z := cls_tZero_hi (b z) (by omega)
    have h2 : b (tZero z) = b z := by rw [hcomm, h1]
    exact cls_tZero_lo z hz (b.injective h2)
  have hCC : ∀ z : Fin 10, 4 ≤ z.val → 4 ≤ (b z).val := by
    intro z hz
    by_contra hbz
    have h := hAA (b z) (by omega)
    rw [hinv z] at h
    omega
  have hb1 : b 1 = tZero (b 0) := by
    have h := hcomm 0
    rwa [cls_t0] at h
  have hb3 : b 3 = tZero (b 2) := by
    have h := hcomm 2
    rwa [cls_t2] at h
  have hkey : (b 0 = 0 ∧ b 2 = 2) ∨ (b 0 = 0 ∧ b 2 = 3) ∨ (b 0 = 1 ∧ b 2 = 2) ∨
      (b 0 = 1 ∧ b 2 = 3) ∨ (b 0 = 2 ∧ b 2 = 0) ∨ (b 0 = 3 ∧ b 2 = 1) := by
    have hA0 := cls_A_val (b 0) (hAA 0 (by decide))
    have hA2 := cls_A_val (b 2) (hAA 2 (by decide))
    have e0 := hinv 0
    have e2 := hinv 2
    rcases hA0 with h0 | h0 | h0 | h0 <;> rcases hA2 with h2 | h2 | h2 | h2 <;>
      simp [h0, h2, hb1, hb3, cls_t0, cls_t1, cls_t2, cls_t3] at e0 e2 ⊢
  rcases hkey with ⟨h0, h2⟩ | ⟨h0, h2⟩ | ⟨h0, h2⟩ | ⟨h0, h2⟩ | ⟨h0, h2⟩ | ⟨h0, h2⟩
  ·
    have hf : ∀ z : Fin 10, z.val < 4 → b z = (1 : Perm (Fin 10)) z := by
      intro z hz
      rcases cls_A_val z hz with rfl | rfl | rfl | rfl <;>
        simp only [hb1, hb3, h0, h2, cls_t0, cls_t1, cls_t2, cls_t3] <;> decide +kernel
    obtain ⟨c1, c2⟩ := cls_counts (m := 0) (m' := 4) hf (by decide +kernel)
      (by decide +kernel) hb4 hab4 hCC
    exfalso
    omega
  ·
    have hf : ∀ z : Fin 10, z.val < 4 → b z = swap 2 3 z := by
      intro z hz
      rcases cls_A_val z hz with rfl | rfl | rfl | rfl <;>
        simp only [hb1, hb3, h0, h2, cls_t0, cls_t1, cls_t2, cls_t3] <;> decide +kernel
    have hfC : ∀ z : Fin 10, 4 ≤ z.val → swap 2 3 z = z := by decide +kernel
    obtain ⟨c1, c2⟩ := cls_counts (m := 2) (m' := 2) hf (by decide +kernel)
      (by decide +kernel) hb4 hab4 hCC
    obtain ⟨x, y, hx, hy, hxy, hb⟩ := cls_two hinv hCC hf hfC (by omega)
    exact Or.inr (Or.inr ⟨x, y, hx, hy, hxy, Or.inr hb⟩)
  ·
    have hf : ∀ z : Fin 10, z.val < 4 → b z = swap 0 1 z := by
      intro z hz
      rcases cls_A_val z hz with rfl | rfl | rfl | rfl <;>
        simp only [hb1, hb3, h0, h2, cls_t0, cls_t1, cls_t2, cls_t3] <;> decide +kernel
    have hfC : ∀ z : Fin 10, 4 ≤ z.val → swap 0 1 z = z := by decide +kernel
    obtain ⟨c1, c2⟩ := cls_counts (m := 2) (m' := 2) hf (by decide +kernel)
      (by decide +kernel) hb4 hab4 hCC
    obtain ⟨x, y, hx, hy, hxy, hb⟩ := cls_two hinv hCC hf hfC (by omega)
    exact Or.inr (Or.inr ⟨x, y, hx, hy, hxy, Or.inl hb⟩)
  ·
    have hf : ∀ z : Fin 10, z.val < 4 → b z = tZero z := by
      intro z hz
      rcases cls_A_val z hz with rfl | rfl | rfl | rfl <;>
        simp only [hb1, hb3, h0, h2, cls_t0, cls_t1, cls_t2, cls_t3] <;> decide +kernel
    obtain ⟨c1, c2⟩ := cls_counts (m := 4) (m' := 0) hf (by decide +kernel)
      (by decide +kernel) hb4 hab4 hCC
    exact absurd (cls_zero hf cls_tZero_hi (by omega)) hne
  ·
    have hf : ∀ z : Fin 10, z.val < 4 → b z = taA z := by
      intro z hz
      rcases cls_A_val z hz with rfl | rfl | rfl | rfl <;>
        simp only [hb1, hb3, h0, h2, cls_t0, cls_t1, cls_t2, cls_t3] <;> decide +kernel
    have hfC : ∀ z : Fin 10, 4 ≤ z.val → taA z = z := by decide +kernel
    obtain ⟨c1, c2⟩ := cls_counts (m := 4) (m' := 4) hf (by decide +kernel)
      (by decide +kernel) hb4 hab4 hCC
    exact Or.inl (cls_zero hf hfC (by omega))
  ·
    have hf : ∀ z : Fin 10, z.val < 4 → b z = (swap 0 3 * swap 1 2 : Perm (Fin 10)) z := by
      intro z hz
      rcases cls_A_val z hz with rfl | rfl | rfl | rfl <;>
        simp only [hb1, hb3, h0, h2, cls_t0, cls_t1, cls_t2, cls_t3] <;> decide +kernel
    have hfC : ∀ z : Fin 10, 4 ≤ z.val → (swap 0 3 * swap 1 2 : Perm (Fin 10)) z = z := by
      decide +kernel
    obtain ⟨c1, c2⟩ := cls_counts (m := 4) (m' := 4) hf (by decide +kernel)
      (by decide +kernel) hb4 hab4 hCC
    exact Or.inr (Or.inl (cls_zero hf hfC (by omega)))

end CFSG.RankThree.PartTwo.Sec15.F153A10K
