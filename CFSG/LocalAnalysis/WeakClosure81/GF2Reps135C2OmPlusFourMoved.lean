module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQPlusSigned

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.StandardType

private def w183_z0 : Fin 4 := 0
private def w183_z1 : Fin 4 := 1
private def w183_z2 : Fin 4 := 2
private def w183_z3 : Fin 4 := 3

private def w183_sgnOf (k : ℕ) : ℤ := if k % 2 = 0 then 1 else -1

private def w183_sgn2Of (k : ℕ) : ℤ := if (k / 2) % 2 = 0 then 1 else -1

private lemma w183_sgnOf_eq (k : ℕ) : w183_sgnOf k = 1 ∨ w183_sgnOf k = -1 := by
  unfold w183_sgnOf
  split_ifs <;> simp

private lemma w183_sgn2Of_eq (k : ℕ) : w183_sgn2Of k = 1 ∨ w183_sgn2Of k = -1 := by
  unfold w183_sgn2Of
  split_ifs <;> simp

private def w183_c2 (i : Fin 7) : Fin 4 := ⟨2 + i.val / 4, by omega⟩

private def w183_c1 (i : Fin 6) : Fin 4 := ⟨1 + i.val / 2, by omega⟩

private lemma w183_z0_ne_c2 (i : Fin 7) : w183_z0 ≠ w183_c2 i := by
  fin_cases i <;> decide

private lemma w183_c2_ne_z0 (i : Fin 7) : w183_c2 i ≠ w183_z0 :=
  (w183_z0_ne_c2 i).symm

private lemma w183_z1_ne_c2 (i : Fin 7) : w183_z1 ≠ w183_c2 i := by
  fin_cases i <;> decide

private lemma w183_z0_ne_c1 (i : Fin 6) : w183_z0 ≠ w183_c1 i := by
  fin_cases i <;> decide

private lemma w183_c1_ne_z0 (i : Fin 6) : w183_c1 i ≠ w183_z0 :=
  (w183_z0_ne_c1 i).symm

private lemma w183_one_ne_zero {m : ℕ} (hm3 : 3 ≤ m) : (1 : ZMod m) ≠ 0 := by
  intro h
  exact absurd (ZMod.one_eq_zero_iff.mp h) (by omega)

private lemma w183_one_ne_neg_one {m : ℕ} (hm3 : 3 ≤ m) : (1 : ZMod m) ≠ -1 := by
  intro h
  rcases ZMod.neg_one_eq_one_iff.mp h.symm with h' | h' <;> omega

private lemma w183_neg_one_ne_zero {m : ℕ} (hm3 : 3 ≤ m) : (-1 : ZMod m) ≠ 0 :=
  neg_ne_zero.mpr (w183_one_ne_zero hm3)

private lemma w183_pm_cast_ne_zero {m : ℕ} (hm3 : 3 ≤ m) {z : ℤ}
    (hz : z = 1 ∨ z = -1) : (z : ZMod m) ≠ 0 := by
  rcases hz with h | h <;> rw [h]
  · simpa using w183_one_ne_zero hm3
  · simpa using w183_neg_one_ne_zero hm3

private lemma w183_intCast_mul_self {m : ℕ} {δ : ℤ} (hδ : δ = 1 ∨ δ = -1) :
    (δ : ZMod m) * (δ : ZMod m) = 1 := by
  rcases hδ with h | h <;> rw [h] <;> push_cast <;> ring

private lemma w183_cast_mul {m : ℕ} {σ δ : ℤ} (hδ : δ = 1 ∨ δ = -1) :
    ((σ * δ : ℤ) : ZMod m) * (δ : ZMod m) = (σ : ZMod m) := by
  rw [Int.cast_mul]
  calc (σ : ZMod m) * (δ : ZMod m) * (δ : ZMod m)
      = (σ : ZMod m) * ((δ : ZMod m) * (δ : ZMod m)) := by ring
    _ = (σ : ZMod m) * 1 := by rw [w183_intCast_mul_self hδ]
    _ = (σ : ZMod m) := by ring

private lemma w183_mul_pm {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

private lemma w183_mul_val {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = 0) :
    a * b = 1 ∨ a * b = -1 ∨ a * b = 0 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> norm_num

private lemma w183_pm01_of {a : ℤ} (h : a = 1 ∨ a = -1) :
    a = 1 ∨ a = -1 ∨ a = 0 := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

private lemma w183_intCast_eq {m : ℕ} (hm3 : 3 ≤ m) {p q : ℤ}
    (hp : p = 1 ∨ p = -1 ∨ p = 0) (hq : q = 1 ∨ q = -1 ∨ q = 0)
    (h : (p : ZMod m) = (q : ZMod m)) : p = q := by
  have h1 : ((1 : ℤ) : ZMod m) ≠ 0 := by simpa using w183_one_ne_zero hm3
  have h2 : ((1 : ℤ) : ZMod m) ≠ ((-1 : ℤ) : ZMod m) := by
    simpa using w183_one_ne_neg_one hm3
  have h3 : ((-1 : ℤ) : ZMod m) ≠ 0 := by simpa using w183_neg_one_ne_zero hm3
  rcases hp with hp | hp | hp <;> rcases hq with hq | hq | hq <;>
    rw [hp, hq] at h ⊢
  all_goals first
    | rfl
    | exact absurd h (by simpa using h1)
    | exact absurd h (by simpa using h2)
    | exact absurd h (by simpa using h3)
    | exact absurd h.symm (by simpa using h1)
    | exact absurd h.symm (by simpa using h2)
    | exact absurd h.symm (by simpa using h3)

private def w183_rho12 : Fin 4 → ℤ := Pi.single w183_z1 1 + Pi.single w183_z2 1

private def w183_rho13 : Fin 4 → ℤ := Pi.single w183_z1 1 + Pi.single w183_z3 1

private def w183_rho23 : Fin 4 → ℤ := Pi.single w183_z2 1 + Pi.single w183_z3 1

private def w183_V {m : ℕ} (v : Fin 4 → ℤ) : Fin 4 → ZMod m := fun b => (v b : ZMod m)

private lemma w183_rho12_z0 : w183_rho12 w183_z0 = 0 := by decide

private lemma w183_rho13_z0 : w183_rho13 w183_z0 = 0 := by decide

private lemma w183_rho23_z0 : w183_rho23 w183_z0 = 0 := by decide

private lemma w183_rho12_z1 : w183_rho12 w183_z1 = 1 := by decide

private lemma w183_rho13_z1 : w183_rho13 w183_z1 = 1 := by decide

private lemma w183_rho12_z2 : w183_rho12 w183_z2 = 1 := by decide

private lemma w183_rho23_z2 : w183_rho23 w183_z2 = 1 := by decide

private lemma w183_rho13_z3 : w183_rho13 w183_z3 = 1 := by decide

private lemma w183_rho23_z3 : w183_rho23 w183_z3 = 1 := by decide

private lemma w183_rho12_val (b : Fin 4) : w183_rho12 b = 1 ∨ w183_rho12 b = 0 := by
  fin_cases b <;> decide

private lemma w183_rho13_val (b : Fin 4) : w183_rho13 b = 1 ∨ w183_rho13 b = 0 := by
  fin_cases b <;> decide

private lemma w183_rho23_val (b : Fin 4) : w183_rho23 b = 1 ∨ w183_rho23 b = 0 := by
  fin_cases b <;> decide

private lemma w183_rho12_eq_one_iff (b : Fin 4) :
    w183_rho12 b = 1 ↔ b = w183_z1 ∨ b = w183_z2 := by
  fin_cases b <;> decide

private lemma w183_rho13_eq_one_iff (b : Fin 4) :
    w183_rho13 b = 1 ↔ b = w183_z1 ∨ b = w183_z3 := by
  fin_cases b <;> decide

private lemma w183_rho23_eq_one_iff (b : Fin 4) :
    w183_rho23 b = 1 ↔ b = w183_z2 ∨ b = w183_z3 := by
  fin_cases b <;> decide

private lemma w183_V_rho12 {m : ℕ} :
    w183_V (m := m) w183_rho12 =
      Pi.single w183_z1 (1 : ZMod m) + Pi.single w183_z2 (1 : ZMod m) := by
  funext b
  fin_cases b <;>
    simp [w183_V, w183_rho12, Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_one,
      w183_z0, w183_z1, w183_z2, w183_z3]

private lemma w183_V_rho13 {m : ℕ} :
    w183_V (m := m) w183_rho13 =
      Pi.single w183_z1 (1 : ZMod m) + Pi.single w183_z3 (1 : ZMod m) := by
  funext b
  fin_cases b <;>
    simp [w183_V, w183_rho13, Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_one,
      w183_z0, w183_z1, w183_z2, w183_z3]

private lemma w183_V_rho23 {m : ℕ} :
    w183_V (m := m) w183_rho23 =
      Pi.single w183_z2 (1 : ZMod m) + Pi.single w183_z3 (1 : ZMod m) := by
  funext b
  fin_cases b <;>
    simp [w183_V, w183_rho23, Pi.add_apply, Pi.single_apply, Int.cast_add, Int.cast_one,
      w183_z0, w183_z1, w183_z2, w183_z3]

private lemma w183_mul_eq_one {a b : ℤ} (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = 0)
    (h : a * b = 1) : a = 1 ∧ b = 1 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

private lemma w183_eq_z1_of {a : Fin 4} (h1 : a = w183_z1 ∨ a = w183_z2)
    (h2 : a = w183_z1 ∨ a = w183_z3) : a = w183_z1 := by
  rcases h1 with h | h <;> rcases h2 with h' | h'
  · exact h
  · exact h
  · exact h'
  · exact absurd (h.symm.trans h') (by decide)

private lemma w183_eq_z2_of {a : Fin 4} (h1 : a = w183_z1 ∨ a = w183_z2)
    (h2 : a = w183_z2 ∨ a = w183_z3) : a = w183_z2 := by
  rcases h1 with h | h <;> rcases h2 with h' | h'
  · exact h'
  · exact absurd (h.symm.trans h') (by decide)
  · exact h
  · exact h

private lemma w183_eq_z3_of {a : Fin 4} (h1 : a = w183_z1 ∨ a = w183_z3)
    (h2 : a = w183_z2 ∨ a = w183_z3) : a = w183_z3 := by
  rcases h1 with h | h <;> rcases h2 with h' | h'
  · exact absurd (h.symm.trans h') (by decide)
  · exact h'
  · exact h
  · exact h

private lemma w183_fixed_coord {m : ℕ} (hm3 : 3 ≤ m) {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hs : SpIsSign s) {v : Fin 4 → ℤ} (hv : ∀ b, v b = 1 ∨ v b = 0)
    (hfix : omqSignedAct π s (w183_V (m := m) v) = w183_V (m := m) v) (b : Fin 4) :
    s (π.symm b) * v (π.symm b) = v b := by
  have h := congrFun hfix b
  simp only [omqSignedAct, w183_V] at h
  rw [← Int.cast_mul] at h
  rcases hv b with hb | hb
  · exact w183_intCast_eq hm3 (w183_mul_val (hs _) (hv _)) (Or.inl hb) h
  · exact w183_intCast_eq hm3 (w183_mul_val (hs _) (hv _)) (Or.inr (Or.inr hb)) h

private lemma w183_negating_three {m : ℕ} (hm3 : 3 ≤ m)
    {π : Equiv.Perm (Fin 4)} {s : Fin 4 → ℤ} (hs0 : s w183_z0 = -1) (hs : SpIsSign s)
    (hprod : ∏ c, s c = 1) :
    omqSignedAct π s (w183_V (m := m) w183_rho12) ≠ w183_V (m := m) w183_rho12 ∨
    omqSignedAct π s (w183_V (m := m) w183_rho13) ≠ w183_V (m := m) w183_rho13 ∨
    omqSignedAct π s (w183_V (m := m) w183_rho23) ≠ w183_V (m := m) w183_rho23 := by
  by_contra h
  simp only [not_or] at h
  have h12 : omqSignedAct π s (w183_V w183_rho12) = w183_V w183_rho12 := not_not.mp h.1
  have h13 : omqSignedAct π s (w183_V w183_rho13) = w183_V w183_rho13 := not_not.mp h.2.1
  have h23 : omqSignedAct π s (w183_V w183_rho23) = w183_V w183_rho23 := not_not.mp h.2.2
  have e12z1 := w183_fixed_coord hm3 hs w183_rho12_val h12 w183_z1
  have e13z1 := w183_fixed_coord hm3 hs w183_rho13_val h13 w183_z1
  rw [w183_rho12_z1] at e12z1
  rw [w183_rho13_z1] at e13z1
  obtain ⟨hs_a1, hr12a1⟩ := w183_mul_eq_one (hs _) (w183_rho12_val _) e12z1
  obtain ⟨hs_b1, hr13b1⟩ := w183_mul_eq_one (hs _) (w183_rho13_val _) e13z1
  have hz1 : π.symm w183_z1 = w183_z1 :=
    w183_eq_z1_of ((w183_rho12_eq_one_iff _).mp hr12a1)
      ((w183_rho13_eq_one_iff _).mp hr13b1)
  have hs_z1 : s w183_z1 = 1 := by rw [← hz1]; exact hs_a1
  have e12z2 := w183_fixed_coord hm3 hs w183_rho12_val h12 w183_z2
  have e23z2 := w183_fixed_coord hm3 hs w183_rho23_val h23 w183_z2
  rw [w183_rho12_z2] at e12z2
  rw [w183_rho23_z2] at e23z2
  obtain ⟨hs_a2, hr12a2⟩ := w183_mul_eq_one (hs _) (w183_rho12_val _) e12z2
  obtain ⟨hs_c2, hr23c2⟩ := w183_mul_eq_one (hs _) (w183_rho23_val _) e23z2
  have hz2 : π.symm w183_z2 = w183_z2 :=
    w183_eq_z2_of ((w183_rho12_eq_one_iff _).mp hr12a2)
      ((w183_rho23_eq_one_iff _).mp hr23c2)
  have hs_z2 : s w183_z2 = 1 := by rw [← hz2]; exact hs_a2
  have e13z3 := w183_fixed_coord hm3 hs w183_rho13_val h13 w183_z3
  have e23z3 := w183_fixed_coord hm3 hs w183_rho23_val h23 w183_z3
  rw [w183_rho13_z3] at e13z3
  rw [w183_rho23_z3] at e23z3
  obtain ⟨hs_b3, hr13b3⟩ := w183_mul_eq_one (hs _) (w183_rho13_val _) e13z3
  obtain ⟨hs_c3, hr23c3⟩ := w183_mul_eq_one (hs _) (w183_rho23_val _) e23z3
  have hz3 : π.symm w183_z3 = w183_z3 :=
    w183_eq_z3_of ((w183_rho13_eq_one_iff _).mp hr13b3)
      ((w183_rho23_eq_one_iff _).mp hr23c3)
  have hs_z3 : s w183_z3 = 1 := by rw [← hz3]; exact hs_b3
  rw [Fin.prod_univ_four] at hprod
  have h0 : s (0 : Fin 4) = -1 := by simpa [w183_z0] using hs0
  have h1 : s (1 : Fin 4) = 1 := by simpa [w183_z1] using hs_z1
  have h2 : s (2 : Fin 4) = 1 := by simpa [w183_z2] using hs_z2
  have h3 : s (3 : Fin 4) = 1 := by simpa [w183_z3] using hs_z3
  rw [h0, h1, h2, h3] at hprod
  norm_num at hprod

theorem omq_exists_seven_orbit_roots_four {m : ℕ} (hm3 : 3 ≤ m)
    {a b : Fin 4} (hab : a ≠ b) {δ δ' : ℤ} (hδ : δ = 1 ∨ δ = -1) (hδ' : δ' = 1 ∨ δ' = -1)
    {π : Equiv.Perm (Fin 4)} {s : Fin 4 → ℤ} (hs : SpIsSign s) (hprod : ∏ c, s c = 1)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ u : Fin 7 → Fin 4 → ZMod m, Function.Injective u ∧
      (∀ i, ∃ (π' : Equiv.Perm (Fin 4)) (s' : Fin 4 → ℤ), SpIsSign s' ∧ ∏ c, s' c = 1 ∧
        omqSignedAct π' s' (Pi.single a (δ : ZMod m) + Pi.single b (δ' : ZMod m)) = u i) ∧
      ∀ i l, u i ≠ omqSignedAct π s (u l) := by
  classical
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ01, hπ10, hs01⟩
  ·
    have hπ0' : π w183_z0 = w183_z0 := by simpa [w183_z0] using hπ0
    have hs0' : s w183_z0 = -1 := by simpa [w183_z0] using hs0
    have hsymm0 : π.symm w183_z0 = w183_z0 := by
      rw [Equiv.symm_apply_eq]
      exact hπ0'.symm
    have hnotall := w183_negating_three (m := m) (π := π) hm3 hs0' hs hprod
    have hex : ∃ v : Fin 4 → ℤ, (v = w183_rho12 ∨ v = w183_rho13 ∨ v = w183_rho23) ∧
        omqSignedAct π s (w183_V (m := m) v) ≠ w183_V (m := m) v := by
      rcases hnotall with hA | hB | hC
      · exact ⟨w183_rho12, Or.inl rfl, hA⟩
      · exact ⟨w183_rho13, Or.inr (Or.inl rfl), hB⟩
      · exact ⟨w183_rho23, Or.inr (Or.inr rfl), hC⟩
    let r : Fin 4 → ℤ := Classical.choose hex
    have hr : omqSignedAct π s (w183_V (m := m) r) ≠ w183_V (m := m) r :=
      (Classical.choose_spec hex).2
    have hrmem : r = w183_rho12 ∨ r = w183_rho13 ∨ r = w183_rho23 :=
      (Classical.choose_spec hex).1
    have hr0 : r w183_z0 = 0 := by
      rcases hrmem with h | h | h <;> rw [h]
      · exact w183_rho12_z0
      · exact w183_rho13_z0
      · exact w183_rho23_z0
    let u6 : Fin 6 → Fin 4 → ZMod m := fun i =>
      Pi.single w183_z0 (1 : ZMod m) +
        Pi.single (w183_c1 i) ((w183_sgnOf i.val : ℤ) : ZMod m)
    let u : Fin 7 → Fin 4 → ZMod m := Fin.snoc u6 (w183_V (m := m) r)
    have hu_last : u (Fin.last 6) = w183_V (m := m) r := by
      show (Fin.snoc u6 (w183_V (m := m) r) : Fin 7 → Fin 4 → ZMod m) (Fin.last 6) =
        w183_V (m := m) r
      rw [Fin.snoc_last]
    have hu_cast : ∀ i : Fin 6, u (Fin.castSucc i) = u6 i := by
      intro i
      show (Fin.snoc u6 (w183_V (m := m) r) : Fin 7 → Fin 4 → ZMod m) (Fin.castSucc i) =
        u6 i
      rw [Fin.snoc_castSucc]
    have hu6_apply : ∀ (i : Fin 6) (b : Fin 4),
        u6 i b = (if b = w183_z0 then (1 : ZMod m) else 0) +
          (if b = w183_c1 i then ((w183_sgnOf i.val : ℤ) : ZMod m) else 0) := by
      intro i b
      simp [u6, Pi.add_apply, Pi.single_apply]
    have hu6_z0 : ∀ i : Fin 6, u6 i w183_z0 = 1 := by
      intro i
      rw [hu6_apply i w183_z0]
      simp [w183_z0_ne_c1 i]
    have hkey6 : Function.Injective
        (fun i : Fin 6 => (w183_c1 i, w183_sgnOf i.val)) := by decide
    have hu6_inj : Function.Injective u6 := by
      intro i j h
      have hc1 : w183_c1 i = w183_c1 j := by
        by_contra hne
        have hc := congrFun h (w183_c1 i)
        rw [hu6_apply i (w183_c1 i), hu6_apply j (w183_c1 i)] at hc
        simp [w183_c1_ne_z0 i, hne] at hc
        exact w183_pm_cast_ne_zero hm3 (w183_sgnOf_eq i.val) hc
      have hsgn : w183_sgnOf i.val = w183_sgnOf j.val := by
        have hc := congrFun h (w183_c1 i)
        rw [hu6_apply i (w183_c1 i), hu6_apply j (w183_c1 i)] at hc
        rw [hc1] at hc
        simp [w183_c1_ne_z0 i] at hc
        exact w183_intCast_eq hm3 (w183_pm01_of (w183_sgnOf_eq _))
          (w183_pm01_of (w183_sgnOf_eq _)) hc
      exact hkey6 (by simp [hc1, hsgn])
    have hu_inj : Function.Injective u := by
      intro i j h
      induction i using Fin.lastCases with
      | last =>
        induction j using Fin.lastCases with
        | last => rfl
        | cast j =>
          exfalso
          have hc := congrFun h w183_z0
          rw [hu_last, hu_cast j] at hc
          rw [show w183_V (m := m) r w183_z0 = 0 from by simp [w183_V, hr0]] at hc
          rw [hu6_z0 j] at hc
          exact w183_one_ne_zero hm3 hc.symm
      | cast i =>
        induction j using Fin.lastCases with
        | last =>
          exfalso
          have hc := congrFun h w183_z0
          rw [hu_last, hu_cast i] at hc
          rw [show w183_V (m := m) r w183_z0 = 0 from by simp [w183_V, hr0]] at hc
          rw [hu6_z0 i] at hc
          exact w183_one_ne_zero hm3 hc
        | cast j =>
          exact congrArg Fin.castSucc
            (hu6_inj (by rw [← hu_cast i, ← hu_cast j]; exact h))
    have hX6 : ∀ l : Fin 6, omqSignedAct π s (u6 l) w183_z0 = -1 := by
      intro l
      unfold omqSignedAct
      rw [hsymm0, hs0', hu6_z0 l]
      simp
    have hvr0 : w183_V (m := m) r w183_z0 = 0 := by simp [w183_V, hr0]
    have hXr : omqSignedAct π s (w183_V (m := m) r) w183_z0 = 0 := by
      unfold omqSignedAct
      rw [hsymm0, hvr0]
      simp
    refine ⟨u, hu_inj, ?_, ?_⟩
    · intro i
      induction i using Fin.lastCases with
      | last =>
        rw [hu_last]
        rcases hrmem with h | h | h
        · rw [h]
          obtain ⟨π', s', hs', hprod', hact⟩ :=
            omq_exists_signed_perm_two_coord (n := 4) (m := m) (by norm_num)
              (a := a) (b := b) (a' := w183_z1) (b' := w183_z2) hab (by decide)
              (e := δ) (he := hδ) (e' := δ') (he' := hδ')
              ((δ : ℤ) : ZMod m) ((δ' : ℤ) : ZMod m)
          refine ⟨π', s', hs', hprod', ?_⟩
          rw [hact, w183_intCast_mul_self hδ, w183_intCast_mul_self hδ', w183_V_rho12]
        · rw [h]
          obtain ⟨π', s', hs', hprod', hact⟩ :=
            omq_exists_signed_perm_two_coord (n := 4) (m := m) (by norm_num)
              (a := a) (b := b) (a' := w183_z1) (b' := w183_z3) hab (by decide)
              (e := δ) (he := hδ) (e' := δ') (he' := hδ')
              ((δ : ℤ) : ZMod m) ((δ' : ℤ) : ZMod m)
          refine ⟨π', s', hs', hprod', ?_⟩
          rw [hact, w183_intCast_mul_self hδ, w183_intCast_mul_self hδ', w183_V_rho13]
        · rw [h]
          obtain ⟨π', s', hs', hprod', hact⟩ :=
            omq_exists_signed_perm_two_coord (n := 4) (m := m) (by norm_num)
              (a := a) (b := b) (a' := w183_z2) (b' := w183_z3) hab (by decide)
              (e := δ) (he := hδ) (e' := δ') (he' := hδ')
              ((δ : ℤ) : ZMod m) ((δ' : ℤ) : ZMod m)
          refine ⟨π', s', hs', hprod', ?_⟩
          rw [hact, w183_intCast_mul_self hδ, w183_intCast_mul_self hδ', w183_V_rho23]
      | cast i =>
        rw [hu_cast i]
        obtain ⟨π', s', hs', hprod', hact⟩ :=
          omq_exists_signed_perm_two_coord (n := 4) (m := m) (by norm_num)
            (a := a) (b := b) (a' := w183_z0) (b' := w183_c1 i) hab (w183_z0_ne_c1 i)
            (e := δ) (he := hδ) (e' := w183_sgnOf i.val * δ')
            (he' := w183_mul_pm (w183_sgnOf_eq i.val) hδ')
            ((δ : ℤ) : ZMod m) ((δ' : ℤ) : ZMod m)
        refine ⟨π', s', hs', hprod', ?_⟩
        rw [hact, w183_intCast_mul_self hδ, w183_cast_mul (σ := w183_sgnOf i.val) hδ']
    · intro i l
      induction i using Fin.lastCases with
      | last =>
        induction l using Fin.lastCases with
        | last =>
          rw [hu_last]
          exact fun hh => hr hh.symm
        | cast l =>
          rw [hu_last, hu_cast l]
          intro hh
          have hc := congrFun hh w183_z0
          rw [hvr0, hX6 l] at hc
          exact w183_neg_one_ne_zero hm3 hc.symm
      | cast i =>
        induction l using Fin.lastCases with
        | last =>
          rw [hu_cast i, hu_last]
          intro hh
          have hc := congrFun hh w183_z0
          rw [hu6_z0 i, hXr] at hc
          exact w183_one_ne_zero hm3 hc
        | cast l =>
          rw [hu_cast i, hu_cast l]
          intro hh
          have hc := congrFun hh w183_z0
          rw [hu6_z0 i, hX6 l] at hc
          exact w183_one_ne_neg_one hm3 hc
  ·
    have hπ10' : π w183_z1 = w183_z0 := by simpa [w183_z0, w183_z1] using hπ10
    let u : Fin 7 → Fin 4 → ZMod m := fun i =>
      Pi.single w183_z0 ((w183_sgnOf i.val : ℤ) : ZMod m) +
        Pi.single (w183_c2 i) ((w183_sgn2Of i.val : ℤ) : ZMod m)
    have hu_apply : ∀ (i : Fin 7) (b : Fin 4),
        u i b = (if b = w183_z0 then ((w183_sgnOf i.val : ℤ) : ZMod m) else 0) +
          (if b = w183_c2 i then ((w183_sgn2Of i.val : ℤ) : ZMod m) else 0) := by
      intro i b
      simp [u, Pi.add_apply, Pi.single_apply]
    have hkey : Function.Injective
        (fun i : Fin 7 => (w183_c2 i, w183_sgnOf i.val, w183_sgn2Of i.val)) := by decide
    have hsymm : π.symm w183_z0 = w183_z1 := by
      rw [Equiv.symm_apply_eq]
      exact hπ10'.symm
    refine ⟨u, ?_, ?_, ?_⟩
    · intro i j h
      have hz0 : (w183_sgnOf i.val : ZMod m) = (w183_sgnOf j.val : ZMod m) := by
        have hc := congrFun h w183_z0
        rw [hu_apply i w183_z0, hu_apply j w183_z0] at hc
        simpa [w183_z0_ne_c2 i, w183_z0_ne_c2 j] using hc
      have hsgn : w183_sgnOf i.val = w183_sgnOf j.val :=
        w183_intCast_eq hm3 (w183_pm01_of (w183_sgnOf_eq _))
          (w183_pm01_of (w183_sgnOf_eq _)) hz0
      have hc2 : w183_c2 i = w183_c2 j := by
        by_contra hne
        have hc := congrFun h (w183_c2 i)
        rw [hu_apply i (w183_c2 i), hu_apply j (w183_c2 i)] at hc
        simp [w183_c2_ne_z0 i, hne] at hc
        exact w183_pm_cast_ne_zero hm3 (w183_sgn2Of_eq i.val) hc
      have hsgn2 : w183_sgn2Of i.val = w183_sgn2Of j.val := by
        have hc := congrFun h (w183_c2 i)
        rw [hu_apply i (w183_c2 i), hu_apply j (w183_c2 i)] at hc
        rw [hc2] at hc
        simp [w183_c2_ne_z0 i, w183_c2_ne_z0 j] at hc
        exact w183_intCast_eq hm3 (w183_pm01_of (w183_sgn2Of_eq _))
          (w183_pm01_of (w183_sgn2Of_eq _)) hc
      exact hkey (by simp [hc2, hsgn, hsgn2])
    · intro i
      obtain ⟨π', s', hs', hprod', hact⟩ :=
        omq_exists_signed_perm_two_coord (n := 4) (m := m) (by norm_num)
          (a := a) (b := b) (a' := w183_z0) (b' := w183_c2 i) hab (w183_z0_ne_c2 i)
          (e := w183_sgnOf i.val * δ) (he := w183_mul_pm (w183_sgnOf_eq i.val) hδ)
          (e' := w183_sgn2Of i.val * δ') (he' := w183_mul_pm (w183_sgn2Of_eq i.val) hδ')
          ((δ : ℤ) : ZMod m) ((δ' : ℤ) : ZMod m)
      refine ⟨π', s', hs', hprod', ?_⟩
      rw [hact, w183_cast_mul (σ := w183_sgnOf i.val) hδ,
        w183_cast_mul (σ := w183_sgn2Of i.val) hδ']
    · intro i l h
      have hui : u i w183_z0 = (w183_sgnOf i.val : ZMod m) := by
        rw [hu_apply i w183_z0]
        simp [w183_z0_ne_c2 i]
      have hul : u l w183_z1 = 0 := by
        rw [hu_apply l w183_z1]
        simp [show w183_z1 ≠ w183_z0 by decide, w183_z1_ne_c2 l]
      have hX : omqSignedAct π s (u l) w183_z0 = 0 := by
        unfold omqSignedAct
        rw [hsymm, hul]
        simp
      have hc := congrFun h w183_z0
      rw [hui, hX] at hc
      exact w183_pm_cast_ne_zero hm3 (w183_sgnOf_eq i.val) hc

end CFSG.LocalAnalysis.WeakClosure81
