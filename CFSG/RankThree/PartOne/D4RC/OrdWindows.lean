module

public import CFSG.RankThree.PartOne.D4RC.OrdKill
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

instance rcs_decZD4 (f k : ℕ) : Decidable (zD4 f k) :=
  inferInstanceAs (Decidable ((k ∣ f * 12 ∧ ¬ k ∣ f * 4) ∨ k ∣ f * 6 ∨ k ∣ f * 2))

instance rcs_decZR (c f k : ℕ) : Decidable (zR c f k) :=
  inferInstanceAs (Decidable (k ∣ f * 2 ∨ (c = 3 ∧ k ∣ f * 3) ∨
    (c ≠ 3 ∧ k ∣ 2 * (f * 3) ∧ ¬ k ∣ f * 3)))

instance rcs_decZBC (n f k : ℕ) : Decidable (zBC n f k) :=
  inferInstanceAs (Decidable (∃ i ∈ Finset.Icc 1 n, k ∣ f * (2 * i)))

instance rcs_decZ2D (n f k : ℕ) : Decidable (z2D n f k) :=
  inferInstanceAs (Decidable ((k ∣ 2 * (f * n) ∧ ¬ k ∣ f * n) ∨
    ∃ i ∈ Finset.Icc 1 (n - 1), k ∣ f * (2 * i)))

instance rcs_decZList (f : ℕ) (L : List ℕ) (k : ℕ) : Decidable (zList f L k) :=
  inferInstanceAs (Decidable (∃ a ∈ L, k ∣ f * a))

instance rcs_decZG2 (f k : ℕ) : Decidable (zG2 f k) :=
  inferInstanceAs (Decidable (zList f [6, 2] k))

instance rcs_decZF4 (f k : ℕ) : Decidable (zF4 f k) :=
  inferInstanceAs (Decidable (zList f [12, 8, 6, 2] k))

instance rcs_decZ2E6 (f k : ℕ) : Decidable (z2E6 f k) :=
  inferInstanceAs (Decidable (k ∣ f * 12 ∨ (k ∣ 2 * (f * 9) ∧ ¬ k ∣ f * 9) ∨ k ∣ f * 8 ∨
    k ∣ f * 6 ∨ (k ∣ 2 * (f * 5) ∧ ¬ k ∣ f * 5) ∨ k ∣ f * 2))

theorem rcs_zG2_mul {s a t : ℕ} (hs : 0 < s) : zG2 (s * a) (s * t) ↔ zG2 a t :=
  rcs_zList_mul hs

theorem rcs_zF4_mul {s a t : ℕ} (hs : 0 < s) : zF4 (s * a) (s * t) ↔ zF4 a t :=
  rcs_zList_mul hs

theorem rcs_window {Z : ℕ → ℕ → Prop} (hom : ∀ s a t, 0 < s → (Z (s * a) (s * t) ↔ Z a t))
    {c e I A f g : ℕ} {Exc : ℕ → ℕ → Prop} (hf : 0 < f) (hg : 0 < g)
    (hG : ∀ k, 2 ≤ k → k ≠ 6 → Z g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → Z g k)
    (h1 : Z g (c * f)) (h2 : f * 3 ≤ g * e) (h3 : g * e ≤ f * 12)
    (hI : ∀ a b, Nat.Coprime a b → Z a (c * b) → ∃ i, 0 < i ∧ i ≤ I ∧ c * b ∣ a * i)
    (hA : ∀ a b, 0 < a → a * e ≤ b * 12 → b ≤ I → a ≤ A)
    (htab : ∀ a b, 0 < a → 0 < b → a ≤ A → b ≤ I → Nat.Coprime a b → Z a (c * b) →
      b * 3 ≤ a * e → a * e ≤ b * 12 →
      (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧ ((Z a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ Z a t))) ∨ Exc a b) :
    ∃ s a b, 0 < s ∧ g = s * a ∧ f = s * b ∧ Exc a b := by
  obtain ⟨s, a, b, hs, hga, hfb, hab, ha, hb, hZ, hb3, ha3, hG', hR'⟩ :=
    rcs_reduce hom hf hg hG hR h1 h2 h3
  have hbI : b ≤ I := rcs_bounds hab (hI a b hab hZ)
  exact ⟨s, a, b, hs, hga, hfb,
    rcs_close hG' hR' (htab a b ha hb (hA a b ha ha3 hbI) hbI hab hZ hb3 ha3)⟩

theorem rcs_tab_psp :
    ∀ c ∈ ({3, 6} : Finset ℕ), ∀ n ∈ Finset.Icc 3 24, ∀ b ∈ Finset.Icc 1 (2 * n),
      ∀ a ∈ Finset.Icc 1 (24 / n), Nat.Coprime a b → zBC n a (c * b) →
        b * 3 ≤ a * (n * n) → a * (n * n) ≤ b * 12 →
        (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧
          ((zBC n a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ zBC n a t))) ∨
          (c = 3 ∧ n = 3 ∧ a = 1 ∧ b = 2) := by
  decide +kernel


theorem rcs_zList_shape {L : List ℕ} {I a k : ℕ} (hL : ∀ x ∈ L, 0 < x ∧ x ≤ I)
    (h : zList a L k) : ∃ i, 0 < i ∧ i ≤ I ∧ k ∣ a * i := by
  obtain ⟨x, hx, hd⟩ := h
  exact ⟨x, (hL x hx).1, (hL x hx).2, hd⟩

theorem rcs_window_psp {c n f g : ℕ} (hc : c = 3 ∨ c = 6) (hn : 3 ≤ n) (hf : 0 < f)
    (hg : 0 < g) (hG : ∀ k, 2 ≤ k → k ≠ 6 → zBC n g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → zBC n g k) (h1 : zBC n g (c * f))
    (h2 : f * 3 ≤ g * (n * n)) (h3 : g * (n * n) ≤ f * 12) : c = 3 ∧ n = 3 ∧ f = 2 * g := by
  obtain ⟨s, a, b, hs, hga, hfb, hc3, hn3, rfl, rfl⟩ :=
    rcs_window (Z := zBC n) (Exc := fun a b => c = 3 ∧ n = 3 ∧ a = 1 ∧ b = 2) (e := n * n)
      (I := 2 * n) (A := 24 / n) (fun s a t hs => rcs_zBC_mul hs) hf hg hG hR h1 h2 h3
      (fun a b _ hZ => by
        obtain ⟨i, hi, hd⟩ := hZ
        have := Finset.mem_Icc.mp hi
        exact ⟨2 * i, by omega, by omega, hd⟩)
      (fun a b _ h hb => by
        have hn0 : 0 < n := by omega
        rw [Nat.le_div_iff_mul_le hn0]
        have h' : a * n * n ≤ 24 * n := by nlinarith
        exact Nat.le_of_mul_le_mul_right h' hn0)
      (fun a b ha hb haA hbI hab hZ hb3 ha3 => by
        have hn24 : n ≤ 24 := by
          have h0 : 1 ≤ 24 / n := le_trans ha haA
          rw [Nat.le_div_iff_mul_le (by omega)] at h0
          omega
        exact rcs_tab_psp c (by rcases hc with rfl | rfl <;> simp) n
          (Finset.mem_Icc.mpr ⟨hn, hn24⟩) b (Finset.mem_Icc.mpr ⟨hb, hbI⟩) a
          (Finset.mem_Icc.mpr ⟨ha, haA⟩) hab hZ hb3 ha3)
  exact ⟨hc3, hn3, by omega⟩

theorem rcs_tab_pom :
    ∀ c ∈ ({3, 6} : Finset ℕ), ∀ n ∈ Finset.Icc 4 25, ∀ b ∈ Finset.Icc 1 (2 * n),
      ∀ a ∈ Finset.Icc 1 (24 / (n - 1)), Nat.Coprime a b → z2D n a (c * b) →
        b * 3 ≤ a * (n * (n - 1)) → a * (n * (n - 1)) ≤ b * 12 →
        (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧
          ((z2D n a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ z2D n a t))) ∨ False := by
  decide +kernel

theorem rcs_window_pom {c n f g : ℕ} (hc : c = 3 ∨ c = 6) (hn : 4 ≤ n) (hf : 0 < f)
    (hg : 0 < g) (hG : ∀ k, 2 ≤ k → k ≠ 6 → z2D n g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → z2D n g k) (h1 : z2D n g (c * f))
    (h2 : f * 3 ≤ g * (n * (n - 1))) (h3 : g * (n * (n - 1)) ≤ f * 12) : False := by
  obtain ⟨s, a, b, hs, hga, hfb, hF⟩ :=
    rcs_window (Z := z2D n) (Exc := fun _ _ => False) (e := n * (n - 1))
      (I := 2 * n) (A := 24 / (n - 1)) (fun s a t hs => rcs_z2D_mul hs) hf hg hG hR h1 h2 h3
      (fun a b _ hZ => by
        rcases hZ with ⟨hk, -⟩ | ⟨i, hi, hd⟩
        · exact ⟨2 * n, by omega, le_rfl, by rw [show a * (2 * n) = 2 * (a * n) by ring]; exact hk⟩
        · have := Finset.mem_Icc.mp hi
          exact ⟨2 * i, by omega, by omega, hd⟩)
      (fun a b _ h hb => by
        obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
        have hm0 : 0 < m := by omega
        rw [Nat.add_sub_cancel] at h ⊢
        rw [Nat.le_div_iff_mul_le hm0]
        have h' : a * m * (m + 1) ≤ 24 * (m + 1) := by nlinarith
        exact Nat.le_of_mul_le_mul_right h' (by omega))
      (fun a b ha hb haA hbI hab hZ hb3 ha3 => by
        have hn25 : n ≤ 25 := by
          have h0 : 1 ≤ 24 / (n - 1) := le_trans ha haA
          rw [Nat.le_div_iff_mul_le (by omega)] at h0
          omega
        exact rcs_tab_pom c (by rcases hc with rfl | rfl <;> simp) n
          (Finset.mem_Icc.mpr ⟨hn, hn25⟩) b (Finset.mem_Icc.mpr ⟨hb, hbI⟩) a
          (Finset.mem_Icc.mpr ⟨ha, haA⟩) hab hZ hb3 ha3)
  exact hF

theorem rcs_tab_g2 :
    ∀ c ∈ ({3, 6} : Finset ℕ), ∀ b ∈ Finset.Icc 1 6, ∀ a ∈ Finset.Icc 1 12,
      Nat.Coprime a b → zG2 a (c * b) → b * 3 ≤ a * 6 → a * 6 ≤ b * 12 →
        (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧
          ((zG2 a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ zG2 a t))) ∨ (a = 1 ∧ b = 1) := by
  decide +kernel

theorem rcs_window_g2 {c f g : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) (hg : 0 < g)
    (hG : ∀ k, 2 ≤ k → k ≠ 6 → zG2 g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → zG2 g k) (h1 : zG2 g (c * f))
    (h2 : f * 3 ≤ g * 6) (h3 : g * 6 ≤ f * 12) : f = g := by
  obtain ⟨s, a, b, hs, hga, hfb, rfl, rfl⟩ :=
    rcs_window (Z := zG2) (Exc := fun a b => a = 1 ∧ b = 1) (e := 6)
      (I := 6) (A := 12) (fun s a t hs => rcs_zG2_mul hs) hf hg hG hR h1 h2 h3
      (fun a b _ hZ => rcs_zList_shape (by decide) hZ)
      (fun a b _ h hb => by omega)
      (fun a b ha hb haA hbI hab hZ hb3 ha3 =>
        rcs_tab_g2 c (by rcases hc with rfl | rfl <;> simp) b (Finset.mem_Icc.mpr ⟨hb, hbI⟩) a
          (Finset.mem_Icc.mpr ⟨ha, haA⟩) hab hZ hb3 ha3)
  omega

theorem rcs_tab_d4 :
    ∀ c ∈ ({3, 6} : Finset ℕ), ∀ b ∈ Finset.Icc 1 12, ∀ a ∈ Finset.Icc 1 12,
      Nat.Coprime a b → zD4 a (c * b) → b * 3 ≤ a * 12 → a * 12 ≤ b * 12 →
        (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧
          ((zD4 a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ zD4 a t))) ∨ (a = 1 ∧ b = 1) := by
  decide +kernel

theorem rcs_window_d4 {c f g : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) (hg : 0 < g)
    (hG : ∀ k, 2 ≤ k → k ≠ 6 → zD4 g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → zD4 g k) (h1 : zD4 g (c * f))
    (h2 : f * 3 ≤ g * 12) (h3 : g * 12 ≤ f * 12) : f = g := by
  obtain ⟨s, a, b, hs, hga, hfb, rfl, rfl⟩ :=
    rcs_window (Z := zD4) (Exc := fun a b => a = 1 ∧ b = 1) (e := 12)
      (I := 12) (A := 12) (fun s a t hs => rcs_zD4_mul hs) hf hg hG hR h1 h2 h3
      (fun a b _ hZ => by
        rcases hZ with ⟨hk, -⟩ | hk | hk
        · exact ⟨12, by omega, le_rfl, hk⟩
        · exact ⟨6, by omega, by omega, hk⟩
        · exact ⟨2, by omega, by omega, hk⟩)
      (fun a b _ h hb => by omega)
      (fun a b ha hb haA hbI hab hZ hb3 ha3 =>
        rcs_tab_d4 c (by rcases hc with rfl | rfl <;> simp) b (Finset.mem_Icc.mpr ⟨hb, hbI⟩) a
          (Finset.mem_Icc.mpr ⟨ha, haA⟩) hab hZ hb3 ha3)
  omega

theorem rcs_tab_f4 :
    ∀ c ∈ ({3, 6} : Finset ℕ), ∀ b ∈ Finset.Icc 1 12, ∀ a ∈ Finset.Icc 1 6,
      Nat.Coprime a b → zF4 a (c * b) → b * 3 ≤ a * 24 → a * 24 ≤ b * 12 →
        (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧
          ((zF4 a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ zF4 a t))) ∨ (c = 3 ∧ a = 1 ∧ b = 4) := by
  decide +kernel

theorem rcs_window_f4 {c f g : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) (hg : 0 < g)
    (hG : ∀ k, 2 ≤ k → k ≠ 6 → zF4 g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → zF4 g k) (h1 : zF4 g (c * f))
    (h2 : f * 3 ≤ g * 24) (h3 : g * 24 ≤ f * 12) : c = 3 ∧ f = 4 * g := by
  obtain ⟨s, a, b, hs, hga, hfb, hc3, rfl, rfl⟩ :=
    rcs_window (Z := zF4) (Exc := fun a b => c = 3 ∧ a = 1 ∧ b = 4) (e := 24)
      (I := 12) (A := 6) (fun s a t hs => rcs_zF4_mul hs) hf hg hG hR h1 h2 h3
      (fun a b _ hZ => rcs_zList_shape (by decide) hZ)
      (fun a b _ h hb => by omega)
      (fun a b ha hb haA hbI hab hZ hb3 ha3 =>
        rcs_tab_f4 c (by rcases hc with rfl | rfl <;> simp) b (Finset.mem_Icc.mpr ⟨hb, hbI⟩) a
          (Finset.mem_Icc.mpr ⟨ha, haA⟩) hab hZ hb3 ha3)
  exact ⟨hc3, by omega⟩

theorem rcs_tab_2e6 :
    ∀ c ∈ ({3, 6} : Finset ℕ), ∀ b ∈ Finset.Icc 1 18, ∀ a ∈ Finset.Icc 1 6,
      Nat.Coprime a b → z2E6 a (c * b) → b * 3 ≤ a * 36 → a * 36 ≤ b * 12 →
        (∃ t ∈ Finset.Icc 4 12, t ≠ 6 ∧
          ((z2E6 a t ∧ ¬ zD4 b t) ∨ (zR c b t ∧ ¬ z2E6 a t))) ∨ False := by
  decide +kernel

theorem rcs_window_2e6 {c f g : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) (hg : 0 < g)
    (hG : ∀ k, 2 ≤ k → k ≠ 6 → z2E6 g k → zD4 f k)
    (hR : ∀ k, 2 ≤ k → k ≠ 6 → zR c f k → z2E6 g k) (h1 : z2E6 g (c * f))
    (h2 : f * 3 ≤ g * 36) (h3 : g * 36 ≤ f * 12) : False := by
  obtain ⟨s, a, b, hs, hga, hfb, hF⟩ :=
    rcs_window (Z := z2E6) (Exc := fun _ _ => False) (e := 36)
      (I := 18) (A := 6) (fun s a t hs => rcs_z2E6_mul hs) hf hg hG hR h1 h2 h3
      (fun a b _ hZ => by
        rcases hZ with hk | ⟨hk, -⟩ | hk | hk | ⟨hk, -⟩ | hk
        · exact ⟨12, by omega, by omega, hk⟩
        · exact ⟨18, by omega, le_rfl, by rw [show a * 18 = 2 * (a * 9) by ring]; exact hk⟩
        · exact ⟨8, by omega, by omega, hk⟩
        · exact ⟨6, by omega, by omega, hk⟩
        · exact ⟨10, by omega, by omega, by rw [show a * 10 = 2 * (a * 5) by ring]; exact hk⟩
        · exact ⟨2, by omega, by omega, hk⟩)
      (fun a b _ h hb => by omega)
      (fun a b ha hb haA hbI hab hZ hb3 ha3 =>
        rcs_tab_2e6 c (by rcases hc with rfl | rfl <;> simp) b (Finset.mem_Icc.mpr ⟨hb, hbI⟩) a
          (Finset.mem_Icc.mpr ⟨ha, haA⟩) hab hZ hb3 ha3)
  exact hF

end CFSG.RankThree.PartOne.D4RC
