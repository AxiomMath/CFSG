module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PTrans
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PConj
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P71Val

public section

namespace CFSG.Quasithin.Fan86

namespace P71

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem exists_smul_of_valence (F : FanTree Γ G) {u v : V}
    (h : Fan86.valence Γ v = Fan86.valence Γ u) : ∃ g : G, g • u = v := by
  obtain ⟨p⟩ := F.isTree.connected.preconnected u v
  obtain ⟨n, hn⟩ := (F.walk_even_iff p).1 h
  exact F.exists_smul_of_walk_even n p (by omega)

theorem rightTransitive_conj (F : FanTree Γ G) {x y : ℕ → V} {i k : ℕ} (hik : i + 1 ≤ k) {g : G}
    (hg : ∀ m, i ≤ m → m ≤ k → g • x m = y m) (h : RightTransitive Γ G x i k) :
    RightTransitive Γ G y i k := by
  intro a b ha hau hb hbu
  have hk := hg k (by omega) le_rfl
  have hk1 := hg (k - 1) (by omega) (by omega)
  have key : ∀ c, Γ.Adj (y k) c → c ≠ y (k - 1) → Γ.Adj (x k) (g⁻¹ • c) ∧ g⁻¹ • c ≠ x (k - 1) := by
    intro c hc hcu
    refine ⟨?_, fun hh => hcu ?_⟩
    · have := (F.adj_smul g⁻¹ (y k) c).2 hc
      rwa [← hk, inv_smul_smul] at this
    · rw [← hk1, ← hh, smul_inv_smul]
  obtain ⟨ha1, ha2⟩ := key a ha hau
  obtain ⟨hb1, hb2⟩ := key b hb hbu
  obtain ⟨t, ht, hta⟩ := h _ _ ha1 ha2 hb1 hb2
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · rw [mem_stabRange] at ht ⊢
    intro m hm1 hm2
    rw [mul_smul, mul_smul, ← hg m hm1 hm2, inv_smul_smul, ht m hm1 hm2]
  · rw [mul_smul, mul_smul, hta, smul_inv_smul]

theorem leftTransitive_conj (F : FanTree Γ G) {x y : ℕ → V} {i k : ℕ} (hik : i + 1 ≤ k) {g : G}
    (hg : ∀ m, i ≤ m → m ≤ k → g • x m = y m) (h : LeftTransitive Γ G x i k) :
    LeftTransitive Γ G y i k := by
  intro a b ha hau hb hbu
  have hk := hg i le_rfl (by omega)
  have hk1 := hg (i + 1) (by omega) hik
  have key : ∀ c, Γ.Adj (y i) c → c ≠ y (i + 1) → Γ.Adj (x i) (g⁻¹ • c) ∧ g⁻¹ • c ≠ x (i + 1) := by
    intro c hc hcu
    refine ⟨?_, fun hh => hcu ?_⟩
    · have := (F.adj_smul g⁻¹ (y i) c).2 hc
      rwa [← hk, inv_smul_smul] at this
    · rw [← hk1, ← hh, smul_inv_smul]
  obtain ⟨ha1, ha2⟩ := key a ha hau
  obtain ⟨hb1, hb2⟩ := key b hb hbu
  obtain ⟨t, ht, hta⟩ := h _ _ ha1 ha2 hb1 hb2
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · rw [mem_stabRange] at ht ⊢
    intro m hm1 hm2
    rw [mul_smul, mul_smul, ← hg m hm1 hm2, inv_smul_smul, ht m hm1 hm2]
  · rw [mul_smul, mul_smul, hta, smul_inv_smul]

theorem two_trans (F : FanTree Γ G) (R : Arc Γ 8) (h6 : Fan86.valence Γ (R.vert 6) = 5)
    (hT : RightTransitive Γ G R.vert 3 6) {v a b c d : V} (hv : Fan86.valence Γ v = 5)
    (ha : Γ.Adj v a) (hb : Γ.Adj v b) (hc : Γ.Adj v c) (hd : Γ.Adj v d) (hab : a ≠ b)
    (hcd : c ≠ d) : ∃ g ∈ MulAction.stabilizer G v, g • a = c ∧ g • b = d := by
  obtain ⟨g₁, hg₁, hg₁a⟩ := F.loc_trans v a c ha hc
  have hb' : Γ.Adj v (g₁ • b) := F.adj_smul_of_mem_stabilizer hg₁ hb
  have hb'c : g₁ • b ≠ c := fun h => hab (MulAction.injective g₁ (hg₁a.trans h.symm))
  have hR56 : Γ.Adj (R.vert 6) (R.vert 5) := (R.adj 5 (by norm_num)).symm
  obtain ⟨g₀, -, hg₀⟩ := F.edgeTransitive (R.vert 6) (R.vert 5) v c hR56 hc
  have hg₀' : g₀ • R.vert 6 = v ∧ g₀ • R.vert 5 = c := by
    rcases hg₀ with h | h
    · exact h
    · exfalso
      have h1 := F.valence_smul_eq g₀ (R.vert 6)
      rw [h.1, h6] at h1
      have := valence_five_three F hc hv
      omega
  obtain ⟨h0v, h0c⟩ := hg₀'
  have key : ∀ e, Γ.Adj v e → e ≠ c → Γ.Adj (R.vert 6) (g₀⁻¹ • e) ∧ g₀⁻¹ • e ≠ R.vert (6 - 1) := by
    intro e he hec
    refine ⟨?_, fun h => hec ?_⟩
    · have := (F.adj_smul g₀⁻¹ v e).2 he
      rwa [← h0v, inv_smul_smul] at this
    · have h' : g₀⁻¹ • e = R.vert 5 := h
      rw [← h0c, ← h', smul_inv_smul]
  obtain ⟨hk1, hk2⟩ := key _ hb' hb'c
  obtain ⟨hl1, hl2⟩ := key d hd hcd.symm
  obtain ⟨k, hk, hkb⟩ := hT _ _ hk1 hk2 hl1 hl2
  rw [mem_stabRange] at hk
  have hk6 := hk 6 (by norm_num) le_rfl
  have hk5 := hk 5 (by norm_num) (by norm_num)
  refine ⟨g₀ * k * g₀⁻¹ * g₁, ?_, ?_, ?_⟩
  · refine MulAction.mem_stabilizer_iff.2 ?_
    rw [mul_smul, MulAction.mem_stabilizer_iff.1 hg₁, mul_smul, mul_smul, ← h0v, inv_smul_smul,
      hk6]
  · rw [mul_smul, hg₁a, mul_smul, mul_smul, ← h0c, inv_smul_smul, hk5]
  · rw [mul_smul, mul_smul, mul_smul, hkb, smul_inv_smul]

theorem agree_right (F : FanTree Γ G) {R B : Arc Γ 8} {g : G} {j : ℕ} (hj : 5 ≤ j)
    (hj8 : j + 1 ≤ 8) (hag : ∀ m, 3 ≤ m → m ≤ j → g • R.vert m = B.vert m)
    (hT : RightTransitive Γ G R.vert 3 j) :
    ∃ g' : G, ∀ m, 3 ≤ m → m ≤ j + 1 → g' • R.vert m = B.vert m := by
  have hTB := rightTransitive_conj F (by omega) hag hT
  have ha : Γ.Adj (B.vert j) (g • R.vert (j + 1)) := by
    have := (F.adj_smul g _ _).2 (R.adj j (by omega))
    rwa [hag j (by omega) le_rfl] at this
  have hau : g • R.vert (j + 1) ≠ B.vert (j - 1) := by
    intro h
    rw [← hag (j - 1) (by omega) (by omega)] at h
    have h2 := MulAction.injective g h
    exact R.nb (j - 1) (by omega) (by rw [show j - 1 + 2 = j + 1 by omega]; exact h2.symm)
  have hb : Γ.Adj (B.vert j) (B.vert (j + 1)) := B.adj j (by omega)
  have hbu : B.vert (j + 1) ≠ B.vert (j - 1) := fun h =>
    B.nb (j - 1) (by omega) (by rw [show j - 1 + 2 = j + 1 by omega]; exact h.symm)
  obtain ⟨h, hh, hha⟩ := hTB _ _ ha hau hb hbu
  rw [mem_stabRange] at hh
  refine ⟨h * g, fun m hm1 hm2 => ?_⟩
  by_cases hm : m ≤ j
  · rw [mul_smul, hag m hm1 hm, hh m hm1 hm]
  · rw [show m = j + 1 by omega, mul_smul]
    exact hha

theorem agree_left (F : FanTree Γ G) {R B : Arc Γ 8} {g : G} {i : ℕ} (hi : 1 ≤ i) (hi8 : i + 1 ≤ 8)
    (hag : ∀ m, i ≤ m → m ≤ 8 → g • R.vert m = B.vert m)
    (hT : LeftTransitive Γ G R.vert i 8) :
    ∃ g' : G, ∀ m, i - 1 ≤ m → m ≤ 8 → g' • R.vert m = B.vert m := by
  have hTB := leftTransitive_conj F (by omega) hag hT
  have ha : Γ.Adj (B.vert i) (g • R.vert (i - 1)) := by
    have h0 : Γ.Adj (R.vert i) (R.vert (i - 1)) := by
      have := (R.adj (i - 1) (by omega)).symm
      rwa [show i - 1 + 1 = i by omega] at this
    have := (F.adj_smul g _ _).2 h0
    rwa [hag i le_rfl (by omega)] at this
  have hau : g • R.vert (i - 1) ≠ B.vert (i + 1) := by
    intro h
    rw [← hag (i + 1) (by omega) (by omega)] at h
    have h2 := MulAction.injective g h
    exact R.nb (i - 1) (by omega) (by rw [show i - 1 + 2 = i + 1 by omega]; exact h2)
  have hb : Γ.Adj (B.vert i) (B.vert (i - 1)) := by
    have := (B.adj (i - 1) (by omega)).symm
    rwa [show i - 1 + 1 = i by omega] at this
  have hbu : B.vert (i - 1) ≠ B.vert (i + 1) := fun h =>
    B.nb (i - 1) (by omega) (by rw [show i - 1 + 2 = i + 1 by omega]; exact h)
  obtain ⟨h, hh, hha⟩ := hTB _ _ ha hau hb hbu
  rw [mem_stabRange] at hh
  refine ⟨h * g, fun m hm1 hm2 => ?_⟩
  by_cases hm : i ≤ m
  · rw [mul_smul, hag m hm hm2, hh m hm hm2]
  · rw [show m = i - 1 by omega, mul_smul]
    exact hha

theorem stage35 (F : FanTree Γ G) (R : Arc Γ 8) (h5 : Fan86.valence Γ (R.vert 4) = 5)
    (hT2 : RightTransitive Γ G R.vert 3 6) (B : Arc Γ 8)
    (hB : Fan86.valence Γ (B.vert 4) = 5) :
    ∃ g : G, ∀ m, 3 ≤ m → m ≤ 5 → g • R.vert m = B.vert m := by
  have h6 : Fan86.valence Γ (R.vert 6) = 5 :=
    (valence_arc F R (by norm_num) h5 6 (by norm_num)).1 (by norm_num)
  obtain ⟨g₀, hg₀⟩ := exists_smul_of_valence F (u := R.vert 4) (v := B.vert 4) (by rw [h5, hB])
  have h3 : Γ.Adj (B.vert 4) (g₀ • R.vert 3) := by
    have := (F.adj_smul g₀ _ _).2 (R.adj 3 (by norm_num)).symm
    rwa [hg₀] at this
  have h5' : Γ.Adj (B.vert 4) (g₀ • R.vert 5) := by
    have := (F.adj_smul g₀ _ _).2 (R.adj 4 (by norm_num))
    rwa [hg₀] at this
  have hne : g₀ • R.vert 3 ≠ g₀ • R.vert 5 := fun h =>
    R.nb 3 (by norm_num) (MulAction.injective g₀ h)
  obtain ⟨g₁, hg₁, e3, e5⟩ := two_trans F R h6 hT2 hB h3 h5' (B.adj 3 (by norm_num)).symm
    (B.adj 4 (by norm_num)) hne (B.nb 3 (by norm_num))
  refine ⟨g₁ * g₀, fun m hm1 hm2 => ?_⟩
  have h4 : m = 3 ∨ m = 4 ∨ m = 5 := by omega
  rcases h4 with rfl | rfl | rfl
  · rw [mul_smul, e3]
  · rw [mul_smul, hg₀, MulAction.mem_stabilizer_iff.1 hg₁]
  · rw [mul_smul, e5]

theorem exists_smul_arc (F : FanTree Γ G) (R : Arc Γ 8) (h5 : Fan86.valence Γ (R.vert 4) = 5)
    (hT : RightTransitive Γ G R.vert 3 5 ∧ RightTransitive Γ G R.vert 3 6 ∧
      RightTransitive Γ G R.vert 3 7 ∧ LeftTransitive Γ G R.vert 3 8 ∧
      LeftTransitive Γ G R.vert 2 8 ∧ LeftTransitive Γ G R.vert 1 8)
    (B : Arc Γ 8) (hB : Fan86.valence Γ (B.vert 4) = 5) :
    ∃ g : G, ∀ m, m ≤ 8 → g • R.vert m = B.vert m := by
  obtain ⟨T1, T2, T3, T4, T5, T6⟩ := hT
  obtain ⟨g₁, h1⟩ := stage35 F R h5 T2 B hB
  obtain ⟨g₂, h2⟩ := agree_right F (by norm_num) (by norm_num) h1 T1
  obtain ⟨g₃, h3⟩ := agree_right F (by norm_num) (by norm_num) h2 T2
  obtain ⟨g₄, h4⟩ := agree_right F (by norm_num) (by norm_num) h3 T3
  obtain ⟨g₅, h5⟩ := agree_left F (by norm_num) (by norm_num) (fun m hm1 hm2 => h4 m hm1 hm2) T4
  obtain ⟨g₆, h6⟩ := agree_left F (by norm_num) (by norm_num) h5 T5
  obtain ⟨g₇, h7⟩ := agree_left F (by norm_num) (by norm_num) h6 T6
  exact ⟨g₇, fun m hm => h7 m (by omega) hm⟩

@[expose] def ArcTrans (Γ : SimpleGraph V) (G : Type*) [Group G] [MulAction G V] : Prop :=
  ∀ A B : Arc Γ 8, Fan86.valence Γ (A.vert 0) = 5 → Fan86.valence Γ (B.vert 0) = 5 →
    ∃ g : G, ∀ m, m ≤ 8 → g • A.vert m = B.vert m

theorem valence_four_of_zero (F : FanTree Γ G) (A : Arc Γ 8)
    (h : Fan86.valence Γ (A.vert 0) = 5) : Fan86.valence Γ (A.vert 4) = 5 := by
  have h1 := valence_five_three F (A.adj 0 (by norm_num)) h
  have h2 := valence_three_five F (A.adj 1 (by norm_num)) h1
  have h3 := valence_five_three F (A.adj 2 (by norm_num)) h2
  exact valence_three_five F (A.adj 3 (by norm_num)) h3

theorem arcTrans_of_tight (F : FanTree Γ G) (R : Arc Γ 8) (h5 : Fan86.valence Γ (R.vert 4) = 5)
    (hT : RightTransitive Γ G R.vert 3 5 ∧ RightTransitive Γ G R.vert 3 6 ∧
      RightTransitive Γ G R.vert 3 7 ∧ LeftTransitive Γ G R.vert 3 8 ∧
      LeftTransitive Γ G R.vert 2 8 ∧ LeftTransitive Γ G R.vert 1 8) : ArcTrans Γ G := by
  intro A B hA hB
  obtain ⟨gA, hgA⟩ := exists_smul_arc F R h5 hT A (valence_four_of_zero F A hA)
  obtain ⟨gB, hgB⟩ := exists_smul_arc F R h5 hT B (valence_four_of_zero F B hB)
  refine ⟨gB * gA⁻¹, fun m hm => ?_⟩
  rw [mul_smul, inv_smul_eq_iff.2 (hgA m hm).symm, hgB m hm]

end P71

end CFSG.Quasithin.Fan86
