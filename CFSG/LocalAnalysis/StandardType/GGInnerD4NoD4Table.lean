module

public import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) s21586DecidableEqLargeEvenLabel :
    DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) s21586DecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) s21586DecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

theorem s2_1586_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
  induction n with
  | zero => left; norm_num
  | succ n ih =>
    rcases ih with h | h
    · right
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k + 1, ?_⟩
      rw [pow_succ]; omega
    · left
      obtain ⟨k, hk⟩ := h
      have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      refine ⟨2 * k - 1, ?_⟩
      rw [pow_succ]; omega

theorem s2_1586_shape_of {n : ℕ} {lab : LargeEvenLabel} (htag : lab.tag = .D)
    (hrank : lab.rank = 4) : ggKacShapeLabel n lab = (.D, 4, lab.n / n) := by
  unfold ggKacShapeLabel
  rw [htag, hrank]

theorem s2_1586_shape_eq {n k : ℕ} {o : GGKacOrbit}
    (h : ggKacShapeLabel n o.lab = (.D, 4, k)) :
    o.lab.tag = .D ∧ o.lab.rank = 4 ∧ o.lab.n / n = k := by
  unfold ggKacShapeLabel at h
  split at h
  · simp at h
  · simp only [Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2⟩

theorem s2_1586_fin_F4_1 :
    ∀ D ∈ ggKacTable .F4 false 3 1, ∀ o ∈ D.orbits,
      o.lab.tag = .D → o.lab.rank = 4 → False := by
  decide +kernel

theorem s2_1586_fin_F4_2 :
    ∀ D ∈ ggKacTable .F4 false 3 2, ∀ o ∈ D.orbits,
      o.lab.tag = .D → o.lab.rank = 4 → False := by
  decide +kernel

theorem s2_1586_fin_E7_1 :
    ∀ D ∈ ggKacTable .E7 false 3 1, ∀ o ∈ D.orbits,
      o.lab.tag = .D → o.lab.rank = 4 → False := by
  decide +kernel

theorem s2_1586_fin_E7_2 :
    ∀ D ∈ ggKacTable .E7 false 3 2, ∀ o ∈ D.orbits,
      o.lab.tag = .D → o.lab.rank = 4 → False := by
  decide +kernel

theorem s2_1586_fin_E8_1 :
    ∀ D ∈ ggKacTable .E8 false 3 1, ∀ o ∈ D.orbits,
      o.lab.tag = .D → o.lab.rank = 4 → False := by
  decide +kernel

theorem s2_1586_fin_E8_2 :
    ∀ D ∈ ggKacTable .E8 false 3 2, ∀ o ∈ D.orbits,
      o.lab.tag = .D → o.lab.rank = 4 → False := by
  decide +kernel

theorem s2_1586_extract_false {T : GGKacType} {n n₀ : ℕ}
    (hshape : (↑((ggKacTable T false 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T false 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T false 3 n)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) (htagD : o.lab.tag = .D) (hrankD : o.lab.rank = 4)
    (hfin : ∀ D' ∈ ggKacTable T false 3 n₀, ∀ o' ∈ D'.orbits,
      o'.lab.tag = .D → o'.lab.rank = 4 → False) : False := by
  have hmem : GGKacDatum.shape n D ∈
      (↑((ggKacTable T false 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨D, hD, rfl⟩)
  rw [hshape] at hmem
  obtain ⟨D', hD'mem, hD'eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
  have hshapeOrb : ggKacShapeLabel n o.lab ∈
      (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hfst : (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) =
      ↑(D'.orbits.map (fun o => ggKacShapeLabel n₀ o.lab)) := by
    have := congrArg Prod.fst hD'eq
    simpa [GGKacDatum.shape] using this.symm
  rw [hfst] at hshapeOrb
  obtain ⟨o', ho', heqo⟩ := List.mem_map.mp (Multiset.mem_coe.mp hshapeOrb)
  have hshapeR : ggKacShapeLabel n₀ o'.lab = (.D, 4, o.lab.n / n) := by
    rw [heqo, s2_1586_shape_of htagD hrankD]
  obtain ⟨htag', hrank', -⟩ := s2_1586_shape_eq hshapeR
  exact hfin D' hD'mem o' ho' htag' hrank'

theorem s2_1586_F4_no_D4 (n : ℕ) (hn : 1 ≤ n) :
    ∀ D ∈ ggKacTable .F4 false 3 n, ∀ o ∈ D.orbits,
      ¬ (o.lab.tag = .D ∧ o.lab.rank = 4) := by
  intro D hD o ho h
  rcases s2_1586_three_dvd n with h3 | h3
  · exact s2_1586_extract_false
      (ggKacTable_shape .F4 false (p := 3) (n := n) (n' := 2) (by norm_num) hn (by norm_num)
        (Or.inl ⟨h3, by norm_num⟩)) hD ho h.1 h.2 s2_1586_fin_F4_2
  · exact s2_1586_extract_false
      (ggKacTable_shape .F4 false (p := 3) (n := n) (n' := 1) (by norm_num) hn (by norm_num)
        (Or.inr ⟨h3, by norm_num⟩)) hD ho h.1 h.2 s2_1586_fin_F4_1

theorem s2_1586_E7_no_D4 (n : ℕ) (hn : 1 ≤ n) :
    ∀ D ∈ ggKacTable .E7 false 3 n, ∀ o ∈ D.orbits,
      ¬ (o.lab.tag = .D ∧ o.lab.rank = 4) := by
  intro D hD o ho h
  rcases s2_1586_three_dvd n with h3 | h3
  · exact s2_1586_extract_false
      (ggKacTable_shape .E7 false (p := 3) (n := n) (n' := 2) (by norm_num) hn (by norm_num)
        (Or.inl ⟨h3, by norm_num⟩)) hD ho h.1 h.2 s2_1586_fin_E7_2
  · exact s2_1586_extract_false
      (ggKacTable_shape .E7 false (p := 3) (n := n) (n' := 1) (by norm_num) hn (by norm_num)
        (Or.inr ⟨h3, by norm_num⟩)) hD ho h.1 h.2 s2_1586_fin_E7_1

theorem s2_1586_E8_no_D4 (n : ℕ) (hn : 1 ≤ n) :
    ∀ D ∈ ggKacTable .E8 false 3 n, ∀ o ∈ D.orbits,
      ¬ (o.lab.tag = .D ∧ o.lab.rank = 4) := by
  intro D hD o ho h
  rcases s2_1586_three_dvd n with h3 | h3
  · exact s2_1586_extract_false
      (ggKacTable_shape .E8 false (p := 3) (n := n) (n' := 2) (by norm_num) hn (by norm_num)
        (Or.inl ⟨h3, by norm_num⟩)) hD ho h.1 h.2 s2_1586_fin_E8_2
  · exact s2_1586_extract_false
      (ggKacTable_shape .E8 false (p := 3) (n := n) (n' := 1) (by norm_num) hn (by norm_num)
        (Or.inr ⟨h3, by norm_num⟩)) hD ho h.1 h.2 s2_1586_fin_E8_1

theorem s2_1586_no_D4 (T : GGKacType) (hT : T = .F4 ∨ T = .E7 ∨ T = .E8) (n : ℕ)
    (hn : 1 ≤ n) :
    ∀ D ∈ ggKacTable T false 3 n, ∀ o ∈ D.orbits,
      ¬ (o.lab.tag = .D ∧ o.lab.rank = 4) := by
  rcases hT with rfl | rfl | rfl
  · exact s2_1586_F4_no_D4 n hn
  · exact s2_1586_E7_no_D4 n hn
  · exact s2_1586_E8_no_D4 n hn

end CFSG.StandardType

end
