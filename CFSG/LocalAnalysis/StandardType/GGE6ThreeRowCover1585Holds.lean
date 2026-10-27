module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRows1585
public import CFSG.LocalAnalysis.StandardType.GGKacK0V2

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) ltrcov_decEqLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) ltrcov_decEqOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ltrcov_decEqDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

theorem ltrcov_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
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

private theorem ltrcov_rank_zero {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) : lab.rank = 0 := by
  rcases htag with h | h
  · unfold LargeEvenInLambda2 at hΛ; rw [h] at hΛ; exact hΛ.2
  · unfold LargeEvenInLambda2 at hΛ; rw [h] at hΛ; exact hΛ.2

private theorem ltrcov_label_eq {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6 ∨ lab.tag = .twE6) : lab = ⟨lab.tag, 0, lab.n⟩ := by
  obtain ⟨t, r, n⟩ := lab
  have hr : r = 0 := ltrcov_rank_zero hΛ htag
  subst hr
  rfl

private theorem ltrcov_shape_lab {n : ℕ} {o : GGKacOrbit} {tag : LargeEvenLieTag} {rank k : ℕ}
    (h : ggKacShapeLabel n o.lab = (tag, rank, k)) (htag : tag ≠ .C) (hdvd : n ∣ o.lab.n) :
    o.lab = ⟨tag, rank, k * n⟩ := by
  obtain ⟨⟨t, r, nn⟩, q⟩ := o
  simp only [ggKacShapeLabel] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    exact absurd h1.symm htag
  · simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2, h3⟩ := h
    have hnmul : nn = k * n := by
      have hh := Nat.div_mul_cancel hdvd
      rw [h3] at hh
      exact hh.symm
    subst h1
    subst h2
    rw [hnmul]

theorem ggKacTable_shape_transfer {T : GGKacType} {tw : Bool} {n n₀ : ℕ}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit}
    (ho : o ∈ D.orbits) :
    ∃ D' ∈ ggKacTable T tw 3 n₀, ∃ o' ∈ D'.orbits,
      ggKacShapeLabel n o.lab = ggKacShapeLabel n₀ o'.lab := by
  have hmem : GGKacDatum.shape n D ∈
      (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
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
    have h := congrArg Prod.fst hD'eq
    simpa [GGKacDatum.shape] using h.symm
  rw [hfst] at hshapeOrb
  obtain ⟨o', ho', heqo⟩ := List.mem_map.mp (Multiset.mem_coe.mp hshapeOrb)
  exact ⟨D', hD'mem, o', ho', heqo.symm⟩

@[expose] def ltrcov_shapes : Bool → ℕ → List (LargeEvenLieTag × ℕ × ℕ)
  | false, 2 => [(.A, 1, 1), (.A, 4, 1), (.A, 2, 1), (.A, 2, 3), (.A, 5, 1), (.D, 4, 1),
      (.D, 5, 1), (.E6, 0, 1), (.triD4, 0, 1)]
  | false, 1 => [(.A, 2, 2), (.twA, 2, 1), (.A, 5, 1), (.twD, 4, 1), (.E6, 0, 1)]
  | true, 2 => [(.A, 2, 1), (.A, 2, 2), (.twA, 5, 1), (.twD, 4, 1), (.twE6, 0, 1)]
  | true, 1 => [(.A, 1, 1), (.twA, 4, 1), (.twA, 2, 1), (.twA, 2, 3), (.twA, 5, 1),
      (.D, 4, 1), (.twD, 5, 1), (.twE6, 0, 1), (.triD4, 0, 1)]
  | _, _ => []

theorem ltrcov_shapes_false2 :
    ∀ D ∈ ggKacTable .E6 false 3 2, ∀ o ∈ D.orbits,
      ggKacShapeLabel 2 o.lab ∈ ltrcov_shapes false 2 := by decide

theorem ltrcov_shapes_false1 :
    ∀ D ∈ ggKacTable .E6 false 3 1, ∀ o ∈ D.orbits,
      ggKacShapeLabel 1 o.lab ∈ ltrcov_shapes false 1 := by decide

theorem ltrcov_shapes_true2 :
    ∀ D ∈ ggKacTable .E6 true 3 2, ∀ o ∈ D.orbits,
      ggKacShapeLabel 2 o.lab ∈ ltrcov_shapes true 2 := by decide

theorem ltrcov_shapes_true1 :
    ∀ D ∈ ggKacTable .E6 true 3 1, ∀ o ∈ D.orbits,
      ggKacShapeLabel 1 o.lab ∈ ltrcov_shapes true 1 := by decide

theorem ggKacTable_E6_normalized_rank_ne_three {tw : Bool} {n : ℕ} (hn : 1 ≤ n)
    (h3 : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1)
    {D : GGKacDatum} (hD : D ∈ ggKacTable .E6 tw 3 n)
    {o : GGKacOrbit} (ho : o ∈ D.orbits) :
    (ggKacShapeLabel n o.lab).2.1 ≠ 3 := by
  rcases h3 with h3 | h3
  · have hshape := ggKacTable_shape .E6 tw (p := 3) (n := n) (n' := 2)
      Nat.prime_three hn (by norm_num : 1 ≤ 2) (Or.inl ⟨h3, by decide⟩)
    obtain ⟨D', hD'mem, o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
    cases tw
    · have hsh := ltrcov_shapes_false2 D' hD'mem o' ho'
      have hno : ∀ x ∈ ltrcov_shapes false 2, x.2.1 ≠ 3 := by decide
      intro h
      exact hno _ hsh (by simpa [heqo] using h)
    · have hsh := ltrcov_shapes_true2 D' hD'mem o' ho'
      have hno : ∀ x ∈ ltrcov_shapes true 2, x.2.1 ≠ 3 := by decide
      intro h
      exact hno _ hsh (by simpa [heqo] using h)
  · have hshape := ggKacTable_shape .E6 tw (p := 3) (n := n) (n' := 1)
      Nat.prime_three hn (by norm_num : 1 ≤ 1) (Or.inr ⟨h3, by decide⟩)
    obtain ⟨D', hD'mem, o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
    cases tw
    · have hsh := ltrcov_shapes_false1 D' hD'mem o' ho'
      have hno : ∀ x ∈ ltrcov_shapes false 1, x.2.1 ≠ 3 := by decide
      intro h
      exact hno _ hsh (by simpa [heqo] using h)
    · have hsh := ltrcov_shapes_true1 D' hD'mem o' ho'
      have hno : ∀ x ∈ ltrcov_shapes true 1, x.2.1 ≠ 3 := by decide
      intro h
      exact hno _ hsh (by simpa [heqo] using h)

private theorem ltrcov_classify_false2 {n : ℕ} {o : GGKacOrbit}
    (hshape : ggKacShapeLabel n o.lab ∈ ltrcov_shapes false 2) (hdvd : n ∣ o.lab.n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGB36JLabel ⟨.E6, 0, n⟩ o.lab ∨ o.lab = ⟨.E6, 0, n⟩ ∨
      o.lab = ⟨.A, 1, n⟩ ∨ o.lab = ⟨.A, 4, n⟩ ∨ o.lab = ⟨.A, 2, n⟩ := by
  simp only [ltrcov_shapes, List.mem_cons, List.not_mem_nil, or_false] at hshape
  rcases hshape with h | h | h | h | h | h | h | h | h
  · right; right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · right; right; right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · right; right; right; right
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · left
    have hlab : o.lab = ⟨.A, 2, 3 * n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inl ⟨rfl, h3, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩
  · left
    have hlab : o.lab = ⟨.A, 5, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inl ⟨rfl, h3, Or.inr (Or.inl rfl)⟩
  · left
    have hlab : o.lab = ⟨.D, 4, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inl ⟨rfl, h3, Or.inr (Or.inr (Or.inl rfl))⟩
  · left
    have hlab : o.lab = ⟨.D, 5, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inl ⟨rfl, h3, Or.inl rfl⟩
  · right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · left
    have hlab : o.lab = ⟨.triD4, 0, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inl ⟨rfl, h3, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩

private theorem ltrcov_classify_false1 {n : ℕ} {o : GGKacOrbit}
    (hshape : ggKacShapeLabel n o.lab ∈ ltrcov_shapes false 1) (hdvd : n ∣ o.lab.n)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGB36JLabel ⟨.E6, 0, n⟩ o.lab ∨ o.lab = ⟨.E6, 0, n⟩ ∨
      o.lab = ⟨.A, 2, 2 * n⟩ ∨ o.lab = ⟨.twA, 2, n⟩ := by
  simp only [ltrcov_shapes, List.mem_cons, List.not_mem_nil, or_false] at hshape
  rcases hshape with h | h | h | h | h
  · right; right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · right; right; right
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · left
    have hlab : o.lab = ⟨.A, 5, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inl ⟨rfl, h3, Or.inl rfl⟩)
  · left
    have hlab : o.lab = ⟨.twD, 4, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inl ⟨rfl, h3, Or.inr (Or.inl rfl)⟩)
  · right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this

private theorem ltrcov_classify_true2 {n : ℕ} {o : GGKacOrbit}
    (hshape : ggKacShapeLabel n o.lab ∈ ltrcov_shapes true 2) (hdvd : n ∣ o.lab.n)
    (h3 : 3 ∣ 2 ^ n - 1) :
    GGB36JLabel ⟨.twE6, 0, n⟩ o.lab ∨ o.lab = ⟨.twE6, 0, n⟩ ∨
      o.lab = ⟨.A, 2, n⟩ ∨ o.lab = ⟨.A, 2, 2 * n⟩ := by
  simp only [ltrcov_shapes, List.mem_cons, List.not_mem_nil, or_false] at hshape
  rcases hshape with h | h | h | h | h
  · right; right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · right; right; right
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · left
    have hlab : o.lab = ⟨.twA, 5, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inr (Or.inl ⟨rfl, h3, Or.inl rfl⟩))
  · left
    have hlab : o.lab = ⟨.twD, 4, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inr (Or.inl ⟨rfl, h3, Or.inr rfl⟩))
  · right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this

private theorem ltrcov_classify_true1 {n : ℕ} {o : GGKacOrbit}
    (hshape : ggKacShapeLabel n o.lab ∈ ltrcov_shapes true 1) (hdvd : n ∣ o.lab.n)
    (h3 : 3 ∣ 2 ^ n + 1) :
    GGB36JLabel ⟨.twE6, 0, n⟩ o.lab ∨ o.lab = ⟨.twE6, 0, n⟩ ∨
      o.lab = ⟨.A, 1, n⟩ ∨ o.lab = ⟨.twA, 4, n⟩ ∨ o.lab = ⟨.twA, 2, n⟩ := by
  simp only [ltrcov_shapes, List.mem_cons, List.not_mem_nil, or_false] at hshape
  rcases hshape with h | h | h | h | h | h | h | h | h
  · right; right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · right; right; right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · right; right; right; right
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · left
    have hlab : o.lab = ⟨.twA, 2, 3 * n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h3,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩))
  · left
    have hlab : o.lab = ⟨.twA, 5, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h3, Or.inr (Or.inl rfl)⟩))
  · left
    have hlab : o.lab = ⟨.D, 4, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h3, Or.inr (Or.inr (Or.inl rfl))⟩))
  · left
    have hlab : o.lab = ⟨.twD, 5, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h3, Or.inl rfl⟩))
  · right; left
    have := ltrcov_shape_lab h (by decide) hdvd
    simpa using this
  · left
    have hlab : o.lab = ⟨.triD4, 0, n⟩ := by
      have := ltrcov_shape_lab h (by decide) hdvd
      simpa using this
    rw [hlab]; unfold GGB36JLabel; dsimp only
    exact Or.inr (Or.inr (Or.inr ⟨rfl, h3, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩))

private theorem ltrcov_orbit_false2 {n : ℕ} (hn : 1 ≤ n) {D : GGKacDatum}
    (hD : D ∈ ggKacTable .E6 false 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n) (h3 : 3 ∣ 2 ^ n - 1) :
    GGB36JLabel ⟨.E6, 0, n⟩ o.lab ∨ o.lab = ⟨.E6, 0, n⟩ ∨
      o.lab = ⟨.A, 1, n⟩ ∨ o.lab = ⟨.A, 4, n⟩ ∨ o.lab = ⟨.A, 2, n⟩ := by
  have hshape := ggKacTable_shape .E6 false (p := 3) (n := n) (n' := 2)
    (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
  obtain ⟨D', hD'mem, o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
  have hsh' := ltrcov_shapes_false2 D' hD'mem o' ho'
  have hsh : ggKacShapeLabel n o.lab ∈ ltrcov_shapes false 2 := by
    rw [heqo]; exact hsh'
  exact ltrcov_classify_false2 hsh hdvd h3

private theorem ltrcov_orbit_false1 {n : ℕ} (hn : 1 ≤ n) {D : GGKacDatum}
    (hD : D ∈ ggKacTable .E6 false 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n) (h3 : 3 ∣ 2 ^ n + 1) :
    GGB36JLabel ⟨.E6, 0, n⟩ o.lab ∨ o.lab = ⟨.E6, 0, n⟩ ∨
      o.lab = ⟨.A, 2, 2 * n⟩ ∨ o.lab = ⟨.twA, 2, n⟩ := by
  have hshape := ggKacTable_shape .E6 false (p := 3) (n := n) (n' := 1)
    (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
  obtain ⟨D', hD'mem, o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
  have hsh' := ltrcov_shapes_false1 D' hD'mem o' ho'
  have hsh : ggKacShapeLabel n o.lab ∈ ltrcov_shapes false 1 := by
    rw [heqo]; exact hsh'
  exact ltrcov_classify_false1 hsh hdvd h3

private theorem ltrcov_orbit_true2 {n : ℕ} (hn : 1 ≤ n) {D : GGKacDatum}
    (hD : D ∈ ggKacTable .E6 true 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n) (h3 : 3 ∣ 2 ^ n - 1) :
    GGB36JLabel ⟨.twE6, 0, n⟩ o.lab ∨ o.lab = ⟨.twE6, 0, n⟩ ∨
      o.lab = ⟨.A, 2, n⟩ ∨ o.lab = ⟨.A, 2, 2 * n⟩ := by
  have hshape := ggKacTable_shape .E6 true (p := 3) (n := n) (n' := 2)
    (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
  obtain ⟨D', hD'mem, o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
  have hsh' := ltrcov_shapes_true2 D' hD'mem o' ho'
  have hsh : ggKacShapeLabel n o.lab ∈ ltrcov_shapes true 2 := by
    rw [heqo]; exact hsh'
  exact ltrcov_classify_true2 hsh hdvd h3

private theorem ltrcov_orbit_true1 {n : ℕ} (hn : 1 ≤ n) {D : GGKacDatum}
    (hD : D ∈ ggKacTable .E6 true 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n) (h3 : 3 ∣ 2 ^ n + 1) :
    GGB36JLabel ⟨.twE6, 0, n⟩ o.lab ∨ o.lab = ⟨.twE6, 0, n⟩ ∨
      o.lab = ⟨.A, 1, n⟩ ∨ o.lab = ⟨.twA, 4, n⟩ ∨ o.lab = ⟨.twA, 2, n⟩ := by
  have hshape := ggKacTable_shape .E6 true (p := 3) (n := n) (n' := 1)
    (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
  obtain ⟨D', hD'mem, o', ho', heqo⟩ := ggKacTable_shape_transfer hshape hD ho
  have hsh' := ltrcov_shapes_true1 D' hD'mem o' ho'
  have hsh : ggKacShapeLabel n o.lab ∈ ltrcov_shapes true 1 := by
    rw [heqo]; exact hsh'
  exact ltrcov_classify_true1 hsh hdvd h3

private theorem ltrcov_iso_eq_of_mem {o_lab labJ : LargeEvenLabel} {n : ℕ}
    (hJmem : labJ = ⟨.D, 5, n⟩ ∨ labJ = ⟨.twD, 5, n⟩ ∨ labJ = ⟨.A, 5, n⟩ ∨
      labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.triD4, 0, n⟩ ∨ labJ = ⟨.twD, 4, n⟩ ∨
      labJ = ⟨.A, 2, 3 * n⟩ ∨ labJ = ⟨.twA, 2, 3 * n⟩)
    (hiso : GGLabelIso o_lab labJ) : o_lab = labJ := by
  rcases hJmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold GGLabelIso at hiso
     rcases hiso with h | h | h | h | h | h | h | h <;> simp_all)

private theorem ltrcov_bad {labJ bad : LargeEvenLabel} {n : ℕ} (hn : 1 ≤ n)
    (hJmem : labJ = ⟨.D, 5, n⟩ ∨ labJ = ⟨.twD, 5, n⟩ ∨ labJ = ⟨.A, 5, n⟩ ∨
      labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.triD4, 0, n⟩ ∨ labJ = ⟨.twD, 4, n⟩ ∨
      labJ = ⟨.A, 2, 3 * n⟩ ∨ labJ = ⟨.twA, 2, 3 * n⟩)
    (h : labJ = bad)
    (hbad : bad = ⟨.E6, 0, n⟩ ∨ bad = ⟨.twE6, 0, n⟩ ∨ bad = ⟨.A, 1, n⟩ ∨
      bad = ⟨.A, 4, n⟩ ∨ bad = ⟨.A, 2, n⟩ ∨ bad = ⟨.A, 2, 2 * n⟩ ∨
      bad = ⟨.twA, 2, n⟩ ∨ bad = ⟨.twA, 4, n⟩) : False := by
  subst h
  rcases hbad with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rcases hJmem with hh | hh | hh | hh | hh | hh | hh | hh
    all_goals
      injection hh with h1 h2 h3
      first
      | exact LargeEvenLieTag.noConfusion h1
      | exact absurd h2 (by decide)
      | omega

private theorem ltrcov_extract_false2 {n : ℕ} (hn : 1 ≤ n) {labL labJ o_lab : LargeEvenLabel}
    (hlabL : labL = ⟨.E6, 0, n⟩) (hJmem : labJ = ⟨.D, 5, n⟩ ∨ labJ = ⟨.twD, 5, n⟩ ∨
      labJ = ⟨.A, 5, n⟩ ∨ labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.triD4, 0, n⟩ ∨
      labJ = ⟨.twD, 4, n⟩ ∨ labJ = ⟨.A, 2, 3 * n⟩ ∨ labJ = ⟨.twA, 2, 3 * n⟩)
    (hoeq : o_lab = labJ)
    (hclass : GGB36JLabel ⟨.E6, 0, n⟩ o_lab ∨ o_lab = ⟨.E6, 0, n⟩ ∨
      o_lab = ⟨.A, 1, n⟩ ∨ o_lab = ⟨.A, 4, n⟩ ∨ o_lab = ⟨.A, 2, n⟩) :
    GGB36JLabel labL labJ := by
  rw [hoeq] at hclass
  rw [hlabL]
  rcases hclass with h | h | h | h | h
  · exact h
  · exact (ltrcov_bad hn hJmem h (Or.inl rfl)).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inl rfl)))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).elim

private theorem ltrcov_extract_false1 {n : ℕ} (hn : 1 ≤ n) {labL labJ o_lab : LargeEvenLabel}
    (hlabL : labL = ⟨.E6, 0, n⟩) (hJmem : labJ = ⟨.D, 5, n⟩ ∨ labJ = ⟨.twD, 5, n⟩ ∨
      labJ = ⟨.A, 5, n⟩ ∨ labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.triD4, 0, n⟩ ∨
      labJ = ⟨.twD, 4, n⟩ ∨ labJ = ⟨.A, 2, 3 * n⟩ ∨ labJ = ⟨.twA, 2, 3 * n⟩)
    (hoeq : o_lab = labJ)
    (hclass : GGB36JLabel ⟨.E6, 0, n⟩ o_lab ∨ o_lab = ⟨.E6, 0, n⟩ ∨
      o_lab = ⟨.A, 2, 2 * n⟩ ∨ o_lab = ⟨.twA, 2, n⟩) :
    GGB36JLabel labL labJ := by
  rw [hoeq] at hclass
  rw [hlabL]
  rcases hclass with h | h | h | h
  · exact h
  · exact (ltrcov_bad hn hJmem h (Or.inl rfl)).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))).elim

private theorem ltrcov_extract_true2 {n : ℕ} (hn : 1 ≤ n) {labL labJ o_lab : LargeEvenLabel}
    (hlabL : labL = ⟨.twE6, 0, n⟩) (hJmem : labJ = ⟨.D, 5, n⟩ ∨ labJ = ⟨.twD, 5, n⟩ ∨
      labJ = ⟨.A, 5, n⟩ ∨ labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.triD4, 0, n⟩ ∨
      labJ = ⟨.twD, 4, n⟩ ∨ labJ = ⟨.A, 2, 3 * n⟩ ∨ labJ = ⟨.twA, 2, 3 * n⟩)
    (hoeq : o_lab = labJ)
    (hclass : GGB36JLabel ⟨.twE6, 0, n⟩ o_lab ∨ o_lab = ⟨.twE6, 0, n⟩ ∨
      o_lab = ⟨.A, 2, n⟩ ∨ o_lab = ⟨.A, 2, 2 * n⟩) :
    GGB36JLabel labL labJ := by
  rw [hoeq] at hclass
  rw [hlabL]
  rcases hclass with h | h | h | h
  · exact h
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inl rfl))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))).elim

private theorem ltrcov_extract_true1 {n : ℕ} (hn : 1 ≤ n) {labL labJ o_lab : LargeEvenLabel}
    (hlabL : labL = ⟨.twE6, 0, n⟩) (hJmem : labJ = ⟨.D, 5, n⟩ ∨ labJ = ⟨.twD, 5, n⟩ ∨
      labJ = ⟨.A, 5, n⟩ ∨ labJ = ⟨.twA, 5, n⟩ ∨ labJ = ⟨.triD4, 0, n⟩ ∨
      labJ = ⟨.twD, 4, n⟩ ∨ labJ = ⟨.A, 2, 3 * n⟩ ∨ labJ = ⟨.twA, 2, 3 * n⟩)
    (hoeq : o_lab = labJ)
    (hclass : GGB36JLabel ⟨.twE6, 0, n⟩ o_lab ∨ o_lab = ⟨.twE6, 0, n⟩ ∨
      o_lab = ⟨.A, 1, n⟩ ∨ o_lab = ⟨.twA, 4, n⟩ ∨ o_lab = ⟨.twA, 2, n⟩) :
    GGB36JLabel labL labJ := by
  rw [hoeq] at hclass
  rw [hlabL]
  rcases hclass with h | h | h | h | h
  · exact h
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inl rfl))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inl rfl)))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))).elim
  · exact (ltrcov_bad hn hJmem h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))).elim

private theorem ltrcov_rows_of_JLabel {labL labJ : LargeEvenLabel}
    (hpair : GGPairE6Three 3 labL labJ) (hLbl : GGB36JLabel labL labJ) :
    GGE6ThreeR1Labels1585 labL labJ ∨ GGE6ThreeR3Labels1585 labL labJ ∨
      GGE6ThreeR4Labels1585 labL labJ ∨ GGE6ThreeR16Labels1585 labL labJ ∨
      GGE6ThreeR4OppLabels1585 labL labJ ∨ GGE6ThreeR16OppLabels1585 labL labJ := by
  obtain ⟨t, r, n⟩ := labL
  obtain ⟨-, htagL, hJmem⟩ := hpair
  unfold GGB36JLabel at hLbl
  unfold GGE6ThreeR1Labels1585 GGE6ThreeR3Labels1585 GGE6ThreeR4Labels1585
    GGE6ThreeR16Labels1585 GGE6ThreeR4OppLabels1585 GGE6ThreeR16OppLabels1585 at ⊢
  dsimp only at hLbl ⊢
  rcases htagL with hE6 | hTw
  · subst hE6
    rcases hLbl with ⟨-, h3, hlab⟩ | ⟨-, h3, hlab⟩ | h | h
    · rcases hlab with rfl | rfl | rfl | rfl | rfl
      · exact Or.inl (Or.inl ⟨rfl, h3, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, h3, rfl⟩)))
      · exfalso
        rcases hJmem with hh | hh | hh | hh | hh | hh | hh | hh
        all_goals
          injection hh with h1 h2 h3
          first
          | exact LargeEvenLieTag.noConfusion h1
          | exact absurd h2 (by decide)
          | omega
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inl ⟨rfl, h3⟩, rfl⟩)))
      · exact Or.inr (Or.inl (Or.inl ⟨rfl, h3, rfl⟩))
    · rcases hlab with rfl | rfl | ⟨hn1, rfl⟩
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, h3, rfl⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inl ⟨rfl, h3⟩, rfl⟩))))
      · exfalso; subst hn1
        rcases hJmem with hh | hh | hh | hh | hh | hh | hh | hh <;> simp_all <;> omega
    · exfalso; exact absurd h.1 (by intro hh; cases hh)
    · exfalso; exact absurd h.1 (by intro hh; cases hh)
  · subst hTw
    rcases hLbl with h | h | ⟨-, h3, hlab⟩ | ⟨-, h3, hlab⟩
    · exfalso; exact absurd h.1 (by intro hh; cases hh)
    · exfalso; exact absurd h.1 (by intro hh; cases hh)
    · rcases hlab with rfl | rfl
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, h3, rfl⟩)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Or.inr ⟨rfl, h3⟩, rfl⟩))))
    · rcases hlab with rfl | rfl | rfl | rfl | rfl | ⟨hn1, rfl⟩
      · exact Or.inl (Or.inr ⟨rfl, h3, rfl⟩)
      · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, h3, rfl⟩)))
      · exfalso
        rcases hJmem with hh | hh | hh | hh | hh | hh | hh | hh
        all_goals
          injection hh with h1 h2 h3
          first
          | exact LargeEvenLieTag.noConfusion h1
          | exact absurd h2 (by decide)
          | omega
      · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Or.inr ⟨rfl, h3⟩, rfl⟩)))
      · exact Or.inr (Or.inl (Or.inr ⟨rfl, h3, rfl⟩))
      · exfalso; subst hn1
        rcases hJmem with hh | hh | hh | hh | hh | hh | hh | hh <;> simp_all <;> omega

theorem ggE6Three_rows_of_datum
    {labL labJ : LargeEvenLabel} {D : GGKacDatum} {o : GGKacOrbit}
    (hΛL : LargeEvenInLambda2 labL) (hpair : GGPairE6Three 3 labL labJ)
    (hValid : GGKacValid labL 3 D) (ho : o ∈ D.orbits) (hdvd : labL.n ∣ o.lab.n)
    (hoeq : o.lab = labJ) :
    GGE6ThreeR1Labels1585 labL labJ ∨ GGE6ThreeR3Labels1585 labL labJ ∨
      GGE6ThreeR4Labels1585 labL labJ ∨ GGE6ThreeR16Labels1585 labL labJ ∨
      GGE6ThreeR4OppLabels1585 labL labJ ∨ GGE6ThreeR16OppLabels1585 labL labJ := by
  obtain ⟨t, r, n⟩ := labL
  have htagL : t = .E6 ∨ t = .twE6 := hpair.2.1
  have hJmem := hpair.2.2
  have hn : 1 ≤ n := hΛL.1
  have hlabL_eq : (⟨t, r, n⟩ : LargeEvenLabel) = ⟨t, 0, n⟩ :=
    ltrcov_label_eq hΛL htagL
  rcases htagL with hE6 | hTw
  · subst hE6
    obtain ⟨T, tw, hTtw, hDmem⟩ := hValid
    have hgt : ggKacTypeOfLabel (⟨.E6, r, n⟩ : LargeEvenLabel) = some (.E6, false) := rfl
    rw [hgt] at hTtw
    cases Option.some.inj hTtw
    rcases ltrcov_three_dvd n with h3 | h3
    · have hclass := ltrcov_orbit_false2 hn hDmem ho hdvd h3
      exact ltrcov_rows_of_JLabel hpair
        (ltrcov_extract_false2 hn hlabL_eq hJmem hoeq hclass)
    · have hclass := ltrcov_orbit_false1 hn hDmem ho hdvd h3
      exact ltrcov_rows_of_JLabel hpair
        (ltrcov_extract_false1 hn hlabL_eq hJmem hoeq hclass)
  · subst hTw
    obtain ⟨T, tw, hTtw, hDmem⟩ := hValid
    have hgt : ggKacTypeOfLabel (⟨.twE6, r, n⟩ : LargeEvenLabel) = some (.E6, true) := rfl
    rw [hgt] at hTtw
    cases Option.some.inj hTtw
    rcases ltrcov_three_dvd n with h3 | h3
    · have hclass := ltrcov_orbit_true2 hn hDmem ho hdvd h3
      exact ltrcov_rows_of_JLabel hpair
        (ltrcov_extract_true2 hn hlabL_eq hJmem hoeq hclass)
    · have hclass := ltrcov_orbit_true1 hn hDmem ho hdvd h3
      exact ltrcov_rows_of_JLabel hpair
        (ltrcov_extract_true1 hn hlabL_eq hJmem hoeq hclass)


private theorem ltrcov_datum
    (hB : GGK0ExcB)
    {L : Type} [Group L] [Finite L] {J : Subgroup L} {y : MulAut L}
    {E : Subgroup (MulAut L)} {labL : LargeEvenLabel}
    (hΛL : LargeEvenInLambda2 labL) (htagL : labL.tag = .E6 ∨ labL.tag = .twE6)
    (hhL : GGHasLabel labL (L ⧸ Subgroup.center L))
    (hpairKac : GGKacExcPair labL 3) (hyE : y ∈ E) (hy3 : y ^ 3 = 1)
    (hcomp : IsComponentOf J (ggAutFixedSubgroup y))
    (hmark : LargeEvenMarking L (fun _ _ _ I _ θ => GGInducedInn E θ I)) :
    ∃ D : GGKacDatum, GGKacValid labL 3 D ∧ ∃ o ∈ D.orbits,
      o.qs = true ∧ labL.n ∣ o.lab.n ∧ LargeEvenInLambda2 o.lab ∧
      GGHasLabel o.lab (J ⧸ Subgroup.center J) := by
  obtain ⟨hperfL, lab', hΛlab', hrawLeg⟩ := hmark
  have hraw : LargeEvenRawDatum lab' (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : L ⧸ Subgroup.center L ≃* R, GGInducedInn E θ I) := hrawLeg
  have hHasLabel_lab' : GGHasLabel lab' (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F h => h.2.2.elim (fun θ _ => ⟨θ⟩)) hraw
  have hiso_mark : GGLabelIso lab' labL :=
    ggLabelRigidInput_holds lab' labL (L ⧸ Subgroup.center L) hΛlab' hΛL hHasLabel_lab' hhL
  have hrawX : LargeEvenRawDatum labL (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : L ⧸ Subgroup.center L ≃* R, GGInducedInn E θ I) :=
    largeEvenRawDatum_of_ggLabelIso hiso_mark hraw
  have hmain := hB 3 labL hΛL hpairKac _ hrawX
  obtain ⟨R, hRgrp, I, F, hQR⟩ := largeEvenRawDatum_exists hmain
  obtain ⟨hsimple, hna, θ, hInd⟩ := hQR.1
  let ψ : L →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψ : Function.Surjective ψ := by
    intro r
    obtain ⟨q, hq⟩ := θ.surjective r
    obtain ⟨l, hl⟩ := QuotientGroup.mk'_surjective (Subgroup.center L) q
    refine ⟨l, ?_⟩
    show θ (QuotientGroup.mk' (Subgroup.center L) l) = r
    rw [hl]
    exact hq
  have hker_le : ψ.ker ≤ Subgroup.center L := by
    intro l hl
    rw [MonoidHom.mem_ker] at hl
    have hl' : θ (QuotientGroup.mk' (Subgroup.center L) l) = 1 := by simpa [ψ] using hl
    have hl'' : QuotientGroup.mk' (Subgroup.center L) l = 1 :=
      θ.injective (by simpa using hl')
    exact (QuotientGroup.eq_one_iff l).mp hl''
  have hfixsub : ggFixSub y = ggAutFixedSubgroup y := by ext l; rfl
  have hcomp' : IsComponentOf J (ggFixSub y) := by rw [hfixsub]; exact hcomp
  have hφ_apply : ∀ l : L, ggInducedAut θ y (ψ l) = ψ (y l) := by
    intro l
    change ggInducedAut θ y (θ (l : L ⧸ Subgroup.center L)) =
      θ ((y l : L) : L ⧸ Subgroup.center L)
    exact ggInducedAut_apply θ y l
  have hφ_mem : ggInducedAut θ y ∈ I := hInd y hyE
  obtain ⟨D, hDval, ha, -⟩ :=
    hQR.2 L ψ hψ hker_le hperfL y hy3 ⟨ggInducedAut θ y, hφ_mem, hφ_apply⟩
  obtain ⟨o, ho, hqs, hdvd, hΛo, hHasO⟩ := ha J hcomp'
  exact ⟨D, hDval, o, ho, hqs, hdvd, hΛo, hHasO⟩

theorem ggE6ThreeRowCover1585_of_B
    (hB : GGK0ExcB) : GGE6ThreeRowCover1585 := by
  intro L _ _ J y E labL labJ hΛL hΛJ hpair hhL hhJ hy hy3 hyE hcomp hcomm hfix hmark
  obtain ⟨t, r, n⟩ := labL
  have htagL : t = .E6 ∨ t = .twE6 := hpair.2.1
  have hJmem := hpair.2.2
  have hpairKac : GGKacExcPair ⟨t, r, n⟩ 3 :=
    ⟨by norm_num, by norm_num, ltrcov_three_dvd n,
      htagL.elim (fun h => by rw [h]; exact Or.inl rfl)
        (fun h => by rw [h]; exact Or.inr (Or.inl rfl))⟩
  obtain ⟨D, hValid, o, ho, hqs, hdvd, hΛo, hHasO⟩ :=
    ltrcov_datum hB hΛL htagL hhL hpairKac hyE hy3 hcomp hmark
  have hiso : GGLabelIso o.lab labJ :=
    ggLabelRigidInput_holds o.lab labJ (J ⧸ Subgroup.center J) hΛo hΛJ hHasO hhJ
  have hoeq : o.lab = labJ := ltrcov_iso_eq_of_mem hJmem hiso
  exact ggE6Three_rows_of_datum hΛL hpair hValid ho hdvd hoeq

end CFSG.StandardType

end
