module

public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabDefs
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabRigid
public import CFSG.LocalAnalysis.StandardType.GGPumpTwLabCompNe
public import CFSG.LocalAnalysis.StandardType.GGKacK1
public import CFSG.LocalAnalysis.StandardType.GGKacExcB2
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
import CFSG.LocalAnalysis.StandardType.GGKacTable

public section

namespace CFSG.StandardType

open CFSG.Assembly

private local instance (priority := high) l04fHL5_decEqLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')
private local instance (priority := high) l04fHL5_decEqOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')
private local instance (priority := high) l04fHL5_decEqDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')
private theorem l04fHL5_three_dvd (n : ℕ) : 3 ∣ 2 ^ n - 1 ∨ 3 ∣ 2 ^ n + 1 := by
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
private theorem l04fHL5_not_both {n : ℕ} (h1 : 3 ∣ 2 ^ n - 1) (h2 : 3 ∣ 2 ^ n + 1) : False := by
  have h2' : 3 ∣ 2 := by
    have hsub : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h2 h1
    have heq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have := Nat.one_le_two_pow (n := n); omega
    rwa [heq] at hsub
  norm_num at h2'
private theorem l04fHL5_shape_eq {n : ℕ} {o : GGKacOrbit} {tag : LargeEvenLieTag} {rank k : ℕ}
    (h : ggKacShapeLabel n o.lab = (tag, rank, k)) (htag : tag ≠ .C) :
    o.lab.tag = tag ∧ o.lab.rank = rank ∧ o.lab.n / n = k := by
  obtain ⟨⟨t, r, nn⟩, q⟩ := o
  simp only [ggKacShapeLabel] at h
  split at h
  · simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm htag
  · simp only [Prod.mk.injEq] at h
    exact ⟨h.1, h.2.1, h.2.2⟩
private theorem l04fHL5_shape_of_A {n : ℕ} {o : GGKacOrbit} (htag : o.lab.tag = .A)
    (hrank : o.lab.rank = 5) : ggKacShapeLabel n o.lab = (.A, 5, o.lab.n / n) := by
  simp only [ggKacShapeLabel]; rw [htag, hrank]
private theorem l04fHL5_shape_of_twA {n : ℕ} {o : GGKacOrbit} (htag : o.lab.tag = .twA)
    (hrank : o.lab.rank = 5) : ggKacShapeLabel n o.lab = (.twA, 5, o.lab.n / n) := by
  simp only [ggKacShapeLabel]; rw [htag, hrank]
private theorem l04fHL5_shape_of_twD {n : ℕ} {o : GGKacOrbit} (htag : o.lab.tag = .twD)
    (hrank : o.lab.rank = 4) : ggKacShapeLabel n o.lab = (.twD, 4, o.lab.n / n) := by
  simp only [ggKacShapeLabel]; rw [htag, hrank]
private theorem l04fHL5_shape_transfer {T : GGKacType} {tw : Bool} {n n₀ : ℕ}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits) :
    ∃ D' ∈ ggKacTable T tw 3 n₀, ∃ o' ∈ D'.orbits,
      ggKacShapeLabel n o.lab = ggKacShapeLabel n₀ o'.lab := by
  have hmem : GGKacDatum.shape n D ∈
      (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨D, hD, rfl⟩)
  rw [hshape] at hmem
  obtain ⟨D', hD'mem, hD'eq⟩ := List.mem_map.mp (Multiset.mem_coe.mp hmem)
  have hshapeOrb : ggKacShapeLabel n o.lab ∈
      (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) : Multiset (LargeEvenLieTag × ℕ × ℕ)) :=
    Multiset.mem_coe.mpr (List.mem_map.mpr ⟨o, ho, rfl⟩)
  have hfst : (↑(D.orbits.map (fun o => ggKacShapeLabel n o.lab)) :
        Multiset (LargeEvenLieTag × ℕ × ℕ)) =
      ↑(D'.orbits.map (fun o => ggKacShapeLabel n₀ o.lab)) := by
    have h := congrArg Prod.fst hD'eq
    simpa [GGKacDatum.shape] using h.symm
  rw [hfst] at hshapeOrb
  obtain ⟨o', ho', heqo⟩ := List.mem_map.mp (Multiset.mem_coe.mp hshapeOrb)
  exact ⟨D', hD'mem, o', ho', heqo.symm⟩
private theorem l04fHL5_div_eq {n m n₀ : ℕ} (hn₀ : 0 < n₀) (hdvd : n ∣ m)
    (heq : m / n = n₀ / n₀) : m = n := by
  rw [Nat.div_self hn₀] at heq
  have h := Nat.div_mul_cancel hdvd
  rw [heq] at h
  simpa using h.symm
private theorem l04fHL5_key {n n₀ : ℕ} (hn₀ : 0 < n₀) {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n) {tag : LargeEvenLieTag} {rank : ℕ} (htagC : tag ≠ .C)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = tag ∧ o'.lab.rank = rank → o'.lab.n = n₀))
    (h1 : ggKacShapeLabel n o.lab = (tag, rank, o.lab.n / n)) : o.lab.n = n := by
  obtain ⟨D', hD'mem, o', ho', heqo⟩ := l04fHL5_shape_transfer hshape hD ho
  have h' : ggKacShapeLabel n₀ o'.lab = (tag, rank, o.lab.n / n) := heqo ▸ h1
  obtain ⟨h1', h2', h3'⟩ := l04fHL5_shape_eq h' htagC
  have hk := hfin D' hD'mem o' ho' ⟨h1', h2'⟩
  have hdiv : o.lab.n / n = n₀ / n₀ := by rw [← h3', hk]
  exact l04fHL5_div_eq hn₀ hdvd hdiv
private theorem l04fHL5_key_false {n n₀ : ℕ} {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    {tag : LargeEvenLieTag} {rank : ℕ} (htagC : tag ≠ .C)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = tag ∧ o'.lab.rank = rank → False))
    (h1 : ggKacShapeLabel n o.lab = (tag, rank, o.lab.n / n)) : False := by
  obtain ⟨D', hD'mem, o', ho', heqo⟩ := l04fHL5_shape_transfer hshape hD ho
  have h' : ggKacShapeLabel n₀ o'.lab = (tag, rank, o.lab.n / n) := heqo ▸ h1
  obtain ⟨h1', h2', -⟩ := l04fHL5_shape_eq h' htagC
  exact hfin D' hD'mem o' ho' ⟨h1', h2'⟩
private theorem l04fHL5_pos_A {n n₀ : ℕ} (hn₀ : 0 < n₀) {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = .A ∧ o'.lab.rank = 5 → o'.lab.n = n₀))
    {f : ℕ} (hA : o.lab = ⟨.A, 5, f⟩) : f = n := by
  have hfn := l04fHL5_key hn₀ hshape hD ho hdvd (by decide) hfin
    (l04fHL5_shape_of_A (by rw [hA]) (by rw [hA]))
  have h1 : o.lab.n = f := by rw [hA]
  omega
private theorem l04fHL5_pos_twA {n n₀ : ℕ} (hn₀ : 0 < n₀) {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = .twA ∧ o'.lab.rank = 5 → o'.lab.n = n₀))
    {f : ℕ} (hA : o.lab = ⟨.twA, 5, f⟩) : f = n := by
  have hfn := l04fHL5_key hn₀ hshape hD ho hdvd (by decide) hfin
    (l04fHL5_shape_of_twA (by rw [hA]) (by rw [hA]))
  have h1 : o.lab.n = f := by rw [hA]
  omega
private theorem l04fHL5_pos_twD {n n₀ : ℕ} (hn₀ : 0 < n₀) {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hdvd : n ∣ o.lab.n)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = .twD ∧ o'.lab.rank = 4 → o'.lab.n = n₀))
    {f : ℕ} (hA : o.lab = ⟨.twD, 4, f⟩) : f = n := by
  have hfn := l04fHL5_key hn₀ hshape hD ho hdvd (by decide) hfin
    (l04fHL5_shape_of_twD (by rw [hA]) (by rw [hA]))
  have h1 : o.lab.n = f := by rw [hA]
  omega
private theorem l04fHL5_neg_A {n n₀ : ℕ} {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = .A ∧ o'.lab.rank = 5 → False))
    {f : ℕ} (hA : o.lab = ⟨.A, 5, f⟩) : False :=
  l04fHL5_key_false hshape hD ho (by decide) hfin
    (l04fHL5_shape_of_A (by rw [hA]) (by rw [hA]))
private theorem l04fHL5_neg_twA {n n₀ : ℕ} {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = .twA ∧ o'.lab.rank = 5 → False))
    {f : ℕ} (hA : o.lab = ⟨.twA, 5, f⟩) : False :=
  l04fHL5_key_false hshape hD ho (by decide) hfin
    (l04fHL5_shape_of_twA (by rw [hA]) (by rw [hA]))
private theorem l04fHL5_neg_twD {n n₀ : ℕ} {T : GGKacType} {tw : Bool}
    (hshape : (↑((ggKacTable T tw 3 n).map (GGKacDatum.shape n)) :
        Multiset (Multiset (LargeEvenLieTag × ℕ × ℕ) × ℕ × ℕ)) =
      ↑((ggKacTable T tw 3 n₀).map (GGKacDatum.shape n₀)))
    {D : GGKacDatum} (hD : D ∈ ggKacTable T tw 3 n) {o : GGKacOrbit} (ho : o ∈ D.orbits)
    (hfin : ∀ D' ∈ ggKacTable T tw 3 n₀, ∀ o' ∈ D'.orbits,
      (o'.lab.tag = .twD ∧ o'.lab.rank = 4 → False))
    {f : ℕ} (hA : o.lab = ⟨.twD, 4, f⟩) : False :=
  l04fHL5_key_false hshape hD ho (by decide) hfin
    (l04fHL5_shape_of_twD (by rw [hA]) (by rw [hA]))
private theorem l04fHL5_fin_E6f_1 :
    ∀ D ∈ ggKacTable .E6 false 3 1, ∀ o ∈ D.orbits,
      (o.lab.tag = .A ∧ o.lab.rank = 5 → o.lab.n = 1) ∧
      ((o.lab.tag = .twA ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → o.lab.n = 1) := by decide +kernel
private theorem l04fHL5_fin_E6f_2 :
    ∀ D ∈ ggKacTable .E6 false 3 2, ∀ o ∈ D.orbits,
      (o.lab.tag = .A ∧ o.lab.rank = 5 → o.lab.n = 2) ∧
      ((o.lab.tag = .twA ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_fin_E6t_1 :
    ∀ D ∈ ggKacTable .E6 true 3 1, ∀ o ∈ D.orbits,
      ((o.lab.tag = .A ∧ o.lab.rank = 5) → False) ∧
      (o.lab.tag = .twA ∧ o.lab.rank = 5 → o.lab.n = 1) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_fin_E6t_2 :
    ∀ D ∈ ggKacTable .E6 true 3 2, ∀ o ∈ D.orbits,
      ((o.lab.tag = .A ∧ o.lab.rank = 5) → False) ∧
      (o.lab.tag = .twA ∧ o.lab.rank = 5 → o.lab.n = 2) ∧
      (o.lab.tag = .twD ∧ o.lab.rank = 4 → o.lab.n = 2) := by decide +kernel
private theorem l04fHL5_fin_E7_1 :
    ∀ D ∈ ggKacTable .E7 false 3 1, ∀ o ∈ D.orbits,
      ((o.lab.tag = .A ∧ o.lab.rank = 5) → False) ∧
      (o.lab.tag = .twA ∧ o.lab.rank = 5 → o.lab.n = 1) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_fin_E7_2 :
    ∀ D ∈ ggKacTable .E7 false 3 2, ∀ o ∈ D.orbits,
      (o.lab.tag = .A ∧ o.lab.rank = 5 → o.lab.n = 2) ∧
      ((o.lab.tag = .twA ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_fin_E8_1 :
    ∀ D ∈ ggKacTable .E8 false 3 1, ∀ o ∈ D.orbits,
      ((o.lab.tag = .A ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twA ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_fin_E8_2 :
    ∀ D ∈ ggKacTable .E8 false 3 2, ∀ o ∈ D.orbits,
      ((o.lab.tag = .A ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twA ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_fin_F4_1 :
    ∀ D ∈ ggKacTable .F4 false 3 1, ∀ o ∈ D.orbits,
      ((o.lab.tag = .A ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twA ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_fin_F4_2 :
    ∀ D ∈ ggKacTable .F4 false 3 2, ∀ o ∈ D.orbits,
      ((o.lab.tag = .A ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twA ∧ o.lab.rank = 5) → False) ∧
      ((o.lab.tag = .twD ∧ o.lab.rank = 4) → False) := by decide +kernel
private theorem l04fHL5_label_eq_E6 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6) : lab = ⟨.E6, 0, lab.n⟩ := by
  have hr : lab.rank = 0 := by
    unfold LargeEvenInLambda2 at hlab; rw [htag] at hlab; exact hlab.2
  obtain ⟨t, r, n⟩ := lab
  have ht : t = .E6 := htag
  have hr' : r = 0 := hr
  cases ht; cases hr'; rfl
private theorem l04fHL5_label_eq_twE6 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twE6) : lab = ⟨.twE6, 0, lab.n⟩ := by
  have hr : lab.rank = 0 := by
    unfold LargeEvenInLambda2 at hlab; rw [htag] at hlab; exact hlab.2
  obtain ⟨t, r, n⟩ := lab
  have ht : t = .twE6 := htag
  have hr' : r = 0 := hr
  cases ht; cases hr'; rfl
private theorem l04fHL5_concl_E6 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .E6) {f : ℕ} (hn : lab.n = f) (h3 : 3 ∣ 2 ^ f + 1) :
    GGPumpTwLabConcl lab f := by
  refine ⟨hn, Or.inr (Or.inl ⟨?_, h3⟩)⟩
  rw [l04fHL5_label_eq_E6 hlab htag, hn]
private theorem l04fHL5_concl_twE6 {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (htag : lab.tag = .twE6) {f : ℕ} (hn : lab.n = f) (h3 : 3 ∣ 2 ^ f - 1) :
    GGPumpTwLabConcl lab f := by
  refine ⟨hn, Or.inr (Or.inr ⟨?_, h3⟩)⟩
  rw [l04fHL5_label_eq_twE6 hlab htag, hn]

theorem ggPumpTwLab_laneExc
    (hB2 : GGK0ExcB2) (lab : LargeEvenLabel) (hlab : LargeEvenInLambda2 lab)
    (hF : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) :
    GGPumpTwLabAt lab := by
  have hn : 1 ≤ lab.n := hlab.1
  have hpair : GGKacExcPair lab 3 :=
    ⟨by norm_num, by norm_num, l04fHL5_three_dvd lab.n, hF⟩
  intro Q hQ
  refine largeEvenRawDatum_mono ?_ (hB2 3 lab hlab hpair Q hQ)
  rintro R _ I F ⟨hQ, hP0⟩
  refine ⟨hQ, ?_⟩
  intro L' _ _ ψ hψ hker hcomm e J f he he3 hφ hJ hJlab
  obtain ⟨D, hDvalid, horbit, -, -, -, -, -⟩ := hP0 L' ψ hψ hker hcomm e he3 hφ
  obtain ⟨o, ho, hqs, hdn, hoLambda, hoHasO⟩ := horbit J hJ
  have hrg := ggPumpTwJLab_rigid hJlab hoLambda hoHasO
  rcases hF with hE6 | hTwE6 | hE7 | hE8 | hF4
  ·
    obtain ⟨T, tw, hTtw, hDmem⟩ := hDvalid
    have hgt : ggKacTypeOfLabel lab = some (.E6, false) := by simp only [ggKacTypeOfLabel, hE6]
    rw [hgt] at hTtw
    obtain ⟨rfl, rfl⟩ := Option.some.inj hTtw
    rcases l04fHL5_three_dvd lab.n with h3 | h3
    · have hsh := ggKacTable_shape .E6 false (p := 3) (n := lab.n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · rw [l04fHL5_pos_A (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E6f_2 D' hD' o' ho').1) hA.1] at hA
        exact (l04fHL5_not_both h3 hA.2).elim
      · exact (l04fHL5_neg_twA hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E6f_2 D' hD' o' ho').2.1) htwA.1).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E6f_2 D' hD' o' ho').2.2) htwD).elim
    · have hsh := ggKacTable_shape .E6 false (p := 3) (n := lab.n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact l04fHL5_concl_E6 hlab hE6 (l04fHL5_pos_A (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E6f_1 D' hD' o' ho').1) hA.1).symm hA.2
      · exact (l04fHL5_neg_twA hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E6f_1 D' hD' o' ho').2.1) htwA.1).elim
      · have hf := l04fHL5_pos_twD (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E6f_1 D' hD' o' ho').2.2) htwD
        exact l04fHL5_concl_E6 hlab hE6 hf.symm (by rw [hf]; exact h3)
  ·
    obtain ⟨T, tw, hTtw, hDmem⟩ := hDvalid
    have hgt : ggKacTypeOfLabel lab = some (.E6, true) := by simp only [ggKacTypeOfLabel, hTwE6]
    rw [hgt] at hTtw
    obtain ⟨rfl, rfl⟩ := Option.some.inj hTtw
    rcases l04fHL5_three_dvd lab.n with h3 | h3
    · have hsh := ggKacTable_shape .E6 true (p := 3) (n := lab.n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact (l04fHL5_neg_A hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E6t_2 D' hD' o' ho').1) hA.1).elim
      · exact l04fHL5_concl_twE6 hlab hTwE6 (l04fHL5_pos_twA (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E6t_2 D' hD' o' ho').2.1) htwA.1).symm htwA.2
      · have hf := l04fHL5_pos_twD (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E6t_2 D' hD' o' ho').2.2) htwD
        exact l04fHL5_concl_twE6 hlab hTwE6 hf.symm (by rw [hf]; exact h3)
    · have hsh := ggKacTable_shape .E6 true (p := 3) (n := lab.n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact (l04fHL5_neg_A hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E6t_1 D' hD' o' ho').1) hA.1).elim
      · rw [l04fHL5_pos_twA (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E6t_1 D' hD' o' ho').2.1) htwA.1] at htwA
        exact (l04fHL5_not_both htwA.2 h3).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E6t_1 D' hD' o' ho').2.2) htwD).elim
  ·
    obtain ⟨T, tw, hTtw, hDmem⟩ := hDvalid
    have hgt : ggKacTypeOfLabel lab = some (.E7, false) := by simp only [ggKacTypeOfLabel, hE7]
    rw [hgt] at hTtw
    obtain ⟨rfl, rfl⟩ := Option.some.inj hTtw
    rcases l04fHL5_three_dvd lab.n with h3 | h3
    · have hsh := ggKacTable_shape .E7 false (p := 3) (n := lab.n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · rw [l04fHL5_pos_A (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E7_2 D' hD' o' ho').1) hA.1] at hA
        exact (l04fHL5_not_both h3 hA.2).elim
      · exact (l04fHL5_neg_twA hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E7_2 D' hD' o' ho').2.1) htwA.1).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E7_2 D' hD' o' ho').2.2) htwD).elim
    · have hsh := ggKacTable_shape .E7 false (p := 3) (n := lab.n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact (l04fHL5_neg_A hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E7_1 D' hD' o' ho').1) hA.1).elim
      · rw [l04fHL5_pos_twA (by norm_num) hsh hDmem ho hdn
          (fun D' hD' o' ho' => (l04fHL5_fin_E7_1 D' hD' o' ho').2.1) htwA.1] at htwA
        exact (l04fHL5_not_both htwA.2 h3).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E7_1 D' hD' o' ho').2.2) htwD).elim
  ·
    obtain ⟨T, tw, hTtw, hDmem⟩ := hDvalid
    have hgt : ggKacTypeOfLabel lab = some (.E8, false) := by simp only [ggKacTypeOfLabel, hE8]
    rw [hgt] at hTtw
    obtain ⟨rfl, rfl⟩ := Option.some.inj hTtw
    rcases l04fHL5_three_dvd lab.n with h3 | h3
    · have hsh := ggKacTable_shape .E8 false (p := 3) (n := lab.n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact (l04fHL5_neg_A hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E8_2 D' hD' o' ho').1) hA.1).elim
      · exact (l04fHL5_neg_twA hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E8_2 D' hD' o' ho').2.1) htwA.1).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E8_2 D' hD' o' ho').2.2) htwD).elim
    · have hsh := ggKacTable_shape .E8 false (p := 3) (n := lab.n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact (l04fHL5_neg_A hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E8_1 D' hD' o' ho').1) hA.1).elim
      · exact (l04fHL5_neg_twA hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E8_1 D' hD' o' ho').2.1) htwA.1).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_E8_1 D' hD' o' ho').2.2) htwD).elim
  ·
    obtain ⟨T, tw, hTtw, hDmem⟩ := hDvalid
    have hgt : ggKacTypeOfLabel lab = some (.F4, false) := by simp only [ggKacTypeOfLabel, hF4]
    rw [hgt] at hTtw
    obtain ⟨rfl, rfl⟩ := Option.some.inj hTtw
    rcases l04fHL5_three_dvd lab.n with h3 | h3
    · have hsh := ggKacTable_shape .F4 false (p := 3) (n := lab.n) (n' := 2)
        (by norm_num) hn (by norm_num) (Or.inl ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact (l04fHL5_neg_A hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_F4_2 D' hD' o' ho').1) hA.1).elim
      · exact (l04fHL5_neg_twA hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_F4_2 D' hD' o' ho').2.1) htwA.1).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_F4_2 D' hD' o' ho').2.2) htwD).elim
    · have hsh := ggKacTable_shape .F4 false (p := 3) (n := lab.n) (n' := 1)
        (by norm_num) hn (by norm_num) (Or.inr ⟨h3, by norm_num⟩)
      rcases hrg with hA | htwA | htwD
      · exact (l04fHL5_neg_A hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_F4_1 D' hD' o' ho').1) hA.1).elim
      · exact (l04fHL5_neg_twA hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_F4_1 D' hD' o' ho').2.1) htwA.1).elim
      · exact (l04fHL5_neg_twD hsh hDmem ho
          (fun D' hD' o' ho' => (l04fHL5_fin_F4_1 D' hD' o' ho').2.2) htwD).elim

end CFSG.StandardType

end
