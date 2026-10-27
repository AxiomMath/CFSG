module

public import CFSG.LocalAnalysis.StandardType.GGExcRERegimeDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNThmUTableExc
public import CFSG.LocalAnalysis.StandardType.GGKacTableShapes
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def tabcAllowed (T : GGKacType) (tw : Bool) (p d : ℕ) :
    List (LargeEvenLieTag × ℕ × ℕ × ℕ) :=
  match T, tw, d with
  | .F4, false, _ => [(.C, 3, 1, 1), (.F4, 4, 1, 1)]
  | .E6, false, 1 => [(.A, 5, 1, 1), (.D, 5, 1, 1), (.E6, 6, 1, 1)]
  | .E6, false, _ => [(.A, 5, 1, 1), (.D, 4, 2, 1), (.E6, 6, 1, 1)]
  | .E6, true, 1 => [(.A, 5, 2, 1), (.D, 4, 2, 1), (.E6, 6, 2, 1)]
  | .E6, true, _ => [(.A, 5, 2, 1), (.D, 5, 2, 1), (.E6, 6, 2, 1)]
  | .E7, false, 1 => [(.D, 6, 1, 1), (.A, 6, 1, 1), (.E6, 6, 1, 1), (.E7, 7, 1, 1)]
  | .E7, false, _ => [(.D, 6, 1, 1), (.A, 6, 2, 1), (.E6, 6, 2, 1), (.E7, 7, 1, 1)]
  | .E8, false, 1 =>
      if p = 3 then [(.A, 8, 1, 1), (.E7, 7, 1, 1), (.D, 7, 1, 1), (.E8, 8, 1, 1)]
      else [(.A, 7, 1, 1), (.E7, 7, 1, 1), (.D, 7, 1, 1), (.E8, 8, 1, 1)]
  | .E8, false, _ =>
      if p = 3 then [(.A, 8, 2, 1), (.E7, 7, 1, 1), (.D, 7, 2, 1), (.E8, 8, 1, 1)]
      else [(.A, 7, 2, 1), (.E7, 7, 1, 1), (.D, 7, 2, 1), (.E8, 8, 1, 1)]
  | _, _, _ => []

private abbrev tabcCheckProp (T : GGKacType) (tw : Bool) (p d : ℕ) : Prop :=
  let D := k0DiagOf T
  let rho0 := k0Rho0 D tw d
  ∀ s ∈ k0VecsAux D.marks p, ∀ a ∈ D.omega, ∀ a0 ∈ D.omega,
    k0pAct a s = s →
    k0pAct (k0pMul a0 rho0) s = s →
    k0NumRhoOrbits (k0pMul a (k0pMul a0 rho0))
      ((List.range D.marks.length).filter (fun i => decide (s.getD i 0 > 0))) - 1 ≤ 1 →
    (ggKacShShapes D s (k0pMul a (k0pMul a0 rho0)) d).length = 1 →
    ∀ x ∈ ggKacShShapes D s (k0pMul a (k0pMul a0 rho0)) d, x ∈ tabcAllowed T tw p d

private theorem tabcCheck_F4_1 : tabcCheckProp .F4 false 3 1 := by decide +kernel
private theorem tabcCheck_F4_2 : tabcCheckProp .F4 false 3 2 := by decide +kernel
private theorem tabcCheck_E6_1 : tabcCheckProp .E6 false 5 1 := by decide +kernel
private theorem tabcCheck_E6_2 : tabcCheckProp .E6 false 5 2 := by decide +kernel
private theorem tabcCheck_twE6_1 : tabcCheckProp .E6 true 5 1 := by decide +kernel
private theorem tabcCheck_twE6_2 : tabcCheckProp .E6 true 5 2 := by decide +kernel
private theorem tabcCheck_E7_3_1 : tabcCheckProp .E7 false 3 1 := by decide +kernel
private theorem tabcCheck_E7_3_2 : tabcCheckProp .E7 false 3 2 := by decide +kernel
private theorem tabcCheck_E7_5_1 : tabcCheckProp .E7 false 5 1 := by decide +kernel
private theorem tabcCheck_E7_5_2 : tabcCheckProp .E7 false 5 2 := by decide +kernel
private theorem tabcCheck_E7_7_1 : tabcCheckProp .E7 false 7 1 := by decide +kernel
private theorem tabcCheck_E7_7_2 : tabcCheckProp .E7 false 7 2 := by decide +kernel
private theorem tabcCheck_E8_3_1 : tabcCheckProp .E8 false 3 1 := by decide +kernel
private theorem tabcCheck_E8_3_2 : tabcCheckProp .E8 false 3 2 := by decide +kernel
private theorem tabcCheck_E8_5_1 : tabcCheckProp .E8 false 5 1 := by decide +kernel
private theorem tabcCheck_E8_5_2 : tabcCheckProp .E8 false 5 2 := by decide +kernel
private theorem tabcCheck_E8_7_1 : tabcCheckProp .E8 false 7 1 := by decide +kernel
private theorem tabcCheck_E8_7_2 : tabcCheckProp .E8 false 7 2 := by decide +kernel

private def tabcRho0 (D : K0Diag) (tw : Bool) (d : ℕ) (a0 : List ℕ) : List ℕ :=
  k0pMul a0 (k0Rho0 D tw d)

private def tabcRho (D : K0Diag) (tw : Bool) (d : ℕ) (a0 a : List ℕ) : List ℕ :=
  k0pMul a (tabcRho0 D tw d a0)

private lemma tabcAllowed_of_checks {T : GGKacType} {tw : Bool} {p d : ℕ}
    {s a a0 : List ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (h1 : tabcCheckProp T tw p 1) (h2 : tabcCheckProp T tw p 2) (hd12 : d = 1 ∨ d = 2)
    (hs : s ∈ k0VecsAux (k0DiagOf T).marks p) (ha : a ∈ (k0DiagOf T).omega)
    (ha0 : a0 ∈ (k0DiagOf T).omega)
    (hact : k0pAct a s = s) (hbact : k0pAct (tabcRho0 (k0DiagOf T) tw d a0) s = s)
    (hz : k0NumRhoOrbits (tabcRho (k0DiagOf T) tw d a0 a)
      ((List.range (k0DiagOf T).marks.length).filter (fun i => decide (s.getD i 0 > 0))) - 1 ≤ 1)
    (hlen : (ggKacShShapes (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d).length = 1)
    (hxsh : x ∈ ggKacShShapes (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d) :
    x ∈ tabcAllowed T tw p d := by
  rcases hd12 with hd | hd
  · subst hd
    exact h1 s hs a ha a0 ha0 hact hbact hz hlen x hxsh
  · subst hd
    exact h2 s hs a ha a0 ha0 hact hbact hz hlen x hxsh

private lemma tabcRankZero {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8 ∨ lab.tag = .F4) :
    lab.rank = 0 := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only [LargeEvenLabel.tag] at h
  have hlab' := hlab
  simp only [LargeEvenInLambda2] at hlab'
  rcases h with h | h | h | h | h <;> rw [h] at hlab' <;> exact hlab'.2

private lemma tabcNPos {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) : 1 ≤ lab.n := by
  have := hlab
  simp only [LargeEvenInLambda2] at this
  exact this.1

private lemma tabcRE_of_not_generic {lab : LargeEvenLabel} {p : ℕ}
    (h : GGKacExcPair lab p) (hg : ¬ GGKacGeneric lab p) : GGKacRE lab p := by
  obtain ⟨hp, hp2, hb, htag⟩ := h
  refine ⟨hp, hp2, hb, ?_⟩
  by_contra hdisj
  exact hg ⟨hp, hp2, hb, htag,
    (by rintro ⟨hF4, hp3⟩; exact hdisj (Or.inl ⟨hF4, hp3⟩)),
    (by rintro ⟨hE6, hp35⟩; exact hdisj (Or.inr (Or.inl ⟨hE6, hp35⟩))),
    (by rintro ⟨hE78, hp357⟩; exact hdisj (Or.inr (Or.inr ⟨hE78, hp357⟩)))⟩

private theorem tabcShapes_eq_single {D : K0Diag} {s rho : List ℕ} {d n st : ℕ} {o : GGKacOrbit}
    (h : (k0Datum D s rho d n st).orbits = [o]) :
    ∃ x, ggKacShShapes D s rho d = [x] ∧
      o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n) := by
  have hsort : k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
      ((ggKacShShapes D s rho d).map fun x =>
        k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)) = [o] := by
    rw [← ggKacShDatum_orbits_shapes]
    exact h
  have hlen : ((ggKacShShapes D s rho d).map fun x =>
      k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).length = 1 := by
    have hp := (ggKacShSortBy_perm (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
      ((ggKacShShapes D s rho d).map fun x =>
        k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n))).length_eq
    rw [hsort] at hp
    simpa using hp.symm
  have hlen' : (ggKacShShapes D s rho d).length = 1 := by simpa using hlen
  have hlen'' : ∃ x, ggKacShShapes D s rho d = [x] := by
    match hl : ggKacShShapes D s rho d with
    | [] => rw [hl] at hlen'; simp at hlen'
    | [x] => exact ⟨x, rfl⟩
    | x :: y :: ys => rw [hl] at hlen'; simp at hlen'
  obtain ⟨x, hx⟩ := hlen''
  refine ⟨x, hx, ?_⟩
  have hmap : (ggKacShShapes D s rho d).map (fun x =>
      k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)) =
      [k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)] := by rw [hx]; rfl
  rw [hmap] at hsort
  have hsingle : k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
      [k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)] =
      [k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)] := rfl
  rw [hsingle] at hsort
  have hfx : k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n) = o := by simpa using hsort
  exact hfx.symm

private structure TabcPat (lab : LargeEvenLabel) (p : ℕ) (D : GGKacDatum) where
  T : GGKacType
  tw : Bool
  d : ℕ
  hty : ggKacTypeOfLabel lab = some (T, tw)
  s : List ℕ
  a : List ℕ
  a0 : List ℕ
  hs : s ∈ k0VecsAux (k0DiagOf T).marks p
  ha : a ∈ (k0DiagOf T).omega
  ha0 : a0 ∈ (k0DiagOf T).omega
  hact : k0pAct a s = s
  hbact : k0pAct (tabcRho0 (k0DiagOf T) tw d a0) s = s
  hd12 : d = 1 ∨ d = 2
  hd1 : d = 1 → p ∣ 2 ^ lab.n - 1
  hd2 : d = 2 → p ∣ 2 ^ lab.n + 1
  hDat : (k0Datum (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d lab.n 1).orbits = D.orbits
  hrZ : (k0Datum (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d lab.n 1).rZ = D.rZ

private lemma tabcPatExists {lab : LargeEvenLabel} {p : ℕ} {D : GGKacDatum}
    (hb : p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1) (hD : GGKacValid lab p D) :
    Nonempty (TabcPat lab p D) := by
  obtain ⟨T, tw, hty, hmem⟩ := hD
  set d : ℕ := if p ∣ 2 ^ lab.n - 1 then 1 else 2 with hd
  have hraw : D ∈ k0RawDatums (k0DiagOf T) tw p lab.n d := by
    rw [hd]
    exact ggKacSh_mem_rawDatums hmem hb
  obtain ⟨s, base, a0, a, rho, hs, hbase, ha0, hbase_act, ha, ha_act, hrho, hDdef⟩ :=
    ggKacShRawClass hraw
  have hd12 : d = 1 ∨ d = 2 := by rw [hd]; by_cases h : p ∣ 2 ^ lab.n - 1 <;> simp [h]
  have hd1 : d = 1 → p ∣ 2 ^ lab.n - 1 := by
    intro h1
    by_contra h1'
    have h2 : d = 2 := by rw [hd]; simp [h1']
    omega
  have hd2 : d = 2 → p ∣ 2 ^ lab.n + 1 := by
    intro h2
    by_cases h : p ∣ 2 ^ lab.n - 1
    · have h1 : d = 1 := by rw [hd]; simp [h]
      omega
    · exact hb.resolve_left h
  refine ⟨⟨T, tw, d, hty, s, a, a0, hs, ha, ha0, ha_act, ?_, hd12, hd1, hd2, ?_, ?_⟩⟩
  · rw [tabcRho0, ← hbase]
    exact hbase_act
  · show (k0Datum (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d lab.n 1).orbits = D.orbits
    rw [tabcRho, tabcRho0, hDdef, hrho, hbase]
    rfl
  · show (k0Datum (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d lab.n 1).rZ = D.rZ
    rw [tabcRho, tabcRho0, hDdef, hrho, hbase]
    rfl

private lemma tabcRow_F4 {lab : LargeEvenLabel} {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (htag : lab.tag = .F4) (hrank : lab.rank = 0) (hn : 1 ≤ lab.n)
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → 3 ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → 3 ∣ 2 ^ lab.n + 1)
    (hx : x ∈ tabcAllowed .F4 false 3 d)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow 3 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  rcases hd12 with rfl | rfl
  · have hb : (3 : ℕ) ∣ 2 ^ n - 1 := hd1 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])
  · have hb : (3 : ℕ) ∣ 2 ^ n + 1 := hd2 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])

private lemma tabcRow_E6 {lab : LargeEvenLabel} {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (htag : lab.tag = .E6) (hrank : lab.rank = 0) (hn : 1 ≤ lab.n)
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → 5 ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → 5 ∣ 2 ^ lab.n + 1)
    (hx : x ∈ tabcAllowed .E6 false 5 d)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow 5 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  rcases hd12 with rfl | rfl
  · have hb : (5 : ℕ) ∣ 2 ^ n - 1 := hd1 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])
  · have hb : (5 : ℕ) ∣ 2 ^ n + 1 := hd2 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])

private lemma tabcRow_twE6 {lab : LargeEvenLabel} {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (htag : lab.tag = .twE6) (hrank : lab.rank = 0) (hn : 1 ≤ lab.n)
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → 5 ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → 5 ∣ 2 ^ lab.n + 1)
    (hx : x ∈ tabcAllowed .E6 true 5 d)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow 5 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  rcases hd12 with rfl | rfl
  · have hb : (5 : ℕ) ∣ 2 ^ n - 1 := hd1 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])
  · have hb : (5 : ℕ) ∣ 2 ^ n + 1 := hd2 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])

private lemma tabcRow_E7 {lab : LargeEvenLabel} {p d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (htag : lab.tag = .E7) (hrank : lab.rank = 0) (hn : 1 ≤ lab.n)
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → p ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → p ∣ 2 ^ lab.n + 1)
    (hx : x ∈ tabcAllowed .E7 false p d)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  rcases hd12 with rfl | rfl
  · have hb : p ∣ 2 ^ n - 1 := hd1 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])
  · have hb : p ∣ 2 ^ n + 1 := hd2 rfl
    simp only [tabcAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])

private lemma tabcRow_E8_three {lab : LargeEvenLabel} {d : ℕ}
    {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (htag : lab.tag = .E8) (hrank : lab.rank = 0) (hn : 1 ≤ lab.n)
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → 3 ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → 3 ∣ 2 ^ lab.n + 1)
    (hx : x ∈ tabcAllowed .E8 false 3 d)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow 3 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  rcases hd12 with rfl | rfl
  · have hb : (3 : ℕ) ∣ 2 ^ n - 1 := hd1 rfl
    simp only [tabcAllowed, if_pos rfl, if_true, List.mem_cons, List.not_mem_nil, or_false,
      false_or] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])
  · have hb : (3 : ℕ) ∣ 2 ^ n + 1 := hd2 rfl
    simp only [tabcAllowed, if_pos rfl, if_true, List.mem_cons, List.not_mem_nil, or_false,
      false_or] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb]
    · exfalso; exact hX (by simp [k0LabelOf])

private lemma tabcRow_E8_other {lab : LargeEvenLabel} {p d : ℕ}
    {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (htag : lab.tag = .E8) (hrank : lab.rank = 0) (hn : 1 ≤ lab.n) (hp3 : p ≠ 3)
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → p ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → p ∣ 2 ^ lab.n + 1)
    (hx : x ∈ tabcAllowed .E8 false p d)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  rcases hd12 with rfl | rfl
  · have hb : p ∣ 2 ^ n - 1 := hd1 rfl
    simp only [tabcAllowed, if_neg hp3, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb, hp3]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb, hp3]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb, hp3]
    · exfalso; exact hX (by simp [k0LabelOf])
  · have hb : p ∣ 2 ^ n + 1 := hd2 rfl
    simp only [tabcAllowed, if_neg hp3, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb, hp3]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb, hp3]
    · simp only [k0LabelOf, Nat.one_mul]
      refine ⟨?_, ?_⟩
      · simp [LargeEvenInLambda2]; omega
      · unfold GGTablePRow
        simp [Nat.one_mul, hb, hp3]
    · exfalso; exact hX (by simp [k0LabelOf])

theorem ggTablePRow_of_ggKacValid_centred {lab : LargeEvenLabel} {p : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hc : GGKacExcCentred lab p) {D : GGKacDatum}
    (hD : GGKacValid lab p D) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit} (hDo : D.orbits = [o])
    (hX : o.lab ≠ lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab lab := by
  obtain ⟨hpair, hcentred⟩ := hc
  by_cases hgen : GGKacGeneric lab p
  · exact ggTablePRow_of_ggKacValid hlab hgen hD hrZ hDo hX
  · have hRE := tabcRE_of_not_generic hpair hgen
    obtain ⟨-, -, hb, hcase⟩ := hRE
    obtain ⟨P⟩ := tabcPatExists hb hD
    obtain ⟨T, tw, d, hty0, s, a, a0, hs, ha, ha0, hact, hbact, hd12, hd1, hd2, hDat, hrZeq⟩ := P
    have hn : 1 ≤ lab.n := tabcNPos hlab
    have hrank : lab.rank = 0 := tabcRankZero hlab hpair.2.2.2
    have horb : (k0Datum (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d lab.n 1).orbits = [o] :=
      by
      rw [hDat, hDo]
    obtain ⟨x, hx, ho⟩ := tabcShapes_eq_single horb
    have hlen1 : (ggKacShShapes (k0DiagOf T) s
        (tabcRho (k0DiagOf T) tw d a0 a) d).length = 1 := by rw [hx]; simp
    have hxsh : x ∈ ggKacShShapes (k0DiagOf T) s
        (tabcRho (k0DiagOf T) tw d a0 a) d := by rw [hx]; simp
    have hz : k0NumRhoOrbits (tabcRho (k0DiagOf T) tw d a0 a)
        ((List.range (k0DiagOf T).marks.length).filter
          (fun i => decide (s.getD i 0 > 0))) - 1 ≤ 1 := by
      change (k0Datum (k0DiagOf T) s (tabcRho (k0DiagOf T) tw d a0 a) d lab.n 1).rZ ≤ 1
      rw [hrZeq]
      exact hrZ
    have hX' : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab := by rwa [← ho]
    rcases hcase with ⟨hF4, hp3⟩ | ⟨hE6, hp35⟩ | ⟨hE78, hp357⟩
    · subst hp3
      have hty := hty0
      simp only [ggKacTypeOfLabel] at hty
      rw [hF4] at hty
      simp only [Option.some.injEq, Prod.mk.injEq] at hty
      obtain ⟨hT, htw⟩ := hty
      subst T; subst tw
      have hxA : x ∈ tabcAllowed .F4 false 3 d :=
        tabcAllowed_of_checks tabcCheck_F4_1 tabcCheck_F4_2 hd12 hs ha ha0 hact hbact hz hlen1 hxsh
      rw [ho]
      exact tabcRow_F4 hF4 hrank hn hd12 hd1 hd2 hxA hX'
    · rcases hp35 with rfl | rfl
      · exact absurd ⟨hE6, rfl⟩ hcentred
      · rcases hE6 with hE6 | htwE6
        · have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [hE6] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E6 false 5 d :=
            tabcAllowed_of_checks tabcCheck_E6_1 tabcCheck_E6_2 hd12 hs ha ha0 hact hbact hz hlen1
              hxsh
          rw [ho]
          exact tabcRow_E6 hE6 hrank hn hd12 hd1 hd2 hxA hX'
        · have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [htwE6] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E6 true 5 d :=
            tabcAllowed_of_checks tabcCheck_twE6_1 tabcCheck_twE6_2 hd12 hs ha ha0 hact hbact hz
              hlen1 hxsh
          rw [ho]
          exact tabcRow_twE6 htwE6 hrank hn hd12 hd1 hd2 hxA hX'
    · rcases hE78 with hE7 | hE8
      · rcases hp357 with rfl | rfl | rfl
        · have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [hE7] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E7 false 3 d :=
            tabcAllowed_of_checks tabcCheck_E7_3_1 tabcCheck_E7_3_2 hd12 hs ha ha0 hact hbact hz
              hlen1 hxsh
          rw [ho]
          exact tabcRow_E7 hE7 hrank hn hd12 hd1 hd2 hxA hX'
        · have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [hE7] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E7 false 5 d :=
            tabcAllowed_of_checks tabcCheck_E7_5_1 tabcCheck_E7_5_2 hd12 hs ha ha0 hact hbact hz
              hlen1 hxsh
          rw [ho]
          exact tabcRow_E7 hE7 hrank hn hd12 hd1 hd2 hxA hX'
        · have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [hE7] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E7 false 7 d :=
            tabcAllowed_of_checks tabcCheck_E7_7_1 tabcCheck_E7_7_2 hd12 hs ha ha0 hact hbact hz
              hlen1 hxsh
          rw [ho]
          exact tabcRow_E7 hE7 hrank hn hd12 hd1 hd2 hxA hX'
      · rcases hp357 with rfl | rfl | rfl
        · have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [hE8] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E8 false 3 d :=
            tabcAllowed_of_checks tabcCheck_E8_3_1 tabcCheck_E8_3_2 hd12 hs ha ha0 hact hbact hz
              hlen1 hxsh
          rw [ho]
          exact tabcRow_E8_three hE8 hrank hn hd12 hd1 hd2 hxA hX'
        · have hp3 : (5 : ℕ) ≠ 3 := by norm_num
          have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [hE8] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E8 false 5 d :=
            tabcAllowed_of_checks tabcCheck_E8_5_1 tabcCheck_E8_5_2 hd12 hs ha ha0 hact hbact hz
              hlen1 hxsh
          rw [ho]
          exact tabcRow_E8_other hE8 hrank hn hp3 hd12 hd1 hd2 hxA hX'
        · have hp3 : (7 : ℕ) ≠ 3 := by norm_num
          have hty := hty0
          simp only [ggKacTypeOfLabel] at hty
          rw [hE8] at hty
          simp only [Option.some.injEq, Prod.mk.injEq] at hty
          obtain ⟨hT, htw⟩ := hty
          subst T; subst tw
          have hxA : x ∈ tabcAllowed .E8 false 7 d :=
            tabcAllowed_of_checks tabcCheck_E8_7_1 tabcCheck_E8_7_2 hd12 hs ha ha0 hact hbact hz
              hlen1 hxsh
          rw [ho]
          exact tabcRow_E8_other hE8 hrank hn hp3 hd12 hd1 hd2 hxA hX'

end CFSG.StandardType

end
