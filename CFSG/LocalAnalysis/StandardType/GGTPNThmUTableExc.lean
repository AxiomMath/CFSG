module

public import CFSG.LocalAnalysis.StandardType.GGKacTablePattern
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private def k0excShapes (D : K0Diag) (s rho : List ℕ) (d : ℕ) :
    List (LargeEvenLieTag × ℕ × ℕ × ℕ) :=
  let nNodes := D.marks.length
  let zero := (List.range nNodes).filter (fun i => decide (s.getD i 0 = 0))
  let comps := k0Comps D zero
  let img : List ℕ → List ℕ := fun c => k0SortNat (c.map (fun i => rho.getD i 0))
  (k0CompOrbits img (nNodes + 1) comps []).map (fun orb =>
    let k := orb.length
    let c := orb.headD []
    let p := k0CompType D c
    let rk := k0pPow rho k
    let o := k0AutOrder c rk
    let tw := if d = 2 ∧ k % 2 = 1 ∧ k0Tau0Of p.1 p.2 then
                (if o = 1 then 2 else if o = 2 then 1 else o) else o
    (p.1, p.2, tw, k))

private def k0excAllowed (T : GGKacType) (tw : Bool) (d : ℕ) :
    List (LargeEvenLieTag × ℕ × ℕ × ℕ) :=
  match T, tw, d with
  | .E6, false, 1 => [(.A, 5, 1, 1), (.D, 5, 1, 1), (.E6, 6, 1, 1)]
  | .E6, false, _ => [(.A, 5, 1, 1), (.D, 4, 2, 1), (.E6, 6, 1, 1)]
  | .E6, true, 1 => [(.A, 5, 2, 1), (.D, 4, 2, 1), (.E6, 6, 2, 1)]
  | .E6, true, _ => [(.A, 5, 2, 1), (.D, 5, 2, 1), (.E6, 6, 2, 1)]
  | .E7, false, 1 => [(.A, 6, 1, 1), (.D, 6, 1, 1), (.E6, 6, 1, 1), (.E7, 7, 1, 1)]
  | .E7, false, _ => [(.A, 6, 2, 1), (.D, 6, 1, 1), (.E6, 6, 2, 1), (.E7, 7, 1, 1)]
  | .E8, false, 1 => [(.A, 7, 1, 1), (.D, 7, 1, 1), (.E7, 7, 1, 1), (.E8, 8, 1, 1)]
  | .E8, false, _ => [(.A, 7, 2, 1), (.D, 7, 2, 1), (.E7, 7, 1, 1), (.E8, 8, 1, 1)]
  | .F4, _, _ => [(.C, 3, 1, 1), (.F4, 4, 1, 1)]
  | _, _, _ => []

private abbrev k0excCheckProp (T : GGKacType) (tw : Bool) (d : ℕ) : Prop :=
  ∀ s ∈ ggKacSupports (k0DiagOf T).marks.length,
  ∀ a ∈ (k0DiagOf T).omega,
    let rho := k0pMul a (k0Rho0 (k0DiagOf T) tw d)
    k0pAct rho s = s →
    ggKacSupportGcd T rho s = 1 →
    k0NumRhoOrbits rho ((List.range (k0DiagOf T).marks.length).filter
      (fun i => decide (s.getD i 0 > 0))) - 1 ≤ 1 →
    (k0excShapes (k0DiagOf T) s rho d).length = 1 →
    ∀ x ∈ k0excShapes (k0DiagOf T) s rho d, x ∈ k0excAllowed T tw d

private theorem k0excCheck_E6_false_1 : k0excCheckProp .E6 false 1 := by decide +kernel
private theorem k0excCheck_E6_false_2 : k0excCheckProp .E6 false 2 := by decide +kernel
private theorem k0excCheck_E6_true_1 : k0excCheckProp .E6 true 1 := by decide +kernel
private theorem k0excCheck_E6_true_2 : k0excCheckProp .E6 true 2 := by decide +kernel
private theorem k0excCheck_E7_1 : k0excCheckProp .E7 false 1 := by decide +kernel
private theorem k0excCheck_E7_2 : k0excCheckProp .E7 false 2 := by decide +kernel
private theorem k0excCheck_E8_1 : k0excCheckProp .E8 false 1 := by decide +kernel
private theorem k0excCheck_E8_2 : k0excCheckProp .E8 false 2 := by decide +kernel
private theorem k0excCheck_F4_1 : k0excCheckProp .F4 false 1 := by decide +kernel
private theorem k0excCheck_F4_2 : k0excCheckProp .F4 false 2 := by decide +kernel

private theorem k0excCheck (T : GGKacType) (tw : Bool) (d : ℕ)
    (hty : (T, tw) = (.E6, false) ∨ (T, tw) = (.E6, true) ∨ (T, tw) = (.E7, false) ∨
      (T, tw) = (.E8, false) ∨ (T, tw) = (.F4, false))
    (hd : d = 1 ∨ d = 2) : k0excCheckProp T tw d := by
  rcases hd with rfl | rfl
  · rcases hty with h | h | h | h | h <;> injection h with h1 h2 <;> subst h1 <;> subst h2
    · exact k0excCheck_E6_false_1
    · exact k0excCheck_E6_true_1
    · exact k0excCheck_E7_1
    · exact k0excCheck_E8_1
    · exact k0excCheck_F4_1
  · rcases hty with h | h | h | h | h <;> injection h with h1 h2 <;> subst h1 <;> subst h2
    · exact k0excCheck_E6_false_2
    · exact k0excCheck_E6_true_2
    · exact k0excCheck_E7_2
    · exact k0excCheck_E8_2
    · exact k0excCheck_F4_2
private theorem k0excDatum_orbits_shapes (D : K0Diag) (s rho : List ℕ) (d n st : ℕ) :
    (k0Datum D s rho d n st).orbits =
      k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
        ((k0excShapes D s rho d).map fun x =>
          k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)) := by
  unfold k0Datum k0excShapes
  rw [List.map_map]
  rfl

private lemma k0excInsertBy_length {α : Type} (le : α → α → Bool) (a : α) (l : List α) :
    (k0InsertBy le a l).length = l.length + 1 := by
  induction l with
  | nil => rfl
  | cons b bs ih =>
      unfold k0InsertBy
      split
      · rfl
      · simp [ih]

private lemma k0excSortBy_length {α : Type} (le : α → α → Bool) (l : List α) :
    (k0SortBy le l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      unfold k0SortBy
      rw [k0excInsertBy_length, ih]
      simp

private theorem k0excShapes_eq_single {D : K0Diag} {s rho : List ℕ} {d n : ℕ} {o : GGKacOrbit}
    (h : (k0Datum D s rho d n 1).orbits = [o]) :
    ∃ x, k0excShapes D s rho d = [x] ∧
      o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n) := by
  have hsort : k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
      ((k0excShapes D s rho d).map fun x =>
        k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)) = [o] := by
    rw [← k0excDatum_orbits_shapes]
    exact h
  have hlen : ((k0excShapes D s rho d).map fun x =>
      k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).length = 1 := by
    have hp := k0excSortBy_length
      (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
      ((k0excShapes D s rho d).map fun x =>
        k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n))
    rw [hsort] at hp
    simpa using hp.symm
  have hlen' : (k0excShapes D s rho d).length = 1 := by simpa using hlen
  have hlen'' : ∃ x, k0excShapes D s rho d = [x] := by
    match hl : k0excShapes D s rho d with
    | [] => rw [hl] at hlen'; simp at hlen'
    | [x] => exact ⟨x, rfl⟩
    | x :: y :: ys => rw [hl] at hlen'; simp at hlen'
  obtain ⟨x, hx⟩ := hlen''
  refine ⟨x, hx, ?_⟩
  have hmap : (k0excShapes D s rho d).map (fun x =>
      k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)) =
      [k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)] := by rw [hx]; rfl
  rw [hmap] at hsort
  have hsingle :
      k0SortBy (fun a b => k0LexLtNat (k0OrbitKey a) (k0OrbitKey b))
        [k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)] =
        [k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)] := rfl
  rw [hsingle] at hsort
  have hfx : k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n) = o := by simpa using hsort
  exact hfx.symm

private lemma k0excBounds {lab : LargeEvenLabel} {p : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hgen : GGKacGeneric lab p) :
    lab.rank = 0 ∧ 2 ≤ lab.n := by
  obtain ⟨tag, rk, n⟩ := lab
  obtain ⟨hn1, hmat⟩ := hlab
  simp only [LargeEvenLabel.n] at hn1
  obtain ⟨hp, hp2, hbranch, htag, hF4, hE6, hE7⟩ := hgen
  simp only [LargeEvenLabel.n] at hbranch
  have hrank : rk = 0 := by
    rcases htag with h | h | h | h | h <;> rw [h] at hmat <;> simpa using hmat
  refine ⟨hrank, ?_⟩
  by_contra hlt
  simp only [LargeEvenLabel.n] at hlt
  have hn : n = 1 := by omega
  subst hn
  rw [show 2 ^ 1 - 1 = 1 by norm_num, show 2 ^ 1 + 1 = 3 by norm_num] at hbranch
  rcases hbranch with hb | hb
  · have hp1 : p = 1 := Nat.dvd_one.mp hb
    have hp2le : 2 ≤ p := hp.two_le
    omega
  · have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hb
    subst hp3
    rcases htag with h | h | h | h | h
    · rw [h] at hE6; exact hE6 ⟨Or.inl rfl, Or.inl rfl⟩
    · rw [h] at hE6; exact hE6 ⟨Or.inr rfl, Or.inl rfl⟩
    · rw [h] at hE7; exact hE7 ⟨Or.inl rfl, Or.inl rfl⟩
    · rw [h] at hE7; exact hE7 ⟨Or.inr rfl, Or.inl rfl⟩
    · rw [h] at hF4; exact hF4 ⟨rfl, rfl⟩

private structure K0ExcPat (lab : LargeEvenLabel) (p : ℕ) (D : GGKacDatum) where
  T : GGKacType
  tw : Bool
  d : ℕ
  hty : ggKacTypeOfLabel lab = some (T, tw)
  hpair : (T, tw) = (.E6, false) ∨ (T, tw) = (.E6, true) ∨ (T, tw) = (.E7, false) ∨
    (T, tw) = (.E8, false) ∨ (T, tw) = (.F4, false)
  hd12 : d = 1 ∨ d = 2
  hd1 : d = 1 → p ∣ 2 ^ lab.n - 1
  hd2 : d = 2 → p ∣ 2 ^ lab.n + 1
  s : List ℕ
  a : List ℕ
  hs : s ∈ ggKacSupports (k0DiagOf T).marks.length
  ha : a ∈ (k0DiagOf T).omega
  hact : k0pAct (k0pMul a (k0Rho0 (k0DiagOf T) tw d)) s = s
  hgcd : ggKacSupportGcd T (k0pMul a (k0Rho0 (k0DiagOf T) tw d)) s = 1
  hDat : (k0Datum (k0DiagOf T) s (k0pMul a (k0Rho0 (k0DiagOf T) tw d)) d lab.n 1).orbits =
    D.orbits
  hrZ : (k0Datum (k0DiagOf T) s (k0pMul a (k0Rho0 (k0DiagOf T) tw d)) d lab.n 1).rZ =
    D.rZ

private lemma k0excPatExists {lab : LargeEvenLabel} {p : ℕ} {D : GGKacDatum}
    (hgen : GGKacGeneric lab p) (hD : GGKacValid lab p D) :
    Nonempty (K0ExcPat lab p D) := by
  obtain ⟨tag, rk, n⟩ := lab
  obtain ⟨T, tw, hty, D', hmem, horb, hz⟩ :=
    exists_mem_ggKacPatternTable_of_ggKacValid hgen hD
  obtain ⟨hp, hp2, hbranch, htag, hF4, hE6, hE7⟩ := hgen
  simp only [LargeEvenLabel.n] at hbranch hF4 hE6 hE7
  let d : ℕ := if p ∣ 2 ^ n - 1 then 1 else 2
  have hd12 : d = 1 ∨ d = 2 := by
    by_cases h : p ∣ 2 ^ n - 1 <;> simp [d, h]
  have hd1 : d = 1 → p ∣ 2 ^ n - 1 := by
    intro hd
    by_contra h1
    have h : d = 2 := by simp [d, h1]
    omega
  have hd2 : d = 2 → p ∣ 2 ^ n + 1 := by
    intro hd
    by_cases h1 : p ∣ 2 ^ n - 1
    · have h : d = 1 := by simp [d, h1]
      omega
    · exact hbranch.resolve_left h1
  have hpair : (T, tw) = (.E6, false) ∨ (T, tw) = (.E6, true) ∨ (T, tw) = (.E7, false) ∨
      (T, tw) = (.E8, false) ∨ (T, tw) = (.F4, false) := by
    rcases htag with h | h | h | h | h
    · left; subst h; simp only [ggKacTypeOfLabel, Option.some.injEq] at hty; exact hty.symm
    · right; left; subst h; simp only [ggKacTypeOfLabel, Option.some.injEq] at hty; exact hty.symm
    · right; right; left; subst h
      simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
      exact hty.symm
    · right; right; right; left; subst h; simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
      exact hty.symm
    · right; right; right; right; subst h; simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
      exact hty.symm
  change D' ∈ ggKacPatternTable T tw d n at hmem
  rw [ggKacPatternTable] at hmem
  simp only [List.mem_flatMap, List.mem_filterMap, List.mem_map] at hmem
  obtain ⟨s, hs, rho, ⟨a, ha, rfl⟩, hif⟩ := hmem
  by_cases hc : k0pAct (k0pMul a (k0Rho0 (k0DiagOf T) tw d)) s = s ∧
      ggKacSupportGcd T (k0pMul a (k0Rho0 (k0DiagOf T) tw d)) s = 1
  · rw [if_pos hc] at hif
    injection hif with hEq
    exact ⟨⟨T, tw, d, hty, hpair, hd12, hd1, hd2, s, a, hs, ha, hc.1, hc.2,
      by rw [hEq]; exact horb, by rw [hEq]; exact hz⟩⟩
  · rw [if_neg hc] at hif
    exact absurd hif (by simp)

private lemma k0excShapeExists {lab : LargeEvenLabel} {p : ℕ} {D : GGKacDatum}
    (P : K0ExcPat lab p D) {o : GGKacOrbit}
    (horb : (k0Datum (k0DiagOf P.T) P.s
      (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d lab.n 1).orbits = [o])
    (hrZ : (k0Datum (k0DiagOf P.T) P.s
      (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d lab.n 1).rZ ≤ 1) :
    ∃ x, k0excShapes (k0DiagOf P.T) P.s
        (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d = [x] ∧
      o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n) ∧
      x ∈ k0excAllowed P.T P.tw P.d := by
  obtain ⟨x, hx, ho⟩ := k0excShapes_eq_single horb
  have hlen1 : (k0excShapes (k0DiagOf P.T) P.s
      (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d).length = 1 := by
    rw [hx]; simp
  have hxh : x ∈ k0excShapes (k0DiagOf P.T) P.s
      (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d := by
    rw [hx]; simp
  have hz : k0NumRhoOrbits (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d))
      ((List.range (k0DiagOf P.T).marks.length).filter
        (fun i => decide (P.s.getD i 0 > 0))) - 1 ≤ 1 := by
    have h : (k0Datum (k0DiagOf P.T) P.s
        (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d lab.n 1).rZ =
        k0NumRhoOrbits (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d))
          ((List.range (k0DiagOf P.T).marks.length).filter
            (fun i => decide (P.s.getD i 0 > 0))) - 1 := rfl
    rw [← h]; exact hrZ
  have hxmem : x ∈ k0excAllowed P.T P.tw P.d :=
    (k0excCheck P.T P.tw P.d P.hpair P.hd12) P.s P.hs P.a P.ha P.hact P.hgcd hz hlen1 x hxh
  exact ⟨x, hx, ho, hxmem⟩

private lemma k0excRow_E6_false_one {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .E6) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n - 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E6 false 1)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_E6_false_two {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .E6) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n + 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E6 false 2)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_E6_true_one {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .twE6) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n - 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E6 true 1)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_E6_true_two {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .twE6) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n + 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E6 true 2)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_E7_one {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .E7) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n - 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E7 false 1)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_E7_two {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .E7) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n + 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E7 false 2)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_E8_one {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .E8) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n - 1) (hp3 : p ≠ 3) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E8 false 1)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb, hp3]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_E8_two {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .E8) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n + 1) (hp3 : p ≠ 3) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .E8 false 2)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb, hp3]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_F4_one {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .F4) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n - 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .F4 false 1)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]
private lemma k0excRow_F4_two {lab : LargeEvenLabel} {p : ℕ}
    (htag : lab.tag = .F4) (hrank : lab.rank = 0) (hn : 2 ≤ lab.n)
    (hb : p ∣ 2 ^ lab.n + 1) {x : LargeEvenLieTag × ℕ × ℕ × ℕ}
    (hx : x ∈ k0excAllowed .F4 false 2)
    (hX : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ≠ lab) :
    LargeEvenInLambda2 (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab ∧
      GGTablePRow p (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n)).lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hb
  simp only [k0excAllowed, List.mem_cons, List.not_mem_nil, or_false, false_or] at hx
  rcases hx with rfl | rfl
  · simp only [k0LabelOf, Nat.one_mul]
    constructor
    · simp [LargeEvenInLambda2]; omega
    · unfold GGTablePRow
      simp [Nat.one_mul, hb]
  · exfalso
    apply hX
    simp [k0LabelOf]

private lemma k0excFinalE6 {lab : LargeEvenLabel} {p : ℕ} {T : GGKacType} {tw : Bool}
    {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ} {o : GGKacOrbit}
    (hrank : lab.rank = 0) (hn : 2 ≤ lab.n) (htag : lab.tag = .E6)
    (hty : ggKacTypeOfLabel lab = some (T, tw))
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → p ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → p ∣ 2 ^ lab.n + 1)
    (hxmem : x ∈ k0excAllowed T tw d)
    (ho : o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n))
    (hX : o.lab ≠ lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
  injection hty with hT htw
  subst hT; subst htw
  have hX' : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).lab ≠ ⟨.E6, 0, n⟩ := by
    rwa [← ho]
  rcases hd12 with hd | hd
  · rw [hd] at hxmem
    have hb := hd1 hd
    rw [ho]
    exact k0excRow_E6_false_one (lab := ⟨.E6, 0, n⟩) rfl rfl hn hb hxmem hX'
  · rw [hd] at hxmem
    have hb := hd2 hd
    rw [ho]
    exact k0excRow_E6_false_two (lab := ⟨.E6, 0, n⟩) rfl rfl hn hb hxmem hX'

private lemma k0excFinalTwE6 {lab : LargeEvenLabel} {p : ℕ} {T : GGKacType} {tw : Bool}
    {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ} {o : GGKacOrbit}
    (hrank : lab.rank = 0) (hn : 2 ≤ lab.n) (htag : lab.tag = .twE6)
    (hty : ggKacTypeOfLabel lab = some (T, tw))
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → p ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → p ∣ 2 ^ lab.n + 1)
    (hxmem : x ∈ k0excAllowed T tw d)
    (ho : o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n))
    (hX : o.lab ≠ lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
  injection hty with hT htw
  subst hT; subst htw
  have hX' : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).lab ≠ ⟨.twE6, 0, n⟩ := by
    rwa [← ho]
  rcases hd12 with hd | hd
  · rw [hd] at hxmem
    have hb := hd1 hd
    rw [ho]
    exact k0excRow_E6_true_one (lab := ⟨.twE6, 0, n⟩) rfl rfl hn hb hxmem hX'
  · rw [hd] at hxmem
    have hb := hd2 hd
    rw [ho]
    exact k0excRow_E6_true_two (lab := ⟨.twE6, 0, n⟩) rfl rfl hn hb hxmem hX'

private lemma k0excFinalE7 {lab : LargeEvenLabel} {p : ℕ} {T : GGKacType} {tw : Bool}
    {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ} {o : GGKacOrbit}
    (hrank : lab.rank = 0) (hn : 2 ≤ lab.n) (htag : lab.tag = .E7)
    (hty : ggKacTypeOfLabel lab = some (T, tw))
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → p ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → p ∣ 2 ^ lab.n + 1)
    (hxmem : x ∈ k0excAllowed T tw d)
    (ho : o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n))
    (hX : o.lab ≠ lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
  injection hty with hT htw
  subst hT; subst htw
  have hX' : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).lab ≠ ⟨.E7, 0, n⟩ := by
    rwa [← ho]
  rcases hd12 with hd | hd
  · rw [hd] at hxmem
    have hb := hd1 hd
    rw [ho]
    exact k0excRow_E7_one (lab := ⟨.E7, 0, n⟩) rfl rfl hn hb hxmem hX'
  · rw [hd] at hxmem
    have hb := hd2 hd
    rw [ho]
    exact k0excRow_E7_two (lab := ⟨.E7, 0, n⟩) rfl rfl hn hb hxmem hX'

private lemma k0excFinalE8 {lab : LargeEvenLabel} {p : ℕ} {T : GGKacType} {tw : Bool}
    {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ} {o : GGKacOrbit}
    (hrank : lab.rank = 0) (hn : 2 ≤ lab.n) (htag : lab.tag = .E8)
    (hty : ggKacTypeOfLabel lab = some (T, tw))
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → p ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → p ∣ 2 ^ lab.n + 1)
    (hp3 : p ≠ 3)
    (hxmem : x ∈ k0excAllowed T tw d)
    (ho : o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n))
    (hX : o.lab ≠ lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
  injection hty with hT htw
  subst hT; subst htw
  have hX' : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).lab ≠ ⟨.E8, 0, n⟩ := by
    rwa [← ho]
  rcases hd12 with hd | hd
  · rw [hd] at hxmem
    have hb := hd1 hd
    rw [ho]
    exact k0excRow_E8_one (lab := ⟨.E8, 0, n⟩) rfl rfl hn hb hp3 hxmem hX'
  · rw [hd] at hxmem
    have hb := hd2 hd
    rw [ho]
    exact k0excRow_E8_two (lab := ⟨.E8, 0, n⟩) rfl rfl hn hb hp3 hxmem hX'

private lemma k0excFinalF4 {lab : LargeEvenLabel} {p : ℕ} {T : GGKacType} {tw : Bool}
    {d : ℕ} {x : LargeEvenLieTag × ℕ × ℕ × ℕ} {o : GGKacOrbit}
    (hrank : lab.rank = 0) (hn : 2 ≤ lab.n) (htag : lab.tag = .F4)
    (hty : ggKacTypeOfLabel lab = some (T, tw))
    (hd12 : d = 1 ∨ d = 2)
    (hd1 : d = 1 → p ∣ 2 ^ lab.n - 1) (hd2 : d = 2 → p ∣ 2 ^ lab.n + 1)
    (hxmem : x ∈ k0excAllowed T tw d)
    (ho : o = k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * lab.n))
    (hX : o.lab ≠ lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab lab := by
  obtain ⟨tag, rk, n⟩ := lab
  simp only at htag hrank
  subst htag; subst hrank
  simp only [LargeEvenLabel.n] at hn hd1 hd2
  simp only [ggKacTypeOfLabel, Option.some.injEq] at hty
  injection hty with hT htw
  subst hT; subst htw
  have hX' : (k0LabelOf x.1 x.2.1 x.2.2.1 (x.2.2.2 * n)).lab ≠ ⟨.F4, 0, n⟩ := by
    rwa [← ho]
  rcases hd12 with hd | hd
  · rw [hd] at hxmem
    have hb := hd1 hd
    rw [ho]
    exact k0excRow_F4_one (lab := ⟨.F4, 0, n⟩) rfl rfl hn hb hxmem hX'
  · rw [hd] at hxmem
    have hb := hd2 hd
    rw [ho]
    exact k0excRow_F4_two (lab := ⟨.F4, 0, n⟩) rfl rfl hn hb hxmem hX'

theorem ggTablePRow_of_ggKacValid {lab : LargeEvenLabel} {p : ℕ}
    (hlab : LargeEvenInLambda2 lab) (hgen : GGKacGeneric lab p) {D : GGKacDatum}
    (hD : GGKacValid lab p D) (hrZ : D.rZ ≤ 1) {o : GGKacOrbit} (hDo : D.orbits = [o])
    (hX : o.lab ≠ lab) :
    LargeEvenInLambda2 o.lab ∧ GGTablePRow p o.lab lab := by
  obtain ⟨hrank, hn2⟩ := k0excBounds hlab hgen
  obtain ⟨P⟩ := k0excPatExists hgen hD
  obtain ⟨hp, hp2, hbranch, htag, hF4, hE6, hE7⟩ := hgen
  have horb : (k0Datum (k0DiagOf P.T) P.s
      (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d lab.n 1).orbits = [o] := by
    rw [P.hDat, hDo]
  have hrz : (k0Datum (k0DiagOf P.T) P.s
      (k0pMul P.a (k0Rho0 (k0DiagOf P.T) P.tw P.d)) P.d lab.n 1).rZ ≤ 1 := by
    rw [P.hrZ]
    exact hrZ
  obtain ⟨x, hx, ho, hxmem⟩ := k0excShapeExists P horb hrz
  rcases htag with htag | htag | htag | htag | htag
  · exact k0excFinalE6 hrank hn2 htag P.hty P.hd12 P.hd1 P.hd2 hxmem ho hX
  · exact k0excFinalTwE6 hrank hn2 htag P.hty P.hd12 P.hd1 P.hd2 hxmem ho hX
  · exact k0excFinalE7 hrank hn2 htag P.hty P.hd12 P.hd1 P.hd2 hxmem ho hX
  · have hp3 : p ≠ 3 := by
      intro h3
      exact hE7 ⟨Or.inr htag, Or.inl h3⟩
    exact k0excFinalE8 hrank hn2 htag P.hty P.hd12 P.hd1 P.hd2 hp3 hxmem ho hX
  · exact k0excFinalF4 hrank hn2 htag P.hty P.hd12 P.hd1 P.hd2 hxmem ho hX

end CFSG.StandardType

end
