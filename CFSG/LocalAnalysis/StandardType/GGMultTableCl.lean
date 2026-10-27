module

public import CFSG.LocalAnalysis.StandardType.GGKacTableCl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private local instance (priority := high) ggMultDecidableEqLargeEvenLabel : DecidableEq LargeEvenLabel :=
  fun a b =>
    match a, b with
    | ⟨ta, ra, na⟩, ⟨tb, rb, nb⟩ =>
      if h1 : ta = tb then
        if h2 : ra = rb then
          if h3 : na = nb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

private local instance (priority := high) ggMultDecidableEqGGKacOrbit : DecidableEq GGKacOrbit :=
  fun a b =>
    match a, b with
    | ⟨la, qa⟩, ⟨lb, qb⟩ =>
      if h1 : la = lb then
        if h2 : qa = qb then isTrue (by cases h1; cases h2; rfl)
        else isFalse (by intro h; injection h with _ h2'; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _; exact h1 h1')

private local instance (priority := high) ggMultDecidableEqGGKacDatum : DecidableEq GGKacDatum :=
  fun a b =>
    match a, b with
    | ⟨oa, za, sa⟩, ⟨ob, zb, sb⟩ =>
      if h1 : oa = ob then
        if h2 : za = zb then
          if h3 : sa = sb then isTrue (by cases h1; cases h2; cases h3; rfl)
          else isFalse (by intro h; injection h with _ _ h3'; exact h3 h3')
        else isFalse (by intro h; injection h with _ h2' _; exact h2 h2')
      else isFalse (by intro h; injection h with h1' _ _; exact h1 h1')

@[expose] def ggMultVecs : ℕ → ℕ → List (List ℕ)
  | 0, t => if t = 0 then [[]] else []
  | k + 1, t =>
      (List.range (t + 1)).flatMap (fun first =>
        (ggMultVecs k (t - first)).map (fun rest => first :: rest))

theorem mem_ggMultVecs {k t : ℕ} {m : List ℕ} :
    m ∈ ggMultVecs k t ↔ m.length = k ∧ m.sum = t := by
  induction k generalizing t m with
  | zero =>
      by_cases ht : t = 0
      · subst ht
        rw [ggMultVecs, if_pos rfl]
        constructor
        · intro h
          rw [List.mem_singleton] at h
          subst h
          simp
        · rintro ⟨hlen, hsum⟩
          rw [List.length_eq_zero_iff] at hlen
          rw [hlen]
          simp
      · rw [ggMultVecs, if_neg ht]
        constructor
        · intro h
          exact False.elim ((List.mem_nil_iff m).mp h)
        · rintro ⟨hlen, hsum⟩
          rw [List.length_eq_zero_iff] at hlen
          rw [hlen] at hsum
          simp only [List.sum_nil] at hsum
          exact absurd hsum.symm ht
  | succ k ih =>
      simp only [ggMultVecs, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨first, hfirst, rest, hrest, rfl⟩
        obtain ⟨hlen, hsum⟩ := ih.mp hrest
        refine ⟨?_, ?_⟩
        · simp [hlen]
        · rw [List.sum_cons, hsum]
          omega
      · rintro ⟨hlen, hsum⟩
        cases m with
        | nil => simp at hlen
        | cons first rest =>
          have hlen' : rest.length = k := by simpa [List.length_cons] using hlen
          have hsum' : first + rest.sum = t := by simpa [List.sum_cons] using hsum
          refine ⟨first, by omega, rest, ih.mpr ⟨hlen', ?_⟩, rfl⟩
          omega

@[expose] def ggMultOrd (p n : ℕ) : ℕ :=
  if p ∣ 2 ^ n - 1 then 1 else if p ∣ 2 ^ n + 1 then 2 else 0

@[expose] def ggMultBlockA (r nf d : ℕ) : GGKacOrbit :=
  if d = 1 then ⟨⟨.A, r, nf⟩, decide (¬ (r = 1 ∧ nf = 1))⟩
  else if 2 ≤ r then ⟨⟨.twA, r, nf⟩, decide (¬ (r = 2 ∧ nf = 1))⟩
  else ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩

@[expose] def ggMultEps0 (p d : ℕ) (tw : Bool) (m : List ℕ) : Bool :=
  ((List.range ((p - 1) / 2)).map (fun j => j + 1)).foldl
    (fun eps j => if d = 2 ∧ m.getD j 0 % 2 = 1 then !eps else eps) (!tw)

@[expose] def ggMultV0 (m0 : ℕ) (plus : Bool) (nf : ℕ) : List GGKacOrbit :=
  if m0 ≤ 1 then []
  else if m0 = 2 then
    if plus then [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩, ⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩]
    else [⟨⟨.A, 1, 2 * nf⟩, true⟩]
  else if m0 = 3 then
    if plus then [⟨⟨.A, 3, nf⟩, true⟩] else [⟨⟨.twA, 3, nf⟩, true⟩]
  else
    if plus then [⟨⟨.D, m0, nf⟩, true⟩] else [⟨⟨.twD, m0, nf⟩, true⟩]

@[expose] def ggMultDatumC (p nf d : ℕ) (m : List ℕ) : GGKacDatum :=
  let H := (p - 1) / 2
  let m0 := m.headD 0
  let orb0 : List GGKacOrbit :=
    if m0 = 1 then [⟨⟨.A, 1, nf⟩, decide (¬ (nf = 1))⟩]
    else if m0 = 2 ∧ nf = 1 then [⟨⟨.B2der, 0, 1⟩, true⟩]
    else if 2 ≤ m0 then [⟨⟨.C, m0, nf⟩, true⟩]
    else []
  let orbJ : List GGKacOrbit :=
    ((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
      (fun j => ggMultBlockA (m.getD j 0 - 1) nf d)
  let rZ : ℕ := ((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length
  ⟨orb0 ++ orbJ, rZ, 1⟩

@[expose] def ggMultDatumD (p nf d : ℕ) (tw : Bool) (m : List ℕ) : GGKacDatum :=
  let H := (p - 1) / 2
  let m0 := m.headD 0
  let eps0 := ggMultEps0 p d tw m
  let orb0 := ggMultV0 m0 eps0 nf
  let orbJ : List GGKacOrbit :=
    ((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
      (fun j => ggMultBlockA (m.getD j 0 - 1) nf d)
  let rZ : ℕ := ((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length
  let rZ := if m0 = 1 ∧ ((eps0 = true ∧ d = 1) ∨ (eps0 = false ∧ d = 2)) then rZ + 1 else rZ
  ⟨orb0 ++ orbJ, rZ, 1⟩

@[expose] def ggMultDatumDList (p nf d : ℕ) (tw : Bool) (m : List ℕ) : List GGKacDatum :=
  if m.headD 0 = 0 then
    (if ggMultEps0 p d tw m = true then
      [ggMultDatumD p nf d tw m, ggMultDatumD p nf d tw m] else [])
  else [ggMultDatumD p nf d tw m]

@[expose] def ggMultAllEq (m : List ℕ) : Bool :=
  match m with
  | [] => false
  | x :: xs => xs.all (fun y => decide (y = x))

@[expose] def ggMultSymm (p : ℕ) (m : List ℕ) : Bool :=
  (List.range p).all (fun j => decide (m.getD ((p - j) % p) 0 = m.getD j 0))

@[expose] def ggMultAdmA (p d : ℕ) (tw : Bool) (m : List ℕ) : Bool :=
  decide ((tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2) ∨ ggMultSymm p m = true)

@[expose] def ggMultDatumA (p nf d : ℕ) (tw : Bool) (m : List ℕ) : GGKacDatum :=
  let H := (p - 1) / 2
  let trivial := (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2)
  let stab : ℕ := if ggMultAllEq m then p else 1
  if trivial then
    let orbs : List GGKacOrbit :=
      ((List.range p).filter (fun j => decide (2 ≤ m.getD j 0))).map
        (fun j => ggMultBlockA (m.getD j 0 - 1) nf d)
    let rZ : ℕ := ((List.range p).filter (fun j => decide (0 < m.getD j 0))).length - 1
    ⟨orbs, rZ, stab⟩
  else
    let orb0 : List GGKacOrbit :=
      if 2 ≤ m.headD 0 then
        let r := m.headD 0 - 1
        if tw = false then [⟨⟨.A, r, nf⟩, decide (¬ (r = 1 ∧ nf = 1))⟩]
        else [ggMultBlockA r nf 2]
      else []
    let orbJ : List GGKacOrbit :=
      ((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 2 ≤ m.getD j 0))).map
        (fun j => ⟨⟨.A, m.getD j 0 - 1, 2 * nf⟩, true⟩)
    let t : ℕ := ((List.range (H + 1)).filter (fun j => decide (1 ≤ j ∧ 0 < m.getD j 0))).length
    ⟨orb0 ++ orbJ, t, stab⟩

@[expose] def ggMultTableCl (T : GGKacTypeCl) (tw : Bool) (p n : ℕ) : List GGKacDatum :=
  match T with
  | .C r =>
      if ggMultOrd p n = 0 then []
      else (ggMultVecs ((p - 1) / 2 + 1) r).map (fun m => ggMultDatumC p n (ggMultOrd p n) m)
  | .D r =>
      if ggMultOrd p n = 0 then []
      else (ggMultVecs ((p - 1) / 2 + 1) r).flatMap (ggMultDatumDList p n (ggMultOrd p n) tw)
  | .A r =>
      if ggMultOrd p n = 0 then []
      else
        ((ggMultVecs p (r + 1)).filter (fun m => ggMultAdmA p (ggMultOrd p n) tw m)).map
          (fun m => ggMultDatumA p n (ggMultOrd p n) tw m)

@[expose] def GGMultValidCl (lab : LargeEvenLabel) (p : ℕ) (D : GGKacDatum) : Prop :=
  ∃ T tw m, ggKacTypeClOfLabel lab = some (T, tw, m) ∧ D ∈ ggMultTableCl T tw p m

theorem ggMultSymm_eq_true {p : ℕ} {m : List ℕ} :
    ggMultSymm p m = true ↔ ∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0 := by
  simp only [ggMultSymm, List.all_eq_true, List.mem_range]
  constructor
  · intro h j hj; simpa using h j hj
  · intro h j hj; simpa using h j hj

theorem ggMultAdmA_eq_true {p d : ℕ} {tw : Bool} {m : List ℕ} :
    ggMultAdmA p d tw m = true ↔
      (tw = false ∧ d = 1) ∨ (tw = true ∧ d = 2) ∨
        ∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0 := by
  rw [ggMultAdmA, decide_eq_true_eq, ggMultSymm_eq_true]

theorem ggMultDatumDList_mem {p nf d : ℕ} {tw : Bool} {m : List ℕ} {D : GGKacDatum} :
    D ∈ ggMultDatumDList p nf d tw m ↔
      (m.headD 0 = 0 → ggMultEps0 p d tw m = true) ∧ D = ggMultDatumD p nf d tw m := by
  rw [ggMultDatumDList]
  rw [List.headD_eq_head?_getD]
  by_cases h0 : m.head?.getD 0 = 0
  · by_cases he : ggMultEps0 p d tw m = true
    · simp [h0, he]
    · have hef : ggMultEps0 p d tw m = false := by
        cases hv : ggMultEps0 p d tw m <;> simp_all
      simp [h0, hef]
  · simp [h0]

theorem mem_ggMultTableCl_C {r p n : ℕ} {D : GGKacDatum} (hd : ggMultOrd p n ≠ 0) :
    D ∈ ggMultTableCl (.C r) false p n ↔
      ∃ m : List ℕ, m.length = (p - 1) / 2 + 1 ∧ m.sum = r ∧
        D = ggMultDatumC p n (ggMultOrd p n) m := by
  simp only [ggMultTableCl, if_neg hd, List.mem_map]
  constructor
  · rintro ⟨m, hm, hmD⟩
    obtain ⟨hlen, hsum⟩ := mem_ggMultVecs.mp hm
    exact ⟨m, hlen, hsum, hmD.symm⟩
  · rintro ⟨m, hlen, hsum, hD⟩
    exact ⟨m, mem_ggMultVecs.mpr ⟨hlen, hsum⟩, hD.symm⟩

theorem mem_ggMultTableCl_D {r p n : ℕ} {tw : Bool} {D : GGKacDatum} (hd : ggMultOrd p n ≠ 0) :
    D ∈ ggMultTableCl (.D r) tw p n ↔
      ∃ m : List ℕ, m.length = (p - 1) / 2 + 1 ∧ m.sum = r ∧
        (m.headD 0 = 0 → ggMultEps0 p (ggMultOrd p n) tw m = true) ∧
        D = ggMultDatumD p n (ggMultOrd p n) tw m := by
  simp only [ggMultTableCl, if_neg hd, List.mem_flatMap]
  constructor
  · rintro ⟨m, hm, hDm⟩
    obtain ⟨hlen, hsum⟩ := mem_ggMultVecs.mp hm
    obtain ⟨hadm, hD⟩ := (ggMultDatumDList_mem (p := p) (nf := n) (d := ggMultOrd p n)
      (tw := tw) (m := m) (D := D)).mp hDm
    exact ⟨m, hlen, hsum, hadm, hD⟩
  · rintro ⟨m, hlen, hsum, hadm, hD⟩
    exact ⟨m, mem_ggMultVecs.mpr ⟨hlen, hsum⟩,
      (ggMultDatumDList_mem (p := p) (nf := n) (d := ggMultOrd p n) (tw := tw)
        (m := m) (D := D)).mpr ⟨hadm, hD⟩⟩

theorem mem_ggMultTableCl_A {r p n : ℕ} {tw : Bool} {D : GGKacDatum} (hd : ggMultOrd p n ≠ 0) :
    D ∈ ggMultTableCl (.A r) tw p n ↔
      ∃ m : List ℕ, m.length = p ∧ m.sum = r + 1 ∧
        ((tw = false ∧ ggMultOrd p n = 1) ∨ (tw = true ∧ ggMultOrd p n = 2) ∨
          ∀ j, j < p → m.getD ((p - j) % p) 0 = m.getD j 0) ∧
        D = ggMultDatumA p n (ggMultOrd p n) tw m := by
  simp only [ggMultTableCl, if_neg hd, List.mem_map, List.mem_filter]
  constructor
  · rintro ⟨m, ⟨hm, hQ⟩, hmD⟩
    obtain ⟨hlen, hsum⟩ := mem_ggMultVecs.mp hm
    exact ⟨m, hlen, hsum, (ggMultAdmA_eq_true.mp hQ), hmD.symm⟩
  · rintro ⟨m, hlen, hsum, hQ, hD⟩
    exact ⟨m, ⟨mem_ggMultVecs.mpr ⟨hlen, hsum⟩, ggMultAdmA_eq_true.mpr hQ⟩, hD.symm⟩

private def ggMultCanonTable (l : List GGKacDatum) : List GGKacDatum :=
  List.dedup (k1SortDatums (l.map (fun D =>
    { D with orbits := k1SortBy (fun a b => k1LexLtNat (k1OrbitKey a) (k1OrbitKey b)) D.orbits })))

example : ggMultDatumC 3 1 2 [1, 1] = ⟨[⟨⟨.A, 1, 1⟩, false⟩], 1, 1⟩ := by decide
example : ggMultDatumD 3 1 2 false [3, 1] = ⟨[⟨⟨.twA, 3, 1⟩, true⟩], 1, 1⟩ := by decide
example : ggMultDatumA 3 1 2 false [3, 0, 0] = ⟨[⟨⟨.A, 2, 1⟩, true⟩], 0, 1⟩ := by decide

example : ggMultCanonTable (ggMultTableCl (.C 2) false 3 1) =
    ggMultCanonTable (ggKacTableCl (.C 2) false 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.C 2) false 5 2) =
    ggMultCanonTable (ggKacTableCl (.C 2) false 5 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.C 3) false 3 1) =
    ggMultCanonTable (ggKacTableCl (.C 3) false 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.C 3) false 3 2) =
    ggMultCanonTable (ggKacTableCl (.C 3) false 3 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.C 3) false 5 2) =
    ggMultCanonTable (ggKacTableCl (.C 3) false 5 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.C 4) false 5 2) =
    ggMultCanonTable (ggKacTableCl (.C 4) false 5 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.C 4) false 3 4) =
    ggMultCanonTable (ggKacTableCl (.C 4) false 3 4) := by decide

example : ggMultCanonTable (ggMultTableCl (.D 4) false 3 1) =
    ggMultCanonTable (ggKacTableCl (.D 4) false 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.D 4) true 3 1) =
    ggMultCanonTable (ggKacTableCl (.D 4) true 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.D 4) false 5 2) =
    ggMultCanonTable (ggKacTableCl (.D 4) false 5 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.D 5) true 5 2) =
    ggMultCanonTable (ggKacTableCl (.D 5) true 5 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.D 5) false 3 2) =
    ggMultCanonTable (ggKacTableCl (.D 5) false 3 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.D 5) true 3 1) =
    ggMultCanonTable (ggKacTableCl (.D 5) true 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.A 2) false 3 1) =
    ggMultCanonTable (ggKacTableCl (.A 2) false 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.A 2) true 3 2) =
    ggMultCanonTable (ggKacTableCl (.A 2) true 3 2) := by decide

example : ggMultCanonTable (ggMultTableCl (.A 3) false 3 1) =
    ggMultCanonTable (ggKacTableCl (.A 3) false 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.A 3) true 3 1) =
    ggMultCanonTable (ggKacTableCl (.A 3) true 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.A 3) false 5 4) =
    ggMultCanonTable (ggKacTableCl (.A 3) false 5 4) := by decide +kernel

example : ggMultCanonTable (ggMultTableCl (.A 5) false 3 1) =
    ggMultCanonTable (ggKacTableCl (.A 5) false 3 1) := by decide

example : ggMultCanonTable (ggMultTableCl (.A 4) true 3 4) =
    ggMultCanonTable (ggKacTableCl (.A 4) true 3 4) := by decide

example : ggMultCanonTable (ggMultTableCl (.A 4) false 3 3) =
    ggMultCanonTable (ggKacTableCl (.A 4) false 3 3) := by decide

end CFSG.StandardType

end
