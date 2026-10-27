module

public import CFSG.Quasithin.Background.HFCodeInputs
public import CFSG.Quasithin.Background.HParabBase

public section

namespace CFSG.Quasithin.H.LU24

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Parab CFSG.QuasithinUnique.Setup.X1

@[expose] def uSMasks : List ℕ :=
  [0, 41, 256, 297, 592, 633, 848, 889, 1099, 1122, 1355, 1378, 1563, 1586, 1819, 1842]

@[expose] def uSBasis : List ℕ := [41, 256, 592, 1099]

@[expose] def uTBasis' : List ℕ := [39, 219, 1108]

@[expose] def predKS (l : List T24s2.Elem) : Bool :=
  l.length != 6 || (codeFixMasks24 l).length != 16 || codeFixMasks24 l == uSMasks

@[expose] def codColsA : List ℕ := [636, 1056, 912, 648, 260, 1302, 391, 1548, 896, 1164, 1300]

@[expose] def codColsB : List ℕ := [798, 252, 1146, 1, 2031, 190, 1118, 1983, 350, 574, 2015]

@[expose] def cocColsA : List ℕ := [64, 96, 1777, 649, 1061, 3, 1, 844, 1396, 397, 1698]

@[expose] def cocColsB : List ℕ := [118, 10, 12, 2047, 24, 1908, 1010, 706, 1672, 1416, 1316]

@[expose] def orbRound (cs : List (List ℕ)) (i : ℕ) :
    Array (List ℕ) × Std.HashSet ℕ × Array (ℕ × ℕ) → ℕ →
      Array (List ℕ) × Std.HashSet ℕ × Array (ℕ × ℕ)
  | (bs, seen, st), g =>
    let b := (bs.getD i []).map (actM (cs.getD g []))
    let k := maskKey b
    if seen.contains k then (bs, seen, st) else (bs.push b, seen.insert k, st.push (g, i))

@[expose] def orbBFS (cs : List (List ℕ)) :
    ℕ → ℕ → Array (List ℕ) × Std.HashSet ℕ × Array (ℕ × ℕ) → Array (ℕ × ℕ)
  | 0, _, s => s.2.2
  | fuel + 1, i, s =>
    if i < s.1.size then orbBFS cs fuel (i + 1) ((List.range cs.length).foldl (orbRound cs i) s)
    else s.2.2

@[expose] def orbSteps (cs : List (List ℕ)) (d : List ℕ) (N : ℕ) : List (ℕ × ℕ) :=
  (orbBFS cs (N + 1) 0 (#[d], (∅ : Std.HashSet ℕ).insert (maskKey d), #[])).toList

@[expose] def orbCheck (n : ℕ) (cs : List (List ℕ)) (d : List ℕ) (N : ℕ) : Bool :=
  let st := orbSteps cs d N
  let bs := orbBases cs d [d] st
  (st.all fun e => decide (e.1 < cs.length)) &&
    (bs.all fun b => b.all fun x => decide (x < 2 ^ n)) &&
    decide (bs.map maskKey).Nodup && bs.length == N

theorem orbCheck_spec {n : ℕ} {cs : List (List ℕ)} {d : List ℕ} {N : ℕ}
    (h : orbCheck n cs d N = true) :
    (∀ e ∈ orbSteps cs d N, e.1 < cs.length) ∧
      (∀ b ∈ orbBases cs d [d] (orbSteps cs d N), ∀ x ∈ b, x < 2 ^ n) ∧
      ((orbBases cs d [d] (orbSteps cs d N)).map maskKey).Nodup ∧
      (orbBases cs d [d] (orbSteps cs d N)).length = N := by
  simp only [orbCheck, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  exact ⟨h1, h2, h3, h4⟩

end CFSG.Quasithin.H.LU24
