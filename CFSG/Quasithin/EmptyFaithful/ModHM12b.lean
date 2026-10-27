module

public import CFSG.Quasithin.EmptyFaithful.ModHS12
public import CFSG.Quasithin.EmptyFaithful.ModHM12a

public section

namespace CFSG.Quasithin.ModH.R12

open CFSG.Quasithin.ModG CFSG.Quasithin.ModH.S12

@[expose] def rW : List (List ℕ) :=
  [[1, 0, 3, 0, 3, 0],
    [1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0],
    [0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0],
    [0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3],
    [0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 1, 0],
    [0, 3, 0, 1, 0, 3, 0, 3, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0],
    [3, 0, 3, 0, 1, 0, 3, 0, 3, 0, 3],
    [1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1],
    [0, 1, 0, 1, 0],
    [1, 0, 1, 0, 3, 0, 3, 0, 1, 0, 3, 0, 3, 0],
    [1, 0, 3, 0, 1, 0, 3, 0, 1, 0, 1, 0],
    [3, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0],
    [3, 0, 1, 0, 1, 0, 3, 0, 1, 0, 3, 0, 1, 0],
    [0, 3, 0, 1, 0, 1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3],
    [1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3],
    [1, 0, 3, 0, 1, 0, 3, 0, 3, 0, 1, 0, 1, 0, 1, 0],
    [1, 0],
    [1, 0, 1, 0, 3, 0, 1, 0, 1, 0, 3, 0, 3, 0, 3, 0],
    []]

@[expose] def cW : List (List ℕ) :=
  [[],
    [0, 1, 0, 3, 0, 3, 0, 1, 0, 3],
    [1, 0, 3, 0, 1, 0, 1, 0, 3, 0]]

@[expose] def Om : List (List Bool) :=
  [[true, true, true, true, false, false, false, false, false, false, false, false],
    [true, true, true, false, false, true, false, false, false, false, false, false],
    [true, true, true, false, false, false, true, false, false, false, false, false],
    [true, true, true, false, false, false, false, true, false, false, false, false],
    [true, true, true, false, false, false, false, false, true, false, false, false],
    [true, true, true, false, false, false, false, false, false, false, true, false],
    [true, true, true, false, false, false, false, false, false, false, false, true],
    [true, true, false, false, true, true, false, false, false, false, false, false],
    [true, true, false, false, true, false, true, false, false, false, false, false],
    [true, true, false, false, true, false, false, false, false, false, false, true],
    [true, true, false, false, false, true, true, false, false, false, false, false],
    [true, true, false, false, false, true, false, false, false, false, false, true],
    [true, true, false, false, false, false, true, false, true, false, false, false],
    [true, false, true, true, true, false, false, false, false, false, false, false],
    [true, false, true, true, false, true, false, false, false, false, false, false],
    [true, false, true, true, false, false, false, false, false, true, false, false],
    [true, false, true, false, false, true, false, false, false, true, false, false],
    [true, false, false, false, true, true, false, true, false, false, false, false],
    [false, true, false, false, false, false, true, false, true, false, false, true]]

@[expose] def B0l : List Bool := [false, true, false, false, false, false, true, false, true, false, false, true]

@[expose] def witW : List (ℕ × ℕ × List ℕ × List ℕ) :=
  [(0, 0, [5, 3, 7, 6], [2, 7, 3, 6, 5, 3, 0]),
    (0, 1, [2, 2, 6, 1], [4, 2, 3]),
    (0, 2, [0], [7, 6, 2, 7]),
    (1, 0, [1, 5, 5], [0, 3, 6, 1]),
    (1, 1, [6, 2, 5, 6], [5, 5, 2, 4, 2, 7]),
    (1, 2, [1], [7, 7, 5, 6]),
    (2, 0, [0], [7, 6]),
    (2, 1, [0, 4, 0], [1, 3, 0, 7]),
    (2, 2, [2, 1, 5, 2, 4], [3, 0, 5, 0, 1, 1]),
    (3, 0, [4], [7, 5, 5, 2, 3, 5]),
    (3, 1, [4], [1, 5, 7, 5, 3, 2]),
    (3, 2, [4], [6, 3, 6, 7]),
    (4, 0, [6, 2, 5], [4, 7, 2, 4, 3, 5, 0]),
    (4, 1, [1], [0, 6, 3, 4, 7, 2]),
    (4, 2, [6, 6, 2, 5], [5, 4, 2, 7, 7, 7]),
    (5, 0, [4], [4, 2, 3, 5, 3, 6]),
    (5, 1, [1, 6], [4, 0, 6, 3, 3, 4, 5]),
    (5, 2, [5], [4, 7, 2, 5, 7]),
    (6, 0, [1], [2, 0, 1, 2, 7, 6]),
    (6, 1, [0], [7, 0, 4, 2]),
    (6, 2, [2, 2], [3]),
    (7, 0, [7, 5, 6, 2, 1, 3, 0], [6, 0, 1, 0, 3]),
    (7, 1, [0], [5, 0, 3, 6, 1, 6, 4]),
    (7, 2, [5], [7, 2, 2, 3, 5, 3, 2]),
    (8, 0, [2, 3, 1, 6, 3, 1, 0], [4, 3, 3, 7, 1]),
    (8, 1, [5, 6], [3, 5, 0, 1, 3]),
    (8, 2, [4, 3, 5, 5, 7], [7]),
    (9, 0, [1, 6, 4, 4], [3, 2, 4, 6, 3, 4]),
    (9, 1, [3, 4, 7], [2, 3]),
    (9, 2, [1, 0, 1, 4], [0, 7, 5, 7]),
    (10, 0, [0], [0, 0, 2, 1, 7, 2]),
    (10, 1, [2, 2, 1, 1, 4, 0], [6, 1, 2, 7, 0]),
    (10, 2, [5, 1, 2, 2], [1, 0, 6, 0, 7]),
    (11, 0, [5, 2, 6, 2, 6], [4, 0, 5, 7, 7, 5, 4]),
    (11, 1, [0, 5, 0, 2, 6], [2, 7, 0, 0, 7]),
    (11, 2, [4], [7, 7, 4, 6, 2]),
    (12, 0, [1], [4, 4, 4, 3, 6]),
    (12, 1, [4], [7, 5, 0, 6, 0]),
    (12, 2, [4], [7, 7]),
    (13, 0, [4, 2, 3, 4, 5], [7, 6, 2, 5, 0, 5, 4]),
    (13, 1, [6, 3, 3, 6, 7, 1], [7, 4, 2, 3, 4, 5, 0]),
    (13, 2, [7, 5, 6, 1, 3, 5, 2], [3, 7, 3, 0, 1]),
    (14, 0, [4, 6, 6, 4], [4, 6, 7, 5, 7, 1]),
    (14, 1, [4], [7, 7, 3, 7]),
    (14, 2, [0, 5, 0], [6, 4, 2, 3, 5, 3]),
    (15, 0, [1], [4, 5, 7, 7, 4]),
    (15, 1, [2, 6, 5], [4, 3, 5, 7, 7, 6, 1]),
    (15, 2, [4, 0, 5], [6, 2, 3, 3, 6, 1, 1]),
    (16, 0, [5], [4, 5, 3, 3, 3, 7, 0]),
    (16, 1, [2, 1, 6], [5, 0, 3, 5, 5, 0]),
    (16, 2, [5], [4, 3, 5, 0, 3, 5]),
    (17, 1, [4, 4, 4, 3, 0, 7, 4], [7, 0, 3, 6, 1, 0]),
    (17, 2, [3, 7, 1, 6, 2], [7, 0, 7, 0, 7, 2, 7])]

@[expose] def rC : List ℕ := rW.map (evcg (compn 12) (kIdn 12) aC)

@[expose] def cC : List ℕ := cW.map (evcg (compn 12) (kIdn 12) aC)

@[expose] def Uim : List ℕ := Om.flatMap fun o => tK.map fun s => bn (actL s o)

@[expose] def chk1B : Bool := allL (fun l => !(Nat.beq (popL l) 4) || memB (bn l) Uim) (allBools 12)

theorem chk1B_true : chk1B = true := by decide +kernel

theorem chk1 : ∀ l ∈ allBools 12, popL l = 4 → memB (bn l) Uim = true := by
  intro l hl hp
  have h := allL_iff.1 chk1B_true l hl
  simp only [hp, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h with h | h
  · exact absurd h (by decide)
  · exact h

theorem chk2 : ∀ k < 19, actL (rC.getD k 0) B0l = Om.getD k [] := by decide +kernel

theorem chk3 : ∀ g ∈ gC, actL g B0l = B0l := by decide +kernel

theorem chk4a : ∀ i < 3, actL (cC.getD i 0) B0l = B0l := by decide +kernel

theorem chk4b : memB (cC.getD 1 0) tK = false ∧ memB (cC.getD 2 0) tK = false ∧
    memB (compn 12 (evcg (compn 12) (kIdn 12) aC (invW 2 (cW.getD 1 []))) (cC.getD 2 0)) tK = false := by
  decide +kernel

@[expose] def Lcodes (k i : ℕ) : List ℕ :=
  let w := rW.getD k [] ++ cW.getD i []
  gC ++ [evcg (compn 12) (kIdn 12) aC w] ++ (gW.map fun v => evcg (compn 12) (kIdn 12) aC (invW 2 v)) ++
    [evcg (compn 12) (kIdn 12) aC (invW 2 w)]

@[expose] def witChk (lc : List ℕ) (wa wb : List ℕ) : Bool :=
  let ca := evcg (compn 12) (kIdn 12) lc wa
  let cb := evcg (compn 12) (kIdn 12) lc wb
  let cab := compn 12 ca cb
  Nat.beq (compn 12 ca ca) (kIdn 12) && Nat.beq (compn 12 (compn 12 cb cb) cb) (kIdn 12) &&
    Nat.beq (compn 12 (compn 12 (compn 12 cab cab) (compn 12 cab cab)) cab) (kIdn 12) && !(Nat.beq cb (kIdn 12))

theorem chk5 : ∀ k < 19, ∀ i < 3, k = 18 ∨ (k = 17 ∧ i = 0) ∨
    ∃ e ∈ witW, e.1 = k ∧ e.2.1 = i ∧ witChk (Lcodes k i) e.2.2.1 e.2.2.2 = true ∧
      (∀ l ∈ e.2.2.1 ++ e.2.2.2, l < 8) := by decide +kernel

@[expose] def trA : List (List ℕ) := [[], gW.getD 2 []]

theorem chk6 : ∀ s ∈ tK, ∃ w ∈ trA,
    memB (compn 12 (evcg (compn 12) (kIdn 12) aC (invW 2 (rW.getD 17 [])))
      (compn 12 (evcg (compn 12) (kIdn 12) aC (invW 2 w)) (compn 12 s (rC.getD 17 0)))) tK = true := by
  decide +kernel

theorem chk7 : ∀ w ∈ rW ++ cW ++ gW, ∀ l ∈ w, l < 4 := by decide +kernel

theorem chk8 : rW.length = 19 ∧ Om.length = 19 ∧ cW.length = 3 := by decide +kernel

end CFSG.Quasithin.ModH.R12
