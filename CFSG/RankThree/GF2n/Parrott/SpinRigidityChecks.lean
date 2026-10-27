module

public section

namespace CFSG.RankThree.GF2n.Parrott.SpinRigid

@[ext] structure B8 where
  c0 : Nat
  c1 : Nat
  c2 : Nat
  c3 : Nat
  c4 : Nat
  c5 : Nat
  c6 : Nat
  c7 : Nat
deriving DecidableEq

@[expose] def B8.col (c : B8) : Fin 8 → Nat
  | 0 => c.c0
  | 1 => c.c1
  | 2 => c.c2
  | 3 => c.c3
  | 4 => c.c4
  | 5 => c.c5
  | 6 => c.c6
  | 7 => c.c7

@[expose] def bapply (A : B8) (m : Nat) : Nat :=
  (if m.testBit 0 then A.c0 else 0) ^^^ (if m.testBit 1 then A.c1 else 0) ^^^
    (if m.testBit 2 then A.c2 else 0) ^^^ (if m.testBit 3 then A.c3 else 0) ^^^
    (if m.testBit 4 then A.c4 else 0) ^^^ (if m.testBit 5 then A.c5 else 0) ^^^
    (if m.testBit 6 then A.c6 else 0) ^^^ (if m.testBit 7 then A.c7 else 0)

@[expose] def bmul (A B : B8) : B8 :=
  ⟨bapply A B.c0, bapply A B.c1, bapply A B.c2, bapply A B.c3, bapply A B.c4, bapply A B.c5,
    bapply A B.c6, bapply A B.c7⟩

@[expose] def bone : B8 := ⟨1, 2, 4, 8, 16, 32, 64, 128⟩

@[expose] def bpow (A : B8) : Nat → B8
  | 0 => bone
  | n + 1 => bmul (bpow A n) A

@[expose] def evalB {n : Nat} (g : Fin n → B8) : List (Fin n × Nat) → B8
  | [] => bone
  | l :: w => bmul (bpow (g l.1) l.2) (evalB g w)

@[expose] def b3 : Fin 3 → B8
  | 0 => ⟨5, 24, 4, 18, 16, 36, 64, 128⟩
  | 1 => ⟨203, 173, 156, 130, 157, 235, 123, 171⟩
  | 2 => ⟨73, 2, 30, 8, 16, 120, 64, 192⟩

@[expose] def bnd (A : B8) : Bool :=
  decide (A.c0 < 256) && decide (A.c1 < 256) && decide (A.c2 < 256) && decide (A.c3 < 256) &&
    decide (A.c4 < 256) && decide (A.c5 < 256) && decide (A.c6 < 256) && decide (A.c7 < 256)

@[expose] def g5words : Fin 5 → List (Fin 3 × Nat)
  | 0 => [(0, 1)]
  | 1 => [(1, 1), (2, 1), (1, 4), (0, 1), (1, 4)]
  | 2 => [(1, 1), (0, 1), (1, 1), (2, 1), (1, 2), (2, 1), (1, 1), (0, 1), (1, 1), (0, 1), (1, 2)]
  | 3 => [(2, 1), (1, 4), (2, 1), (1, 3), (2, 1), (1, 2), (2, 1), (1, 1), (0, 1)]
  | 4 => [(1, 4), (0, 1), (1, 1), (0, 1)]

@[expose] def bN2 : B8 := evalB b3 (g5words 1)

@[expose] def bM1 : B8 := evalB b3 (g5words 2)

@[expose] def bM2 : B8 := evalB b3 (g5words 3)

@[expose] def bM3 : B8 := evalB b3 (g5words 4)

@[expose] def gb : Fin 5 → B8
  | 0 => b3 0
  | 1 => bN2
  | 2 => bM1
  | 3 => bM2
  | 4 => bM3

@[expose] def mTrip : Fin 8 → Nat × Nat × Nat
  | 0 => (0, 0, 0)
  | 1 => (0, 0, 1)
  | 2 => (0, 1, 0)
  | 3 => (1, 0, 0)
  | 4 => (0, 0, 2)
  | 5 => (0, 1, 1)
  | 6 => (0, 2, 0)
  | 7 => (1, 1, 0)

@[expose] def tcM (i : Fin 8) : B8 :=
  evalB gb [(2, (mTrip i).1), (3, (mTrip i).2.1), (4, (mTrip i).2.2)]

@[expose] def wcols (T : Fin 8 → B8) (w : Nat) : B8 :=
  ⟨bapply (T 0) w, bapply (T 1) w, bapply (T 2) w, bapply (T 3) w, bapply (T 4) w,
    bapply (T 5) w, bapply (T 6) w, bapply (T 7) w⟩

@[expose] def v0 : Nat := 7

@[expose] def b0inv : B8 := ⟨35, 6, 36, 156, 189, 236, 12, 31⟩

@[expose] def xc (w : Nat) : B8 := bmul (wcols tcM w) b0inv

theorem b0_inv : bmul (wcols tcM v0) b0inv = bone := by decide +kernel

theorem b0inv_bnd : bnd b0inv = true := by decide +kernel

@[expose] def sj : List B8 := [bM1, bM2, bM3]

@[expose] def okWit (w₀ : Nat) : Bool :=
  decide (bpow (xc w₀) 3 = bone) &&
    decide (bmul (xc w₀) bM1 = bmul bM1 (xc w₀)) &&
    decide (bmul (xc w₀) bM2 = bmul bM2 (xc w₀)) &&
    decide (bmul (xc w₀) bM3 = bmul bM3 (xc w₀))

@[expose] def wit1 : List (Nat × Nat) :=
  [(7, 7), (25, 19), (222, 68)]

@[expose] def stage1Ok (w : Nat) : Bool :=
  match wit1.lookup w with
  | none => false
  | some w₀ => okWit w₀ && decide (bmul (bmul (b3 0) (xc w)) (xc w₀) = bmul (xc w₀) (b3 0))

@[expose] def chk1 : Bool :=
  (List.range 256).all fun w =>
    !decide (bmul (bmul (b3 0) (xc w)) (bmul (b3 0) (xc w)) = bone) || stage1Ok w

theorem chk1_true : chk1 = true := by decide +kernel

@[expose] def rN : List (Fin 5 × Nat) := [(0, 1), (1, 3), (0, 1), (1, 3)]

@[expose] def gP (P : B8) : Fin 5 → B8
  | 0 => b3 0
  | 1 => P
  | 2 => bM1
  | 3 => bM2
  | 4 => bM3

@[expose] def wit3 : List (Nat × Nat) :=
  [(7, 7), (17, 164), (19, 174), (31, 150), (71, 184), (81, 81), (86, 86), (96, 220), (107, 105),
   (108, 91), (111, 46), (113, 71), (115, 114), (135, 77), (142, 178), (144, 100), (145, 27),
   (148, 214), (150, 233), (166, 17), (170, 99), (185, 135), (198, 56), (214, 163), (225, 156),
   (229, 145), (251, 13)]

@[expose] def stage3Ok (w : Nat) : Bool :=
  match wit3.lookup w with
  | none => false
  | some w₀ => okWit w₀ && decide (bmul (xc w₀) (b3 0) = bmul (b3 0) (xc w₀)) &&
      decide (bmul (bmul bN2 (xc w)) (xc w₀) = bmul (xc w₀) bN2)

@[expose] def chk3 : Bool :=
  (List.range 256).all fun w =>
    !decide (evalB (gP (bmul bN2 (xc w))) rN = bone) || stage3Ok w

theorem chk3_true : chk3 = true := by decide +kernel

@[expose] def st4 : Fin 8 → List (Fin 5 × Nat) × List (Fin 5 × Nat)
  | 0 => ([], [])
  | 1 => ([(4, 1), (0, 1)], [(0, 1)])
  | 2 => ([(1, 2), (4, 2), (1, 1)], [(3, 2), (2, 1), (1, 3)])
  | 3 => ([(1, 5), (2, 1)], [(4, 1), (3, 1), (0, 1), (1, 1), (0, 1)])
  | 4 => ([(2, 2), (1, 1)], [(4, 2), (2, 2), (0, 1), (1, 5), (0, 1)])
  | 5 => ([(2, 1), (1, 3), (0, 1)], [(3, 2), (2, 1), (1, 3), (0, 1)])
  | 6 => ([(4, 2), (3, 2), (1, 5), (0, 1)], [(4, 1), (3, 1), (0, 1), (1, 1)])
  | 7 => ([(1, 1), (3, 1), (2, 1), (0, 1)], [(4, 2), (2, 2), (0, 1), (1, 5)])

@[expose] def tlF (i : Fin 8) : B8 := evalB gb (st4 i).1

@[expose] def vL : Nat := 3

@[expose] def bLinv : B8 := ⟨25, 24, 10, 9, 253, 138, 161, 104⟩

@[expose] def yc (w : Nat) : B8 := bmul (wcols tlF w) bLinv

theorem bL_inv : bmul (wcols tlF vL) bLinv = bone := by decide +kernel

theorem bLinv_bnd : bnd bLinv = true := by decide +kernel

@[expose] def commL (w : Nat) : Bool :=
  (List.finRange 8).all fun i => decide (bmul (yc w) (tlF i) = bmul (tlF i) (yc w))

@[expose] def chk4 : Bool :=
  (List.range 256).all fun w =>
    !commL w || !decide (bpow (bmul (b3 0) (bmul (b3 1) (yc w))) 9 = bone) || decide (yc w = bone)

theorem chk4_true : chk4 = true := by decide +kernel

@[expose] def tcomp (a b : List Nat) : List Nat := b.map fun j => a.getD j 0

@[expose] def tone : List Nat := List.range 45

@[expose] def tpow (a : List Nat) : Nat → List Nat
  | 0 => tone
  | n + 1 => tcomp (tpow a n) a

@[expose] def evalT {n : Nat} (g : Fin n → List Nat) : List (Fin n × Nat) → List Nat
  | [] => tone
  | l :: w => tcomp (tpow (g l.1) l.2) (evalT g w)

@[expose] def tx : List Nat :=
  [0, 2, 1, 6, 7, 8, 3, 4, 5, 12, 13, 14, 9, 10, 11, 15, 16, 19, 22, 17, 20, 23, 18, 21, 24, 25,
   26, 29, 32, 27, 30, 33, 28, 31, 34, 35, 36, 39, 42, 37, 40, 43, 38, 41, 44]

@[expose] def ty : List Nat :=
  [38, 0, 42, 18, 32, 13, 28, 10, 22, 8, 33, 17, 31, 19, 5, 34, 11, 25, 4, 23, 7, 30, 26, 14, 21,
   35, 39, 44, 1, 41, 2, 36, 40, 37, 43, 16, 27, 20, 6, 9, 3, 15, 24, 29, 12]

@[expose] def tf : List Nat :=
  [0, 2, 1, 3, 5, 4, 6, 8, 7, 9, 11, 10, 12, 14, 13, 15, 16, 18, 17, 22, 24, 23, 19, 21, 20, 35,
   36, 38, 37, 42, 44, 43, 39, 41, 40, 25, 26, 28, 27, 32, 34, 33, 29, 31, 30]

@[expose] def t3 : Fin 3 → List Nat
  | 0 => tx
  | 1 => ty
  | 2 => tf

@[expose] def tN2 : List Nat := evalT t3 (g5words 1)

@[expose] def tM1 : List Nat := evalT t3 (g5words 2)

@[expose] def tM2 : List Nat := evalT t3 (g5words 3)

@[expose] def tM3 : List Nat := evalT t3 (g5words 4)

@[expose] def t5 : Fin 5 → List Nat
  | 0 => tx
  | 1 => tN2
  | 2 => tM1
  | 3 => tM2
  | 4 => tM3

theorem tab_x_sq : tcomp tx tx = tone := by decide +kernel

@[expose] def mWord (t : Nat × Nat × Nat) : List (Fin 5 × Nat) := [(2, t.1), (3, t.2.1), (4, t.2.2)]

@[expose] def normData : List (Fin 5 × Fin 5 × (Nat × Nat × Nat)) :=
  [(0, 2, (1, 0, 0)), (0, 3, (0, 1, 0)), (0, 4, (0, 0, 2)),
    (1, 2, (0, 2, 0)), (1, 3, (2, 2, 1)), (1, 4, (0, 1, 1))]

theorem tab_norm : ∀ p ∈ normData,
    tcomp (t5 p.1) (t5 p.2.1) = tcomp (evalT t5 (mWord p.2.2)) (t5 p.1) := by decide +kernel

theorem tab_rN : evalT t5 rN = tone := by decide +kernel

theorem tab_st4 : ∀ i : Fin 8,
    tcomp ty (evalT t5 (st4 i).1) = tcomp (evalT t5 (st4 i).2) ty := by decide +kernel

theorem tab_xy9 : tpow (tcomp tx ty) 9 = tone := by decide +kernel

theorem tab_f : tf = tcomp (tcomp (tcomp (tcomp (tpow ty 4) tN2) ty) tx) ty := by decide +kernel

theorem spec1 (w : Nat) (hw : w < 256)
    (h : bmul (bmul (b3 0) (xc w)) (bmul (b3 0) (xc w)) = bone) :
    ∃ w₀ : Nat, okWit w₀ = true ∧ bmul (bmul (b3 0) (xc w)) (xc w₀) = bmul (xc w₀) (b3 0) := by
  have h1 := List.all_eq_true.1 chk1_true w (List.mem_range.2 hw)
  simp only [h, decide_true, Bool.not_true, Bool.false_or] at h1
  unfold stage1Ok at h1
  cases hl : wit1.lookup w with
  | none => rw [hl] at h1; exact absurd h1 (by simp)
  | some w₀ =>
    rw [hl] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨w₀, h1.1, h1.2⟩

theorem spec3 (w : Nat) (hw : w < 256)
    (h : evalB (gP (bmul bN2 (xc w))) rN = bone) :
    ∃ w₀ : Nat, okWit w₀ = true ∧ bmul (xc w₀) (b3 0) = bmul (b3 0) (xc w₀) ∧
      bmul (bmul bN2 (xc w)) (xc w₀) = bmul (xc w₀) bN2 := by
  have h1 := List.all_eq_true.1 chk3_true w (List.mem_range.2 hw)
  simp only [h, decide_true, Bool.not_true, Bool.false_or] at h1
  unfold stage3Ok at h1
  cases hl : wit3.lookup w with
  | none => rw [hl] at h1; exact absurd h1 (by simp)
  | some w₀ =>
    rw [hl] at h1
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
    exact ⟨w₀, h1.1.1, h1.1.2, h1.2⟩

theorem spec4 (w : Nat) (hw : w < 256)
    (hc : ∀ i : Fin 8, bmul (yc w) (tlF i) = bmul (tlF i) (yc w))
    (h : bpow (bmul (b3 0) (bmul (b3 1) (yc w))) 9 = bone) : yc w = bone := by
  have h1 := List.all_eq_true.1 chk4_true w (List.mem_range.2 hw)
  have hc' : commL w = true := by
    unfold commL
    exact List.all_eq_true.2 fun i _ => decide_eq_true (hc i)
  simpa [hc', h] using h1

end CFSG.RankThree.GF2n.Parrott.SpinRigid
