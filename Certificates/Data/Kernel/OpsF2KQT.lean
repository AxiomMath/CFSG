module

public import Certificates.Data.Kernel.OpsF2KQ
public import Certificates.Data.Kernel.OpsF2KMcert

public section

namespace CFSG.KC.OpsF2K

open CFSG.KC.M1F2 CFSG.KLie.CT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native
open CFSG.KC.Misc.G24 (mulF2)

inductive RT where
  | leaf (v : Nat)
  | node (l r : RT)

@[expose] def tget (h : Nat) : RT → Nat → Nat :=
  Nat.rec (motive := fun _ => RT → Nat → Nat)
    (fun t _ => RT.casesOn (motive := fun _ => Nat) t (fun v => v) (fun _ _ => 0))
    (fun _ ih t i => RT.casesOn (motive := fun _ => Nat) t (fun v => v)
      (fun l r => cond (Nat.beq (i % 2) 0) (ih l (i / 2)) (ih r (i / 2)))) h

@[expose] def tset (h : Nat) : RT → Nat → Nat → RT :=
  Nat.rec (motive := fun _ => RT → Nat → Nat → RT)
    (fun _ _ x => RT.leaf x)
    (fun _ ih t i x => RT.casesOn (motive := fun _ => RT) t
      (fun v => cond (Nat.beq (i % 2) 0) (RT.node (ih (RT.leaf v) (i / 2) x) (RT.leaf v))
        (RT.node (RT.leaf v) (ih (RT.leaf v) (i / 2) x)))
      (fun l r => cond (Nat.beq (i % 2) 0) (RT.node (ih l (i / 2) x) r)
        (RT.node l (ih r (i / 2) x)))) h

@[expose] noncomputable def gT (d n h : Nat) (T : RT) (i : Nat) : Nat :=
  cond (Nat.blt i n) (tget h T i) (idF d)

@[expose] noncomputable def stepTG (d n h : Nat) (M P : Nat → Nat → Nat) (T : RT) : Op → RT
  | .mul i j k => cond (Nat.blt k n) (tset h T k (M (gT d n h T i) (gT d n h T j))) T
  | .pow e i k => cond (Nat.blt k n) (tset h T k (P (gT d n h T i) e)) T

@[expose] noncomputable def runTG (d A B n h : Nat) (M P : Nat → Nat → Nat) (prog : List Op) : RT :=
  prog.foldl (stepTG d n h M P) (tset h (tset h (RT.leaf (idF d)) 0 A) 1 B)

@[expose] noncomputable def runT (d A B n h : Nat) (prog : List Op) : RT :=
  runTG d A B n h (mulF2 d) (fun X e => pqK d X e) prog

@[expose] noncomputable def runTK (d A B n h : Nat) (prog : List Op) : RT :=
  runTG d A B n h (mulF d) (fun X e => powK d X e) prog

@[expose] noncomputable def w4QT (h d A B : Nat) (D : Data) (inv : Nat) : Bool :=
  let T := runT d A B D.nregs h D.prog
  let G := gT d D.nregs h T
  let xs := D.outs.map G
  seedsOK d A B && D.prog.all expOK && decide (2 ≤ D.nregs) && D.prog.all (Op.lt D.nregs) &&
    D.outs.all (decide <| · < D.nregs) && decide (inv < D.nregs) &&
    D.tests.all (decide <| · < d) &&
    xs.all (fun X => Nat.beq (mulF2 d (mulF2 d X X) X) (idF d)) && commsQ d xs &&
    ((List.range (3 ^ xs.length - 1)).all fun n =>
      D.tests.any fun k => !Nat.beq (appBaseK d 3 xs (n + 1) (pw2 k)) (pw2 k)) &&
    Nat.beq (mulF2 d (G inv) (G inv)) (idF d) &&
    D.tests.any (fun k => !Nat.beq (vmF d (G inv) (pw2 k)) (pw2 k)) &&
    D.outs.all (fun r => commQ d (G r) (G inv))

theorem tget_leaf : ∀ (h v i : Nat), tget h (RT.leaf v) i = v
  | 0, _, _ => rfl
  | _ + 1, _, _ => rfl

theorem tget_succ_node (h : Nat) (l r : RT) (i : Nat) :
    tget (h + 1) (RT.node l r) i = cond (Nat.beq (i % 2) 0) (tget h l (i / 2)) (tget h r (i / 2)) :=
  rfl

theorem tset_succ (h : Nat) (t : RT) (i x : Nat) :
    tset (h + 1) t i x = RT.casesOn (motive := fun _ => RT) t
      (fun v => cond (Nat.beq (i % 2) 0) (RT.node (tset h (RT.leaf v) (i / 2) x) (RT.leaf v))
        (RT.node (RT.leaf v) (tset h (RT.leaf v) (i / 2) x)))
      (fun l r => cond (Nat.beq (i % 2) 0) (RT.node (tset h l (i / 2) x) r)
        (RT.node l (tset h r (i / 2) x))) :=
  rfl

theorem eq_iff_mod_div {i k : Nat} : i = k ↔ i % 2 = k % 2 ∧ i / 2 = k / 2 := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← Nat.mod_add_div i 2, ← Nat.mod_add_div k 2, h1, h2]

theorem tget_tset : ∀ (h : Nat) (t : RT) (k i x : Nat), k < 2 ^ h → i < 2 ^ h →
    tget h (tset h t k x) i = if i = k then x else tget h t i
  | 0, t, k, i, x, hk, hi => by
    have hk0 : k = 0 := by simpa using hk
    have hi0 : i = 0 := by simpa using hi
    subst hk0 hi0
    rfl
  | h + 1, t, k, i, x, hk, hi => by
    have hk' : k / 2 < 2 ^ h := by rw [Nat.pow_succ] at hk; omega
    have hi' : i / 2 < 2 ^ h := by rw [Nat.pow_succ] at hi; omega
    have IH := fun t => tget_tset h t (k / 2) (i / 2) x hk' hi'
    have hkm : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
    have him : i % 2 = 0 ∨ i % 2 = 1 := Nat.mod_two_eq_zero_or_one i
    have b0 : Nat.beq 0 0 = true := rfl
    have b1 : Nat.beq 1 0 = false := rfl
    cases t with
    | leaf v =>
      rw [tset_succ, tget_leaf]
      rcases hkm with hk2 | hk2 <;> rcases him with hi2 | hi2 <;>
        simp only [hk2, hi2, b0, b1, Bool.cond_true, Bool.cond_false, tget_succ_node, IH,
          tget_leaf] <;>
        simp [eq_iff_mod_div (i := i) (k := k), hk2, hi2]
    | node l r =>
      rw [tset_succ, tget_succ_node]
      rcases hkm with hk2 | hk2 <;> rcases him with hi2 | hi2 <;>
        simp only [hk2, hi2, b0, b1, Bool.cond_true, Bool.cond_false, tget_succ_node, IH] <;>
        simp [eq_iff_mod_div (i := i) (k := k), hk2, hi2]

def Agree (d n h : Nat) (R : List Nat) (T : RT) : Prop :=
  R.length = n ∧ getR d R = gT d n h T

theorem getR_set (d : Nat) (R : List Nat) (k x i : Nat) (hk : k < R.length) :
    getR d (R.set k x) i = if i = k then x else getR d R i := by
  unfold getR
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hik : i = k
  · subst hik; simp [hk]
  · simp [hik, Ne.symm hik]

theorem agree_set {d n h : Nat} {R : List Nat} {T : RT} (hn : n ≤ 2 ^ h) (H : Agree d n h R T)
    (k x : Nat) :
    Agree d n h (R.set k x) (cond (Nat.blt k n) (tset h T k x) T) := by
  obtain ⟨hl, hg⟩ := H
  by_cases hk : k < n
  · have hb : Nat.blt k n = true := Nat.blt_eq.mpr hk
    rw [hb, Bool.cond_true]
    refine ⟨by rw [List.length_set, hl], funext fun i => ?_⟩
    rw [getR_set d R k x i (by omega), hg]
    unfold gT
    by_cases hi : i < n
    · have hbi : Nat.blt i n = true := Nat.blt_eq.mpr hi
      rw [hbi, Bool.cond_true, Bool.cond_true, tget_tset h T k i x (by omega) (by omega)]
    · have hbi : Nat.blt i n = false := by
        rw [Bool.eq_false_iff]; intro h'; exact hi (Nat.blt_eq.mp h')
      have hik : i ≠ k := by omega
      rw [hbi, if_neg hik, Bool.cond_false, Bool.cond_false]
  · have hb : Nat.blt k n = false := by
      rw [Bool.eq_false_iff]; intro h'; exact hk (Nat.blt_eq.mp h')
    rw [hb, Bool.cond_false]
    refine ⟨by rw [List.length_set, hl], ?_⟩
    rw [List.set_eq_of_length_le (by omega)]
    exact hg

theorem agree_step {d n h : Nat} (hn : n ≤ 2 ^ h) {M P : Nat → Nat → Nat}
    {st : List Nat → Op → List Nat}
    (hm : ∀ R i j k, st R (.mul i j k) = R.set k (M (getR d R i) (getR d R j)))
    (hp : ∀ R e i k, st R (.pow e i k) = R.set k (P (getR d R i) e)) :
    ∀ {R : List Nat} {T : RT} (op : Op),
    Agree d n h R T → Agree d n h (st R op) (stepTG d n h M P T op)
  | R, T, .mul i j k, H => by
    have hg := H.2
    rw [hm]
    unfold stepTG
    rw [hg]
    exact agree_set hn ⟨H.1, hg⟩ k _
  | R, T, .pow e i k, H => by
    have hg := H.2
    rw [hp]
    unfold stepTG
    rw [hg]
    exact agree_set hn ⟨H.1, hg⟩ k _

theorem agree_foldl {d n h : Nat} (hn : n ≤ 2 ^ h) {M P : Nat → Nat → Nat}
    {st : List Nat → Op → List Nat}
    (hm : ∀ R i j k, st R (.mul i j k) = R.set k (M (getR d R i) (getR d R j)))
    (hp : ∀ R e i k, st R (.pow e i k) = R.set k (P (getR d R i) e)) :
    ∀ (prog : List Op) {R : List Nat} {T : RT},
    Agree d n h R T → Agree d n h (prog.foldl st R) (prog.foldl (stepTG d n h M P) T)
  | [], _, _, H => H
  | op :: prog, _, _, H => agree_foldl hn hm hp prog (agree_step hn hm hp op H)

theorem agree_init (d A B n h : Nat) (hn : n ≤ 2 ^ h) (h1 : 1 ≤ h) :
    Agree d n h ((List.range n).map fun r => if r = 0 then A else if r = 1 then B else idF d)
      (tset h (tset h (RT.leaf (idF d)) 0 A) 1 B) := by
  have h2 : 2 ≤ 2 ^ h := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ h := Nat.pow_le_pow_right (by decide) h1
  refine ⟨by simp, funext fun i => ?_⟩
  unfold getR gT
  by_cases hi : i < n
  · have hbi : Nat.blt i n = true := Nat.blt_eq.mpr hi
    rw [hbi, Bool.cond_true, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi,
      Option.map_some, Option.getD_some, tget_tset h _ 1 i B (by omega) (by omega),
      tget_tset h _ 0 i A (by omega) (by omega), tget_leaf]
    by_cases h0 : i = 0
    · subst h0; simp
    · by_cases h1' : i = 1
      · subst h1'; simp
      · simp [h0, h1']
  · have hbi : Nat.blt i n = false := by
      rw [Bool.eq_false_iff]; intro h'; exact hi (Nat.blt_eq.mp h')
    rw [hbi, Bool.cond_false, List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
    rfl

theorem getR_runQ (d A B n h : Nat) (prog : List Op) (hn : n ≤ 2 ^ h) (h1 : 1 ≤ h) :
    getR d (runQ d A B n prog) = gT d n h (runT d A B n h prog) :=
  (agree_foldl hn (st := stepQ d) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) prog
    (agree_init d A B n h hn h1)).2

theorem getR_runK (d A B n h : Nat) (prog : List Op) (hn : n ≤ 2 ^ h) (h1 : 1 ≤ h) :
    getR d (runK d A B n prog) = gT d n h (runTK d A B n h prog) :=
  (agree_foldl hn (st := stepK d) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) prog
    (agree_init d A B n h hn h1)).2

theorem w4Q_eq_T (h d A B : Nat) (D : Data) (inv : Nat) (hn : D.nregs ≤ 2 ^ h) (h1 : 1 ≤ h) :
    w4Q d A B D inv = w4QT h d A B D inv := by
  simp only [w4Q, w4QT]
  rw [getR_runQ d A B D.nregs h D.prog hn h1]

@[expose] noncomputable def evalWT (d : Nat) (G : Nat → Nat) : Word → Nat
  | [] => idF d
  | (r, e) :: w => mulF d (powK d (G r) e) (evalWT d G w)

@[expose] noncomputable def factKT (d : Nat) (G : Nat → Nat) (n : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) && decide (e < 65536) &&
      Nat.beq (powK d (G r) e) (idF d)
  | .conj h u w => decide (h < n) && wordLtK n u && wordLtK n w &&
      Nat.beq (mulF d (G h) (evalWT d G u)) (mulF d (evalWT d G w) (G h))
  | .ne w₁ w₂ t => wordLtK n w₁ && wordLtK n w₂ && decide (t < d) &&
      !Nat.beq (vmF d (evalWT d G w₁) (pw2 t)) (vmF d (evalWT d G w₂) (pw2 t))
  | .eq w₁ w₂ => wordLtK n w₁ && wordLtK n w₂ && Nat.beq (evalWT d G w₁) (evalWT d G w₂)

@[expose] noncomputable def fusKT (h d A B nregs : Nat) (prog : List Op)
    (D : CFSG.RankThree.PartOne.CTP.Fus.Spec) : Bool :=
  let G := gT d nregs h (runTK d A B nregs h prog)
  seedsOK d A B && prog.all expOK && decide (2 ≤ nregs) && prog.all (Op.lt nregs) &&
    D.facts.all (factKT d G nregs) && decide (D.rA < nregs) && decide (D.rB < nregs) &&
    Nat.beq (G D.rA) A && Nat.beq (G D.rB) B && D.wf

theorem evalWK_eq (d : Nat) (R : List Nat) : ∀ w : Word, evalWK d R w = evalWT d (getR d R) w
  | [] => rfl
  | (r, e) :: w => by
    simp only [evalWK, evalWT, evalWK_eq d R w]

theorem factK_eq (d : Nat) (R : List Nat) (n : Nat) : factK d R n = factKT d (getR d R) n := by
  funext f
  cases f <;> simp only [factK, factKT, evalWK_eq]

theorem fusK_eq_T (h d A B nregs : Nat) (prog : List Op) (D : CFSG.RankThree.PartOne.CTP.Fus.Spec)
    (hn : nregs ≤ 2 ^ h) (h1 : 1 ≤ h) :
    fusK d A B nregs prog D = fusKT h d A B nregs prog D := by
  simp only [fusK, mcertK, fusKT, factK_eq]
  rw [getR_runK d A B nregs h prog hn h1]

end CFSG.KC.OpsF2K

end
