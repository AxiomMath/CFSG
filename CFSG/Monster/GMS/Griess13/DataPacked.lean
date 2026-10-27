module

public import CFSG.Monster.GMS.Griess13.Data
public import CFSG.Sporadic.HS.SmallF2Spec
public meta import CFSG.Monster.GMS.Griess13.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import Certificates.Certificate3024
public meta import CFSG.Sporadic.Co1Base
public import CFSG.Sporadic.Co1Base
public meta import CFSG.Sporadic.Th.F2Spec
public import CFSG.Sporadic.Th.F2Spec

public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open CFSG.Sporadic.SmallF2 (rowsMatrix rowsMatrix_mulRows rowsMatrix_idRows rowsMatrix_apply
  toVecD toVecD_apply)
open CFSG.Sporadic.SmallF2.Native (mulRows idRows)

structure PR where
  r : Array ℕ
  s : Array ℕ

namespace PR

@[expose] def one : PR := ⟨idRows 24, idRows 24⟩

@[expose] def mul
    (a b : PR) : PR := ⟨mulRows 24 a.r b.r, mulRows 24 b.s a.s⟩

@[expose] def inv (a : PR) : PR := ⟨a.s, a.r⟩

@[expose] def pow (a : PR) : ℕ → PR
  | 0 => one
  | n + 1 => (pow a n).mul a

@[expose] def zpow
    (a : PR) (e : ℤ) : PR := if 0 ≤ e then a.pow e.toNat else a.inv.pow (-e).toNat

@[expose] def Is
    (a : PR) (g : G) : Prop := rowsMatrix 24 a.r = mat g ∧ rowsMatrix 24 a.s = mat g⁻¹

theorem Is.one : Is one 1 :=
  ⟨rowsMatrix_idRows 24, by rw [inv_one, mat_one]; exact rowsMatrix_idRows 24⟩

theorem Is.mul
    {a b : PR} {g h : G} (ha : Is a g) (hb : Is b h) : Is (a.mul b) (g * h) := by
  refine ⟨?_, ?_⟩
  · rw [PR.mul, rowsMatrix_mulRows, ha.1, hb.1, mat_mul]
  · rw [PR.mul, rowsMatrix_mulRows, ha.2, hb.2, mul_inv_rev, mat_mul]

theorem Is.inv {a : PR} {g : G} (ha : Is a g) : Is a.inv g⁻¹ :=
  ⟨ha.2, by rw [inv_inv]; exact ha.1⟩

theorem Is.pow
    {a : PR} {g : G} (ha : Is a g) (n : ℕ) : Is (a.pow n) (g ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact Is.one
  | succ n ih => rw [pow_succ]; exact ih.mul ha

theorem Is.zpow
    {a : PR} {g : G} (ha : Is a g) (e : ℤ) : Is (a.zpow e) (g ^ e) := by
  unfold PR.zpow
  split_ifs with h
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h
    rw [Int.toNat_natCast, zpow_natCast]
    exact ha.pow n
  · obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ -e)
    rw [hn, Int.toNat_natCast, show e = -(n : ℤ) by omega, zpow_neg, zpow_natCast, ← inv_pow]
    exact ha.inv.pow n

@[expose] def conj (a b : PR) : PR := (a.mul b).mul a.inv

theorem Is.conj {a b : PR} {g h : G} (ha : Is a g) (hb : Is b h) :
    Is (a.conj b) (g * h * g⁻¹) := (ha.mul hb).mul ha.inv

end PR

@[expose] def eqRows (X Y : Array ℕ) : Bool :=
  (List.range 24).all fun i => (X[i]?.getD 0) % 2 ^ 24 == (Y[i]?.getD 0) % 2 ^ 24

theorem eqRows_iff {X Y : Array ℕ} : eqRows X Y = true ↔ rowsMatrix 24 X = rowsMatrix 24 Y := by
  unfold eqRows
  rw [List.all_eq_true]
  constructor
  · intro h
    ext i j
    rw [rowsMatrix_apply, rowsMatrix_apply, toVecD_apply, toVecD_apply]
    have hi := h i.val (List.mem_range.2 i.isLt)
    rw [beq_iff_eq] at hi
    have := congrArg (fun z => z.testBit j.val) hi
    simp only [Nat.testBit_mod_two_pow, j.isLt, decide_true, Bool.true_and] at this
    rw [this]
  · intro h i hi
    rw [beq_iff_eq]
    refine Nat.eq_of_testBit_eq fun j => ?_
    rw [Nat.testBit_mod_two_pow, Nat.testBit_mod_two_pow]
    by_cases hj : j < 24
    · have := congrFun (congrFun h ⟨i, List.mem_range.1 hi⟩) ⟨j, hj⟩
      rw [rowsMatrix_apply, rowsMatrix_apply, toVecD_apply, toVecD_apply] at this
      simp only [hj, decide_true, Bool.true_and]
      cases hx : (X[i]?.getD 0).testBit j <;> cases hy : (Y[i]?.getD 0).testBit j <;>
        simp_all
    · simp [hj]

namespace PR

@[expose] def eq (a b : PR) : Bool := eqRows a.r b.r

theorem Is.eq_of
    {a b : PR} {g h : G} (ha : Is a g) (hb : Is b h) (e : eq a b = true) : g = h :=
  mat_injective (by rw [← ha.1, ← hb.1]; exact eqRows_iff.1 e)

theorem Is.ne_of
    {a b : PR} {g h : G} (ha : Is a g) (hb : Is b h) (e : eq a b = false) :
    g ≠ h := by
  rintro rfl
  have : eq a b = true := eqRows_iff.2 (by rw [ha.1, hb.1])
  rw [this] at e
  exact Bool.noConfusion e

end PR

@[expose] def letterPR (gens : List PR) (l : ℤ) : PR :=
  if 0 < l then gens.getD (l.toNat - 1) PR.one else (gens.getD ((-l).toNat - 1) PR.one).inv

@[expose] def wordPR (gens : List PR) (w : List ℤ) : PR :=
  w.foldl (fun acc l => acc.mul (letterPR gens l)) PR.one

theorem forall₂_getD
    {l : List PR} {m : List G} (h : List.Forall₂ PR.Is l m) (i : ℕ) :
    PR.Is (l.getD i PR.one) (m.getD i 1) := by
  induction h generalizing i with
  | nil => simpa using PR.Is.one
  | cons hab _ ih =>
    cases i with
    | zero => simpa using hab
    | succ i => simpa using ih i

theorem is_letterPR
    {gens : List PR} {gensG : List G} (h : List.Forall₂ PR.Is gens gensG) (l : ℤ) :
    PR.Is (letterPR gens l) (letterVal gensG l) := by
  unfold letterPR letterVal
  split_ifs
  · exact forall₂_getD h _
  · exact (forall₂_getD h _).inv

theorem is_foldl_word
    {gens : List PR} {gensG : List G} (h : List.Forall₂ PR.Is gens gensG)
    (w : List ℤ) : ∀ (acc : PR) (g : G), PR.Is acc g →
      PR.Is (w.foldl (fun a l => a.mul (letterPR gens l)) acc)
        (w.foldl (fun a l => a * letterVal gensG l) g) := by
  induction w with
  | nil => intro acc g hg; exact hg
  | cons l w ih =>
    intro acc g hg
    have h1 := hg.mul (is_letterPR h l)
    have h2 := ih _ _ h1
    simp only [List.foldl_cons]
    exact h2

theorem is_wordPR
    {gens : List PR} {gensG : List G} (h : List.Forall₂ PR.Is gens gensG)
    (w : List ℤ) : PR.Is (wordPR gens w) (evalWord gensG w) :=
  is_foldl_word h w PR.one 1 PR.Is.one

namespace SLP

@[expose] def lookupPR : List (ℕ × PR) → ℕ → PR
  | [], _ => PR.one
  | (k, v) :: l, i => if i = k then v else lookupPR l i

@[expose] def initRegsAux : List PR → ℕ → List (ℕ × PR)
  | [], _ => []
  | x :: l, j => (j, x) :: initRegsAux l (j + 1)

@[expose] def stepPR
    (R : List (ℕ × PR)) (l : ℕ × List (ℕ × ℤ)) : List (ℕ × PR) :=
  (l.1, l.2.foldl (fun acc f => acc.mul ((lookupPR R f.1).zpow f.2)) PR.one) :: R

@[expose] def regsPR (p : SLP) (inputs : List PR) : List (ℕ × PR) :=
  p.lines.foldl stepPR (initRegsAux inputs 1)

@[expose] def evalPR (p : SLP) (inputs : List PR) : List PR :=
  p.outs.map fun f => (lookupPR (p.regsPR inputs) f.1).zpow f.2

theorem is_lookup_init
    {l : List PR} {m : List G} (h : List.Forall₂ PR.Is l m) (j : ℕ) (i : ℕ) :
    PR.Is (lookupPR (initRegsAux l j) i) (if j ≤ i then m.getD (i - j) 1 else 1) := by
  induction h generalizing j with
  | nil => simpa [initRegsAux, lookupPR] using (PR.Is.one)
  | cons hab _ ih =>
    rename_i x y xs ys
    simp only [initRegsAux, lookupPR]
    by_cases hij : i = j
    · subst hij
      simpa using hab
    · have := ih (j + 1)
      by_cases hlt : j < i
      · have h1 : j ≤ i := hlt.le
        have h2 : j + 1 ≤ i := hlt
        have h3 : i - j = (i - (j + 1)) + 1 := by omega
        simp only [hij, h1, h2, h3, ↓reduceIte, List.getD_cons_succ] at this ⊢
        exact this
      · have h1 : ¬ j ≤ i := by omega
        have h2 : ¬ j + 1 ≤ i := by omega
        simp only [hij, h1, h2, ↓reduceIte] at this ⊢
        exact this

theorem is_lookup_step
    {R : List (ℕ × PR)} {RG : ℕ → G} (h : ∀ i, PR.Is (lookupPR R i) (RG i))
    (l : ℕ × List (ℕ × ℤ)) : ∀ i, PR.Is (lookupPR (stepPR R l) i) (step RG l i) := by
  have key : ∀ (fs : List (ℕ × ℤ)) (acc : PR) (g : G), PR.Is acc g →
      PR.Is (fs.foldl (fun acc f => acc.mul ((lookupPR R f.1).zpow f.2)) acc)
        (fs.foldl (fun acc f => acc * RG f.1 ^ f.2) g) := by
    intro fs
    induction fs with
    | nil => intro acc g hg; exact hg
    | cons f fs ih =>
      intro acc g hg
      have h1 := hg.mul ((h f.1).zpow f.2)
      have h2 := ih _ _ h1
      simp only [List.foldl_cons]
      exact h2
  intro i
  unfold stepPR step
  by_cases hi : i = l.1
  · subst hi
    rw [Function.update_self]
    simp only [lookupPR, ↓reduceIte]
    exact key _ _ _ PR.Is.one
  · rw [Function.update_of_ne hi]
    simp only [lookupPR, hi, ↓reduceIte]
    exact h i

theorem is_regsPR (p : SLP) {inputs : List PR} {inputsG : List G}
    (h : List.Forall₂ PR.Is inputs inputsG) :
    ∀ i, PR.Is (lookupPR (p.regsPR inputs) i) (p.regs inputsG i) := by
  have key : ∀ (ls : List (ℕ × List (ℕ × ℤ))) (R : List (ℕ × PR)) (RG : ℕ → G),
      (∀ i, PR.Is (lookupPR R i) (RG i)) →
      ∀ i, PR.Is (lookupPR (ls.foldl stepPR R) i) (ls.foldl step RG i) := by
    intro ls
    induction ls with
    | nil => intro R RG hR; exact hR
    | cons l ls ih =>
      intro R RG hR
      have h1 := is_lookup_step hR l
      have h2 := ih _ _ h1
      simp only [List.foldl_cons]
      exact h2
  refine key p.lines _ _ ?_
  intro i
  have := is_lookup_init h 1 i
  unfold init
  exact this

theorem is_evalPR (p : SLP) {inputs : List PR} {inputsG : List G}
    (h : List.Forall₂ PR.Is inputs inputsG) :
    List.Forall₂ PR.Is (p.evalPR inputs) (p.eval inputsG) := by
  unfold evalPR eval
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  exact List.forall₂_same.2 fun f _ => (is_regsPR p h f.1).zpow f.2

end SLP

theorem is_foldr_mul
    {l : List PR} {m : List G} (h : List.Forall₂ PR.Is l m) :
    PR.Is (l.foldr PR.mul PR.one) m.prod := by
  induction h with
  | nil => exact PR.Is.one
  | cons hab _ ih => exact hab.mul ih

theorem forall₂_ofFn
    {n : ℕ} {f : Fin n → PR} {g : Fin n → G} (h : ∀ i, PR.Is (f i) (g i)) :
    List.Forall₂ PR.Is (List.ofFn f) (List.ofFn g) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ]
    exact List.Forall₂.cons (h 0) (ih fun i => h i.succ)

@[expose] def prA : PR := ⟨dat.rowsA, dat.rowsA⟩

@[expose] def prB : PR := ⟨dat.rowsB, mulRows 24 dat.rowsB dat.rowsB⟩

theorem is_prA : PR.Is prA genA := by
  have h1 : rowsMatrix 24 dat.rowsA = mat genA := rowsMatrix_rowsA_eq.trans mat_genA.symm
  have hinv : genA⁻¹ = genA := inv_eq_of_mul_eq_one_right genA_mul_self
  exact ⟨h1, h1.trans (congrArg mat hinv).symm⟩

theorem is_prB : PR.Is prB genB := by
  have h1 : rowsMatrix 24 dat.rowsB = mat genB := rowsMatrix_rowsB_eq.trans mat_genB.symm
  have h3 : genB * (genB * genB) = 1 := by
    rw [← pow_two, ← pow_succ']; exact genB_pow_three
  have hinv : genB⁻¹ = genB * genB := inv_eq_of_mul_eq_one_right h3
  refine ⟨h1, ?_⟩
  have h2 : rowsMatrix 24 (mulRows 24 dat.rowsB dat.rowsB) = mat (genB * genB) := by
    rw [rowsMatrix_mulRows, h1, mat_mul]
  exact h2.trans (congrArg mat hinv).symm

theorem forall₂_AB : List.Forall₂ PR.Is [prA, prB] [genA, genB] :=
  List.Forall₂.cons is_prA (List.Forall₂.cons is_prB List.Forall₂.nil)

@[expose] def prNout
    : List PR := (parseSLP slpMax11).evalPR [prA, prB]

theorem forall₂_nout :
    List.Forall₂ PR.Is prNout nOut := SLP.is_evalPR _ forall₂_AB

@[expose] def prN1 : PR := prNout.getD 0 PR.one

@[expose] def prN2 : PR := prNout.getD 1 PR.one

theorem is_prN1 : PR.Is prN1 n1 := forall₂_getD forall₂_nout 0

theorem is_prN2 : PR.Is prN2 n2 := forall₂_getD forall₂_nout 1

theorem forall₂_N : List.Forall₂ PR.Is [prN1, prN2] [n1, n2] :=
  List.Forall₂.cons is_prN1 (List.Forall₂.cons is_prN2 List.Forall₂.nil)

@[expose] def prWN
    (s : String) : PR := wordPR [prN1, prN2] (parseWord s)

theorem is_prWN
    (s : String) : PR.Is (prWN s) (wN s) := is_wordPR forall₂_N _

@[expose] def prE (i : Fin 6) : PR := prWN (eStr i)

theorem is_prE (i : Fin 6) : PR.Is (prE i) (e i) := is_prWN _

@[expose] def prIota (v : Fin 6 → ZMod 3) : PR :=
  (List.ofFn fun i => (prE i).pow (v i).val).foldr PR.mul PR.one

theorem is_prIota (v : Fin 6 → ZMod 3) : PR.Is (prIota v) (iota v) :=
  is_foldr_mul (forall₂_ofFn fun i => (is_prE i).pow _)

@[expose] def prTau : PR := prWN tauStr

theorem is_prTau : PR.Is prTau tau := is_prWN _

@[expose] def prM (i : Fin 2) : PR := prWN (mStr i)

theorem is_prM (i : Fin 2) : PR.Is (prM i) (m i) := is_prWN _

theorem forall₂_M : List.Forall₂ PR.Is [prM 0, prM 1] [m 0, m 1] :=
  List.Forall₂.cons (is_prM 0) (List.Forall₂.cons (is_prM 1) List.Forall₂.nil)

@[expose] def prWM
    (s : String) : PR := wordPR [prM 0, prM 1] (parseWord s)

theorem is_prWM
    (s : String) : PR.Is (prWM s) (wM s) := is_wordPR forall₂_M _

@[expose] def prCm
    : PR := (((prM 0).inv.mul (prM 1).inv).mul (prM 0)).mul (prM 1)

set_option maxRecDepth 2000 in
theorem is_prCm : PR.Is prCm cm := by
  have h1 := (is_prM 0).inv.mul (is_prM 1).inv
  have h2 := h1.mul (is_prM 0)
  have h3 := h2.mul (is_prM 1)
  exact h3

@[expose] def prCConj (g : PR) : PR := (g.inv.mul prCm).mul g

theorem is_prCConj
    {g : PR} {gg : G} (h : PR.Is g gg) : PR.Is (prCConj g) (cConj gg) := by
  have h1 := h.inv.mul is_prCm
  have h2 := h1.mul h
  exact h2

@[expose] def prS : List PR :=
  [prCm, prCConj (prM 0), prCConj (prM 1), prCConj (prM 0).inv, prCConj (prM 1).inv,
    prCConj ((prM 0).mul (prM 1)), prCConj ((prM 1).mul (prM 0))]

set_option maxRecDepth 2000 in
theorem forall₂_S : List.Forall₂ PR.Is prS S := by
  have h0 := is_prM 0
  have h1 := is_prM 1
  have c0 := is_prCConj h0
  have c1 := is_prCConj h1
  have c2 := is_prCConj h0.inv
  have c3 := is_prCConj h1.inv
  have c4 := is_prCConj (h0.mul h1)
  have c5 := is_prCConj (h1.mul h0)
  exact List.Forall₂.cons is_prCm (List.Forall₂.cons c0 (List.Forall₂.cons c1
    (List.Forall₂.cons c2 (List.Forall₂.cons c3 (List.Forall₂.cons c4
    (List.Forall₂.cons c5 List.Forall₂.nil))))))

@[expose] def prR (k : Fin 12) : PR := prWN (repStr k)

theorem is_prR (k : Fin 12) : PR.Is (prR k) (r k) := is_prWN _

@[expose] def prE0 : PR := prIota v0

theorem is_prE0 : PR.Is prE0 e0 := is_prIota _

@[expose] def prHout
    : List PR := (parseSLP slpMax2).evalPR [prA, prB]

theorem forall₂_hout :
    List.Forall₂ PR.Is prHout hOut := SLP.is_evalPR _ forall₂_AB

@[expose] def prG : PR := wordPR prHout (parseWord gStr)

theorem is_prG : PR.Is prG g := is_wordPR forall₂_hout _

@[expose] def prX (k : Fin 3) : PR := prWN (xStr k)

theorem is_prX (k : Fin 3) : PR.Is (prX k) (xGen k) := is_prWN _

@[expose] def prY (k : Fin 3) : PR := prWN (yStr k)

theorem is_prY (k : Fin 3) : PR.Is (prY k) (yGen k) := is_prWN _

theorem forall₂_NNG :
    List.Forall₂ PR.Is [prN1, prN2, prG] [n1, n2, g] :=
  List.Forall₂.cons is_prN1 (List.Forall₂.cons is_prN2 (List.Forall₂.cons is_prG List.Forall₂.nil))

@[expose] def prAB
    : List PR := (parseSLP slpWordsAB).evalPR [prN1, prN2, prG]

theorem forall₂_AB_out :
    List.Forall₂ PR.Is prAB abOut := SLP.is_evalPR _ forall₂_NNG

end CFSG.Monster.GMS.Griess13.Co1Data
