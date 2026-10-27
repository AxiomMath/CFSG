module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7DatD1
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7DatD2
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7B

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

@[expose] def memB (l : PL) : Bool := l.getD 0 0 == 0 && sameSet (imgSet l L0) L0

@[expose] def conjL (r x : PL) : PL := comp r (comp x r)

@[expose] def chkU (s t u : PL) : Bool :=
  comp u u == idL && memB u && memB (conjL t u) && memB (conjL s (conjL t u)) &&
    memB (conjL t (conjL s (conjL t u))) && !memB (conjL s u)

@[expose] def chkW (s t w : PL) : Bool :=
  comp w w == idL && memB w && memB (conjL s w) && memB (conjL t (conjL s w)) &&
    memB (conjL s (conjL t (conjL s w))) && !memB (conjL t w)

@[expose] def chkE (e : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  let s := Dl1.getD e.1 []
  let t := Dl2.getD e.2.1 []
  let u := Thl.getD e.2.2.1 []
  let w₁ := Thl.getD e.2.2.2.1 []
  let w₂ := Thl.getD e.2.2.2.2.1 []
  let w₃ := Thl.getD e.2.2.2.2.2 []
  chkU s t u && chkW s t w₁ && chkW s t w₂ && chkW s t w₃ &&
    !memB (conjL t (comp w₁ w₂)) && !memB (conjL t (comp w₁ w₃)) &&
    !memB (conjL t (comp w₂ w₃))

@[expose] def pairTable : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
  [ (8, 11, 3, 9, 29, 40), (8, 12, 3, 9, 29, 40), (8, 17, 61, 19, 29, 54),
    (8, 24, 3, 9, 29, 40), (8, 25, 3, 9, 29, 40), (8, 73, 61, 19, 29, 54),
    (8, 74, 61, 19, 29, 54), (8, 75, 61, 19, 29, 54), (9, 11, 3, 21, 36, 53),
    (9, 12, 3, 21, 36, 53), (9, 17, 61, 14, 33, 36), (9, 24, 3, 21, 36, 53),
    (9, 25, 3, 21, 36, 53), (9, 73, 61, 14, 33, 36), (9, 74, 61, 14, 33, 36),
    (9, 75, 61, 14, 33, 36), (10, 11, 3, 14, 33, 36), (10, 12, 3, 14, 33, 36),
    (10, 17, 61, 21, 36, 53), (10, 24, 3, 14, 33, 36), (10, 25, 3, 14, 33, 36),
    (10, 73, 61, 21, 36, 53), (10, 74, 61, 21, 36, 53), (10, 75, 61, 21, 36, 53),
    (32, 11, 3, 19, 29, 54), (32, 12, 3, 19, 29, 54), (32, 17, 61, 9, 29, 40),
    (32, 24, 3, 19, 29, 54), (32, 25, 3, 19, 29, 54), (32, 73, 61, 9, 29, 40),
    (32, 74, 61, 9, 29, 40), (32, 75, 61, 9, 29, 40), (60, 11, 3, 19, 29, 54),
    (60, 12, 3, 19, 29, 54), (60, 17, 61, 9, 29, 40), (60, 24, 3, 19, 29, 54),
    (60, 25, 3, 19, 29, 54), (60, 73, 61, 9, 29, 40), (60, 74, 61, 9, 29, 40),
    (60, 75, 61, 9, 29, 40), (92, 11, 3, 9, 29, 40), (92, 12, 3, 9, 29, 40),
    (92, 17, 61, 19, 29, 54), (92, 24, 3, 9, 29, 40), (92, 25, 3, 9, 29, 40),
    (92, 73, 61, 19, 29, 54), (92, 74, 61, 19, 29, 54), (92, 75, 61, 19, 29, 54),
    (93, 11, 3, 21, 36, 53), (93, 12, 3, 21, 36, 53), (93, 17, 61, 14, 33, 36),
    (93, 24, 3, 21, 36, 53), (93, 25, 3, 21, 36, 53), (93, 73, 61, 14, 33, 36),
    (93, 74, 61, 14, 33, 36), (93, 75, 61, 14, 33, 36), (95, 11, 3, 14, 33, 36),
    (95, 12, 3, 14, 33, 36), (95, 17, 61, 21, 36, 53), (95, 24, 3, 14, 33, 36),
    (95, 25, 3, 14, 33, 36), (95, 73, 61, 21, 36, 53), (95, 74, 61, 21, 36, 53),
    (95, 75, 61, 21, 36, 53)]

theorem pairTable_check : pairTable.all chkE = true := by decide +kernel

@[expose] def condS (l : PL) : Bool := comp l l == idL && !memB l

theorem pairTable_complete :
    ∀ l ∈ Dl1, condS l = true → ∀ m ∈ Dl2, condS m = true → powL (comp l m) 4 = idL →
      ∃ e ∈ pairTable, Dl1.getD e.1 [] = l ∧ Dl2.getD e.2.1 [] = m := by decide +kernel

theorem pairTable_idx : ∀ e ∈ pairTable, e.2.2.1 < 128 ∧ e.2.2.2.1 < 128 ∧ e.2.2.2.2.1 < 128 ∧
    e.2.2.2.2.2 < 128 := by decide +kernel

theorem Thl_length : Thl.length = 128 := by decide +kernel

theorem getD_mem_Thl {i : ℕ} (hi : i < 128) : Thl.getD i [] ∈ Thl := by
  rw [List.getD_eq_getElem _ _ (by rw [Thl_length]; exact hi)]
  exact List.getElem_mem _

end CFSG.Quasithin.H13.F431.U42Aut
