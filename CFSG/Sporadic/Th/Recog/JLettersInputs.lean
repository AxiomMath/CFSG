module

public import Certificates.Data.G23RecogWordsInputs
public import CFSG.Assembly.Defs
public import CFSG.Sporadic.Bridge.ThData
public import CFSG.Sporadic.Recognition.PresentedWords
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.Sporadic.Th.Recog

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3
open CFSG.GH74.QTGen4.Recog.G23

@[expose] def midWord : List (Fin 8 × Bool) :=
  [(3, false), (2, true), (1, false)]

@[expose] def uWord : List (Fin 8 × Bool) :=
  midWord ++ [(0, true)] ++ FreeGroup.invRev midWord

@[expose] def aWord : List (Fin 8 × Bool) :=
  [(7, true), (3, true), (4, true), (3, false), (7, false)]

@[expose] def cWord : List (Fin 8 × Bool) :=
  uWord ++ aWord ++ uWord ++ aWord ++ uWord ++ aWord ++ [(0, true)] ++ uWord

@[expose] def lWord : Fin 6 → List (Fin 8 × Bool) :=
  ![[(0, true), (3, true), (2, true), (1, true), (7, true), (3, true), (7, true), (4, true),
      (3, true), (7, true), (3, true), (2, true), (3, true), (7, false), (2, true), (1, true),
      (3, true), (2, true), (1, false), (0, false), (3, true)],
    [(3, true), (2, true), (3, true), (2, true), (1, true), (7, true), (3, true), (7, true),
      (4, true), (7, false), (3, true), (2, true), (3, true), (7, false), (0, true), (1, true),
      (2, true), (1, true), (3, true), (2, true), (3, true)],
    [(3, false), (1, false), (0, false), (2, false), (3, false), (1, false), (2, false),
      (3, false), (1, false), (0, false), (7, true), (3, true), (2, true), (3, true),
      (7, false), (3, true), (4, true), (1, false), (7, false), (3, false), (1, false),
      (7, true), (3, false), (1, false), (2, false), (4, false)],
    [(7, false), (1, false), (7, true), (3, false), (7, false), (1, false), (7, false),
      (0, true), (2, true), (4, true)],
    [(2, false), (3, false), (1, false), (2, false), (4, false), (3, false), (2, false),
      (3, false), (1, false), (2, false), (3, false), (7, false), (3, false), (7, false),
      (1, false), (7, false), (3, false), (1, false), (0, false), (4, false), (7, false)],
    [(1, false), (0, false), (2, true), (1, true), (3, true), (2, true), (3, true), (4, true),
      (7, false), (3, true), (2, true), (3, true), (7, true), (3, true), (1, false), (7, false),
      (3, false), (1, false), (7, false), (0, false)]]

@[expose] def wJ (i : Fin 8) : List Max3.Gen :=
  match i.val with
  | 0 =>
    []
  | 1 =>
    []
  | 2 =>
    [
      .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .x, .y, .y, .y, .y, .y, .x,
      .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y,
      .y, .x, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y
    ]
  | 3 =>
    [
      .x, .y, .x, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .x, .y, .x, .y,
      .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y,
      .y, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y,
      .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y, .y, .x, .y, .y,
      .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y
    ]
  | 4 =>
    [
      .x, .y, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y, .y, .x, .y, .x, .y, .y, .y, .y,
      .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .x, .y, .x, .x, .y, .y, .x, .y, .x, .y, .y, .x,
      .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .x, .y,
      .x, .y, .y, .y, .x, .y, .x, .y, .x
    ]
  | 5 =>
    [
      .y, .y, .y, .x, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y, .y,
      .x, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .x, .y, .x, .x, .y, .y, .y, .y, .y, .x,
      .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y,
      .y, .x, .y, .x, .y, .y, .y, .y, .y, .x, .y, .x, .y, .y, .y, .y, .y, .x, .y, .x, .y, .y,
      .x, .y, .x, .y, .y, .y, .y, .y, .x, .y
    ]
  | 6 =>
    [
      .y, .x, .y, .x, .y, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y, .y, .x, .y, .y, .y,
      .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .x, .y, .x, .y, .x, .y, .x, .y,
      .y, .x, .y, .x, .y, .x, .y, .x, .y, .x, .y, .y
    ]
  | _ =>
    [
      .y, .x, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y, .y, .y, .x, .y, .x, .y, .y, .y, .y,
      .y, .x, .y, .x, .y, .y, .x, .y, .y, .x, .x, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .y,
      .x, .y, .x, .y, .y, .y, .y, .y, .x, .y, .y, .x, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y,
      .y, .y, .y, .x, .y, .y, .y, .y, .y, .y, .y, .y, .y, .y
    ]

@[expose] def εJ (i : Fin 8) : ℕ :=
  match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 0
  | 6 => 0
  | _ => 1

@[expose] def rowsWJ (i : Fin 8) : Array V4 :=
  mulRows (wordRows rowsX rowsY (wJ i)) (powRows rowsA (εJ i))

@[expose] def rowsG (i : Fin 8) : Array V4 :=
  (CFSG.Sporadic.Bridge.Th.imgMats[i.val]?).getD idRows

@[expose] def rowsGInv (i : Fin 8) : Array V4 :=
  ((CFSG.Sporadic.Bridge.Th.imgMats.map invRows)[i.val]?).getD idRows

@[expose] def wRows {n : ℕ} (rs rsi : Fin n → Array V4) (w : List (Fin n × Bool)) : Array V4 :=
  prodRows (w.map fun l => if l.2 then rs l.1 else rsi l.1)

@[expose] def hswWord (i : Fin 8) : List (Fin 8 × Bool) :=
  (cWord ++ [(i, true)]) ++ FreeGroup.invRev cWord

@[expose] def hswWordInv (i : Fin 8) : List (Fin 8 × Bool) :=
  (cWord ++ [(i, false)]) ++ FreeGroup.invRev cWord

@[expose] def rowsHsw (i : Fin 8) : Array V4 :=
  wRows rowsG rowsGInv (hswWord i)

@[expose] def rowsHswInv (i : Fin 8) : Array V4 :=
  wRows rowsG rowsGInv (hswWordInv i)

@[expose] def rowsHswArr (_ : Unit := ()) : Array (Array V4) :=
  Array.ofFn (n := 8) fun i => rowsHsw i

@[expose] def rowsHswInvArr (_ : Unit := ()) : Array (Array V4) :=
  Array.ofFn (n := 8) fun i => rowsHswInv i

@[expose] def wRowsArr {n : ℕ} (rs rsi : Array (Array V4))
    (w : List (Fin n × Bool)) : Array V4 :=
  prodRows (w.map fun l =>
    if l.2 then (rs[l.1.val]?).getD idRows else (rsi[l.1.val]?).getD idRows)

@[expose] def rowsLArr (_ : Unit := ()) : Array (Array V4) :=
  let H := rowsHswArr ()
  let HI := rowsHswInvArr ()
  Array.ofFn (n := 6) fun i => wRowsArr H HI (lWord i)

@[expose] def rowsLInvArr (_ : Unit := ()) : Array (Array V4) :=
  let H := rowsHswArr ()
  let HI := rowsHswInvArr ()
  Array.ofFn (n := 6) fun i => wRowsArr H HI (FreeGroup.invRev (lWord i))

@[expose] def rowsL (i : Fin 6) : Array V4 :=
  wRowsArr (rowsHswArr ()) (rowsHswInvArr ()) (lWord i)

@[expose] def rowsLInv (i : Fin 6) : Array V4 :=
  wRowsArr (rowsHswArr ()) (rowsHswInvArr ()) (FreeGroup.invRev (lWord i))

theorem rowsLArr_get (i : Fin 6) :
    ((rowsLArr ())[i.val]?).getD idRows = rowsL i := by
  simp [rowsLArr, rowsL, Array.getElem?_ofFn, i.isLt]

theorem rowsLInvArr_get (i : Fin 6) :
    ((rowsLInvArr ())[i.val]?).getD idRows = rowsLInv i := by
  simp [rowsLInvArr, rowsLInv, Array.getElem?_ofFn, i.isLt]

theorem rowsHswArr_get (i : Fin 8) :
    ((rowsHswArr ())[i.val]?).getD idRows = rowsHsw i := by
  simp [rowsHswArr, Array.getElem?_ofFn, i.isLt]

theorem rowsHswInvArr_get (i : Fin 8) :
    ((rowsHswInvArr ())[i.val]?).getD idRows = rowsHswInv i := by
  simp [rowsHswInvArr, Array.getElem?_ofFn, i.isLt]

@[expose] def checkWJ2 (_ : Unit := ()) : Bool := eqRows (rowsHsw 2) (rowsWJ 2)
@[expose] def checkWJ3 (_ : Unit := ()) : Bool := eqRows (rowsHsw 3) (rowsWJ 3)
@[expose] def checkWJ4 (_ : Unit := ()) : Bool := eqRows (rowsHsw 4) (rowsWJ 4)
@[expose] def checkWJ5 (_ : Unit := ()) : Bool := eqRows (rowsHsw 5) (rowsWJ 5)
@[expose] def checkWJ6 (_ : Unit := ()) : Bool := eqRows (rowsHsw 6) (rowsWJ 6)
@[expose] def checkWJ7 (_ : Unit := ()) : Bool := eqRows (rowsHsw 7) (rowsWJ 7)

@[expose] def checkLJ (_ : Unit := ()) : Bool :=
  let L := rowsLArr ()
  let LI := rowsLInvArr ()
  g23Words.all (fun r => eqRows (wRowsArr L LI r) idRows)

theorem rowsMatrix_prodRows (l : List (Array V4)) :
    rowsMatrix (prodRows l) = (l.map rowsMatrix).prod := by
  induction l with
  | nil => rw [prodRows_nil, rowsMatrix_idRows]; rfl
  | cons R l ih => rw [prodRows_cons, rowsMatrix_mulRows, ih]; rfl

theorem toMat_prod (l : List ↥CFSG.Sporadic.Th.J) :
    (l.map toMat).prod = toMat l.prod := by
  induction l with
  | nil => rw [List.prod_nil, toMat_one]; rfl
  | cons g l ih => rw [List.map_cons, List.prod_cons, List.prod_cons, toMat_mul, ih]

theorem rowsMatrix_wRows {n : ℕ} (rs rsi : Fin n → Array V4)
    (g : Fin n → ↥CFSG.Sporadic.Th.J)
    (h : ∀ i, rowsMatrix (rs i) = toMat (g i))
    (hi : ∀ i, rowsMatrix (rsi i) = toMat ((g i)⁻¹))
    (w : List (Fin n × Bool)) :
    rowsMatrix (wRows rs rsi w) = toMat (CFSG.Sporadic.Recognition.PresentedWords.wprod g w) := by
  unfold wRows
  rw [rowsMatrix_prodRows]
  have hmap : (w.map fun l => rowsMatrix (if l.2 then rs l.1 else rsi l.1)) =
      (w.map fun l => toMat (if l.2 then g l.1 else (g l.1)⁻¹)) := by
    apply List.map_congr_left
    intro l _
    obtain ⟨i, b⟩ := l
    cases b <;> simp [hi i, h i]
  calc
    (List.map rowsMatrix (List.map (fun l => if l.2 then rs l.1 else rsi l.1) w)).prod
        = (w.map fun l => rowsMatrix (if l.2 then rs l.1 else rsi l.1)).prod  := by
            rw [List.map_map]; rfl
    _ = (w.map fun l => toMat (if l.2 then g l.1 else (g l.1)⁻¹)).prod := by rw [hmap]
    _ = toMat ((w.map fun l => if l.2 then g l.1 else (g l.1)⁻¹).prod) := by
          simpa only [List.map_map, Function.comp_def] using
            toMat_prod (w.map fun l => if l.2 then g l.1 else (g l.1)⁻¹)
    _ = toMat (CFSG.Sporadic.Recognition.PresentedWords.wprod g w) := rfl

theorem rowsMatrix_wRowsArr {n : ℕ} (rs rsi : Array (Array V4))
    (g : Fin n → ↥CFSG.Sporadic.Th.J)
    (h : ∀ i, rowsMatrix ((rs[i.val]?).getD idRows) = toMat (g i))
    (hi : ∀ i, rowsMatrix ((rsi[i.val]?).getD idRows) = toMat ((g i)⁻¹))
    (w : List (Fin n × Bool)) :
    rowsMatrix (wRowsArr rs rsi w) =
      toMat (CFSG.Sporadic.Recognition.PresentedWords.wprod g w) := by
  unfold wRowsArr
  rw [rowsMatrix_prodRows]
  have hmap : (w.map fun l =>
      rowsMatrix (if l.2 then (rs[l.1.val]?).getD idRows else (rsi[l.1.val]?).getD idRows)) =
      (w.map fun l => toMat (if l.2 then g l.1 else (g l.1)⁻¹)) := by
    apply List.map_congr_left
    intro l _
    obtain ⟨i, b⟩ := l
    cases b <;> simp [hi i, h i]
  calc
    (List.map rowsMatrix (List.map (fun l =>
        if l.2 then (rs[l.1.val]?).getD idRows else (rsi[l.1.val]?).getD idRows) w)).prod
        = (w.map fun l => rowsMatrix (if l.2 then (rs[l.1.val]?).getD idRows
            else (rsi[l.1.val]?).getD idRows)).prod  := by rw [List.map_map]; rfl
    _ = (w.map fun l => toMat (if l.2 then g l.1 else (g l.1)⁻¹)).prod := by rw [hmap]
    _ = toMat ((w.map fun l => if l.2 then g l.1 else (g l.1)⁻¹).prod) := by
          simpa only [List.map_map, Function.comp_def] using
            toMat_prod (w.map fun l => if l.2 then g l.1 else (g l.1)⁻¹)
    _ = toMat (CFSG.Sporadic.Recognition.PresentedWords.wprod g w) := rfl

end CFSG.Sporadic.Th.Recog
