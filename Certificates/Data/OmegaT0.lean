module

public import Certificates.Data.PSp43Sylow
public import Certificates.Data.OmegaT0Words

public section

namespace Certificates.OmegaT0

open CFSG.ComponentClassification.CatFactsSmall.PSp43 CFSG.GH74.KGroups CFSG.Sporadic.Schreier

local notation "P45" => Equiv.Perm (Fin 45)

@[expose] def z0 (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 2] * List.formPerm [3, 6] * List.formPerm [4, 7] * List.formPerm [5, 8] *
    List.formPerm [9, 12] * List.formPerm [10, 13] * List.formPerm [11, 14] *
    List.formPerm [17, 19] * List.formPerm [18, 22] * List.formPerm [21, 23] *
    List.formPerm [27, 29] * List.formPerm [28, 32] * List.formPerm [31, 33] *
    List.formPerm [37, 39] * List.formPerm [38, 42] * List.formPerm [41, 43])

@[expose] def yB (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 17] * List.formPerm [2, 19] * List.formPerm [3, 29] *
    List.formPerm [4, 37] * List.formPerm [5, 14] * List.formPerm [6, 27] * List.formPerm [7, 39] *
    List.formPerm [8, 11] * List.formPerm [9, 38] * List.formPerm [10, 31] *
    List.formPerm [12, 42] * List.formPerm [13, 33] * List.formPerm [18, 23] *
    List.formPerm [21, 22] * List.formPerm [25, 30] * List.formPerm [26, 34] *
    List.formPerm [28, 41] * List.formPerm [32, 43] * List.formPerm [35, 36] *
    List.formPerm [40, 44])

@[expose] def za (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 3, 2, 6] * List.formPerm [4, 8, 7, 5] * List.formPerm [9, 21, 12, 23] *
    List.formPerm [10, 32, 13, 28] * List.formPerm [11, 37, 14, 39] * List.formPerm [15, 16] *
    List.formPerm [17, 27, 19, 29] * List.formPerm [18, 42, 22, 38] * List.formPerm [20, 24] *
    List.formPerm [25, 30] * List.formPerm [26, 34] * List.formPerm [31, 41, 33, 43] *
    List.formPerm [35, 44] * List.formPerm [36, 40])

@[expose] def zb (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 4, 2, 7] * List.formPerm [3, 5, 6, 8] * List.formPerm [9, 41, 12, 43] *
    List.formPerm [10, 22, 13, 18] * List.formPerm [11, 27, 14, 29] * List.formPerm [15, 20] *
    List.formPerm [16, 24] * List.formPerm [17, 39, 19, 37] * List.formPerm [21, 31, 23, 33] *
    List.formPerm [25, 34] * List.formPerm [26, 30] * List.formPerm [28, 38, 32, 42] *
    List.formPerm [35, 36] * List.formPerm [40, 44])

@[expose] def ya (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 5, 2, 8] * List.formPerm [3, 7, 6, 4] * List.formPerm [9, 31, 12, 33] *
    List.formPerm [10, 42, 13, 38] * List.formPerm [11, 17, 14, 19] * List.formPerm [15, 24] *
    List.formPerm [16, 20] * List.formPerm [18, 28, 22, 32] * List.formPerm [21, 43, 23, 41] *
    List.formPerm [25, 26] * List.formPerm [27, 37, 29, 39] * List.formPerm [30, 34] *
    List.formPerm [35, 40] * List.formPerm [36, 44])

@[expose] def yb (_ : Unit := ()) : P45 :=
  tab (List.formPerm [1, 18] * List.formPerm [2, 22] * List.formPerm [3, 29] *
    List.formPerm [5, 41] * List.formPerm [6, 27] * List.formPerm [8, 43] * List.formPerm [9, 38] *
    List.formPerm [11, 32] * List.formPerm [12, 42] * List.formPerm [14, 28] *
    List.formPerm [17, 23] * List.formPerm [19, 21] * List.formPerm [25, 44] *
    List.formPerm [26, 35] * List.formPerm [30, 40] * List.formPerm [34, 36])


@[expose] def sylowChk (_ : Unit := ()) : Bool :=
  let T := elemsT QT0
  decide ((T.filter fun g => T.all fun t => decide (g * t = t * g)).length = 2) &&
    (elemsT QA45).all fun a => !(T.all fun t => decide (a * t = t * a)) || decide (a ∈ T)

@[expose] def coverOK (reps L : List P45) : Bool :=
  L.all fun t => !decide (t * t = 1 ∧ t ≠ 1) ||
    L.any fun g => reps.any fun r => decide (g * t * g⁻¹ = r)

@[expose] def cntCent (L : List P45) (r : P45) : ℕ :=
  (L.filter fun g => decide (g * r = r * g)).length

@[expose] def wordW {M : Type*} [Monoid M] (gs : List M) (w : List ℕ) : M :=
  w.foldr (fun i g => gs.getD i 1 * g) 1

@[expose] def coverW {M : Type*} [Group M] [DecidableEq M] (gs reps : List M) :
    List M → List (List ℕ) → Bool
  | [], _ => true
  | t :: L, ws =>
    if decide (t * t = 1 ∧ t ≠ 1) then
      match ws with
      | [] => false
      | w :: ws =>
        (reps.any fun r => decide (wordW gs w * t * (wordW gs w)⁻¹ = r)) && coverW gs reps L ws
    else coverW gs reps L ws

@[expose] def treeL {M : Type*} [One M] (f : M → M → M) (a : M) (gs : List M)
    (ps : List (ℕ × ℕ)) : List M :=
  ps.foldl (fun L kp => L ++ [f (gs.getD kp.1 1) (L.getD kp.2 a)]) [a]

@[expose] def mulTab {M : Type*} [Monoid M] [DecidableEq M] (gs L : List M) (ts : List (List ℕ))
    (k : ℕ) : Bool :=
  decide (L.length = k) && decide (ts.length = gs.length) &&
    (gs.zip ts).all fun st => (List.range k).all fun i =>
      decide (st.2.getD i 0 < k) && decide (st.1 * L.getD i 1 = L.getD (st.2.getD i 0) 1)

@[expose] def nodupB : List ℕ → ℕ → Bool
  | [], _ => true
  | c :: cs, m => !m.testBit c && nodupB cs (m ||| 2 ^ c)

@[expose] def pcode {n : ℕ} (ps : List (Fin n)) (σ : Equiv.Perm (Fin n)) : ℕ :=
  ps.foldr (fun p a => (σ p).val + n * a) 0

@[expose] def orbTr {M : Type*} [Group M] [DecidableEq M] (cd : M → ℕ) (gs : List M) (r : M)
    (ps : List (ℕ × ℕ)) (ts : List (List ℕ)) (k : ℕ) : Bool :=
  let O := treeL (fun s o => s * o * s⁻¹) r gs ps
  decide (O.length = k) && nodupB (O.map cd) 0 && decide (ts.length = gs.length) &&
    (gs.zip ts).all fun st => decide (st.2.length = k) && (O.zip st.2).all fun oj =>
      decide (oj.2 < k) && decide (st.1 * oj.1 * st.1⁻¹ = O.getD oj.2 r)

@[expose] def t0L (_ : Unit := ()) : List P45 :=
  treeL (· * ·) 1 (sylW.map (wordW [x45, y45])) t0P

@[expose] def n7Chk (_ : Unit := ()) : Bool :=
  let S := [x45, y45]
  let T := t0L ()
  let z := z0 ()
  let y := yB ()
  let a := za ()
  let b := zb ()
  let c := ya ()
  let d := yb ()
  mulTab (sylW.map (wordW S)) T t0T 64 && coverW S [z, y] T covW && decide (z ∈ T) &&
    decide (y ∈ T) &&
    orbTr (pcode [0, 1, 3]) S z orbZP orbZT 45 && decide (cntCent T z = 64) &&
    orbTr (pcode [0, 1, 3]) S y orbYP orbYT 270 && decide (cntCent T y = 32) &&
    decide (a ∈ T) && decide (b ∈ T) && decide (a * z = z * a) && decide (b * z = z * b) &&
    decide (a * b * a⁻¹ * b⁻¹ = z) &&
    decide (c ∈ T) && decide (d ∈ T) && decide (c * y = y * c) && decide (d * y = y * d) &&
    decide (c * d * c⁻¹ * d⁻¹ = y)

@[expose] def check (_ : Unit := ()) : Bool := sylowChk () && n7Chk ()

end Certificates.OmegaT0
