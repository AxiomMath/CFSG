module

public import CFSG.Sporadic.SmallOddCore.J2LocalCheckInputs
public import CFSG.Quasithin.Recognition.St84.HeisF4

public section

namespace CFSG.Quasithin.F112R.St84.J2Model

open CFSG.Fischer
open CFSG.Quasithin.F112R.St84.Heis
open CFSG.Sporadic.SmallOddCore
open CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native
open CFSG.Sporadic.SmallOddCore.Native

@[expose] def c2aT (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [2, 1, 2]

@[expose] def c2bT (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [4, 4]

@[expose] def e1T (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [3, 2, 3, 3]

@[expose] def e2T (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [2, 3, 3, 3]

@[expose] def f1T (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [2, 1, 2]

@[expose] def f2T (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [1, 4, 3, 4, 3, 2]

@[expose] def bmT (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [2, 3]

@[expose] def tmT (_ : Unit := ()) : Table := wordTbl 315 j2C2Gens [1, 2, 4, 2, 1, 4]

@[expose] def yT (_ : Unit := ()) : Table :=
  wordTbl 315 j2PGTbls.toList [1, 2, 1, 2, 1, 2, 2, 1, 2, 2]

@[expose] def rmT (_ : Unit := ()) : Table :=
  wordTbl 315 [e1T, e2T, f1T, f2T, tmT, bmT, yT] [1, 4, 7, 5, 6]

@[expose] def EmT (a : F4) : Table :=
  compT 315 (powT 315 (a.code.val % 2) e1T) (powT 315 (a.code.val / 2) e2T)

@[expose] def FmT (b : F4) : Table :=
  compT 315 (powT 315 (b.code.val % 2) f1T) (powT 315 (b.code.val / 2) f2T)

@[expose] def commFT (b : F4) : Table :=
  compT 315 (compT 315 (compT 315 e1T (FmT b)) (invT 315 e1T)) (invT 315 (FmT b))

@[expose] def κT (q : Q1M) : Table :=
  compT 315 (compT 315 (EmT q.a) (FmT q.b)) (commFT (q.c + q.a * q.b))

@[expose] def q1mIdx (q : Q1M) : ℕ :=
  q.a.code.val + 4 * q.b.code.val + 16 * q.c.code.val

@[expose] def q1mAt (k : ℕ) : Q1M :=
  ⟨⟨⟨k % 4, Nat.mod_lt _ (by norm_num)⟩⟩,
   ⟨⟨k / 4 % 4, Nat.mod_lt _ (by norm_num)⟩⟩,
   ⟨⟨k / 16 % 4, Nat.mod_lt _ (by norm_num)⟩⟩⟩

@[expose] def q1mList (_ : Unit := ()) : List Q1M := List.ofFn fun k : Fin 64 => q1mAt k

@[expose] def κArr (_ : Unit := ()) : Array Table := (q1mList ()).map κT |>.toArray

theorem q1mAt_q1mIdx (q : Q1M) : q1mAt (q1mIdx q) = q := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := q
  refine Q1M.ext ?_ ?_ ?_
  · refine F4.ext_code (Fin.ext ?_)
    simp only [q1mAt, q1mIdx]
    omega
  · refine F4.ext_code (Fin.ext ?_)
    simp only [q1mAt, q1mIdx]
    omega
  · refine F4.ext_code (Fin.ext ?_)
    simp only [q1mAt, q1mIdx]
    omega

theorem q1mIdx_lt (q : Q1M) : q1mIdx q < 64 := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩ := q
  simp only [q1mIdx]
  omega

theorem q1mList_length : (q1mList ()).length = 64 := by
  simp [q1mList]

theorem κArr_getElem (i : ℕ) (hi : i < 64) : (κArr ())[i]! = κT (q1mAt i) := by
  have hlen : i < ((q1mList ()).map κT).length := by simpa [q1mList] using hi
  rw [κArr, List.getElem!_toArray,
    getElem!_pos (List.map κT (q1mList ())) i hlen, List.getElem_map]
  congr 1
  simp only [q1mList, List.getElem_ofFn]

@[expose] def a1Checks (_ : Unit := ()) : List Bool :=
  [permOK 315 (c2aT ()), permOK 315 (c2bT ())]

@[expose] def a1OK (_ : Unit := ()) : Bool := (a1Checks ()).all id

@[expose] def a2Checks (_ : Unit := ()) : List Bool :=
  let a := c2aT ()
  let b := c2bT ()
  [tblEq 315 (compT 315 a a) (idT 315),
   tblEq 315 (powT 315 3 b) (idT 315),
   tblEq 315 (powT 315 5 (compT 315 a b)) (idT 315)]

@[expose] def a2OK (_ : Unit := ()) : Bool := (a2Checks ()).all id

@[expose] def a3OK (_ : Unit := ()) : Bool := enumOK 315 200 60 [c2aT, c2bT]

theorem c2aT_permOK (h : a1OK = true) : permOK 315 (c2aT ()) = true := by
  have h' : (a1Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (permOK 315 (c2aT ())) (by simp [a1Checks])
  rwa [id_eq] at hx

theorem c2bT_permOK (h : a1OK = true) : permOK 315 (c2bT ()) = true := by
  have h' : (a1Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (permOK 315 (c2bT ())) (by simp [a1Checks])
  rwa [id_eq] at hx

theorem c2aT_sq (h : a2OK = true) :
    tblEq 315 (compT 315 (c2aT ()) (c2aT ())) (idT 315) = true := by
  have h' : (a2Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h'
    (tblEq 315 (compT 315 (c2aT ()) (c2aT ())) (idT 315)) (by simp [a2Checks])
  rwa [id_eq] at hx

theorem c2bT_cube (h : a2OK = true) :
    tblEq 315 (powT 315 3 (c2bT ())) (idT 315) = true := by
  have h' : (a2Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (tblEq 315 (powT 315 3 (c2bT ())) (idT 315))
    (by simp [a2Checks])
  rwa [id_eq] at hx

theorem c2abT_pow_five (h : a2OK = true) :
    tblEq 315 (powT 315 5 (compT 315 (c2aT ()) (c2bT ()))) (idT 315) = true := by
  have h' : (a2Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h'
    (tblEq 315 (powT 315 5 (compT 315 (c2aT ()) (c2bT ()))) (idT 315))
    (by simp [a2Checks])
  rwa [id_eq] at hx

theorem c2_enumOK (h : a3OK = true) :
    enumOK 315 200 60 [c2aT, c2bT] = true := h

@[expose] def b0Tbls (_ : Unit := ()) : List Table :=
  [e1T, e2T, f1T, f2T, bmT, tmT, yT, rmT]

@[expose] def b0OK (_ : Unit := ()) : Bool :=
  (b0Tbls ()).all (fun T => permOK 315 T)

@[expose] def b1OK (_ : Unit := ()) : Bool :=
  let ks := κArr ()
  let it := idT 315
  allIn 0 64 (fun i => allIn 0 64 (fun j =>
      tblEq 315 (ks[q1mIdx (q1mAt i * q1mAt j)]!)
        (compT 315 (ks[i]!) (ks[j]!)))) &&
    allIn 0 64 (fun i => decide (q1mAt i = 1) || !tblEq 315 (ks[i]!) it)

@[expose] def gensQ1M : List Q1M := [e1, e2, f1, f2]

@[expose] def conjGenOK (c : Table) (α : MulAut Q1M) : Bool :=
  (gensQ1M).all fun g => tblEq 315 (conjT 315 c (invT 315 c) (κT g)) (κT (α g))

@[expose] def b2Checks (_ : Unit := ()) : List Bool :=
  [conjGenOK (bmT ()) βM, conjGenOK (rmT ()) ρM, conjGenOK (tmT ()) τM]

@[expose] def b2OK (_ : Unit := ()) : Bool := (b2Checks ()).all id

@[expose] def b3Checks (_ : Unit := ()) : List Bool :=
  let b := bmT ()
  let t := tmT ()
  [tblEq 315 (powT 315 3 b) (idT 315),
   tblEq 315 (powT 315 2 t) (idT 315),
   tblEq 315 (compT 315 t b) (compT 315 b t)]

@[expose] def b3OK (_ : Unit := ()) : Bool := (b3Checks ()).all id

@[expose] def b4Checks (_ : Unit := ()) : List Bool :=
  [enumOK 315 200 128 [e1T, e2T, f1T, f2T, tmT],
   enumOK 315 100 18 [rmT, bmT, tmT],
   enumOK 315 3000 1152 [e1T, e2T, f1T, f2T, rmT, bmT, tmT]]

@[expose] def b4OK (_ : Unit := ()) : Bool := (b4Checks ()).all id

@[expose] def b5OK (_ : Unit := ()) : Bool := j2Sift (rmT ())

theorem b0_permOK (h : b0OK = true) {T : Table} (hT : T ∈ b0Tbls ()) : permOK 315 T = true := by
  have h' : (b0Tbls ()).all (fun T => permOK 315 T) = true := h
  exact List.all_eq_true.mp h' T hT

theorem e1T_permOK (h : b0OK = true) : permOK 315 (e1T ()) = true :=
  b0_permOK h (by simp [b0Tbls])

theorem e2T_permOK (h : b0OK = true) : permOK 315 (e2T ()) = true :=
  b0_permOK h (by simp [b0Tbls])

theorem f1T_permOK (h : b0OK = true) : permOK 315 (f1T ()) = true :=
  b0_permOK h (by simp [b0Tbls])

theorem f2T_permOK (h : b0OK = true) : permOK 315 (f2T ()) = true :=
  b0_permOK h (by simp [b0Tbls])

theorem bmT_permOK (h : b0OK = true) : permOK 315 (bmT ()) = true :=
  b0_permOK h (by simp [b0Tbls])

theorem tmT_permOK (h : b0OK = true) : permOK 315 (tmT ()) = true :=
  b0_permOK h (by simp [b0Tbls])

theorem rmT_permOK (h : b0OK = true) : permOK 315 (rmT ()) = true :=
  b0_permOK h (by simp [b0Tbls])

theorem κT_mul (h : b1OK = true) (x y : Q1M) :
    tblEq 315 (κT (x * y)) (compT 315 (κT x) (κT y)) = true := by
  obtain ⟨hp, -⟩ := Bool.and_eq_true_iff.mp h
  have hx := allIn_eq_true.mp hp (q1mIdx x) (Nat.zero_le _) (q1mIdx_lt x)
  have hy := allIn_eq_true.mp hx (q1mIdx y) (Nat.zero_le _) (q1mIdx_lt y)
  rw [q1mAt_q1mIdx x, q1mAt_q1mIdx y] at hy
  rw [κArr_getElem (q1mIdx x) (q1mIdx_lt x), κArr_getElem (q1mIdx y) (q1mIdx_lt y),
    κArr_getElem (q1mIdx (x * y)) (q1mIdx_lt (x * y))] at hy
  rw [q1mAt_q1mIdx x, q1mAt_q1mIdx y, q1mAt_q1mIdx (x * y)] at hy
  exact hy

theorem κT_ne_one (h : b1OK = true) {x : Q1M} (hx : x ≠ 1) :
    tblEq 315 (κT x) (idT 315) = false := by
  obtain ⟨-, hi⟩ := Bool.and_eq_true_iff.mp h
  have hx' := allIn_eq_true.mp hi (q1mIdx x) (Nat.zero_le _) (q1mIdx_lt x)
  rw [κArr_getElem (q1mIdx x) (q1mIdx_lt x), q1mAt_q1mIdx x] at hx'
  have hne : decide (x = 1) = false := decide_eq_false_iff_not.mpr hx
  rw [hne, Bool.false_or] at hx'
  simpa using hx'

theorem conjGenOK_spec {c : Table} {α : MulAut Q1M} (h : conjGenOK c α = true)
    {g : Q1M} (hg : g ∈ gensQ1M) :
    tblEq 315 (conjT 315 c (invT 315 c) (κT g)) (κT (α g)) = true := by
  have h' : (gensQ1M).all
      (fun g => tblEq 315 (conjT 315 c (invT 315 c) (κT g)) (κT (α g))) = true := h
  exact List.all_eq_true.mp h' g hg

theorem b2OK_bm (h : b2OK = true) : conjGenOK (bmT ()) βM = true := by
  have h' : (b2Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (conjGenOK (bmT ()) βM) (by simp [b2Checks])
  rwa [id_eq] at hx

theorem b2OK_rm (h : b2OK = true) : conjGenOK (rmT ()) ρM = true := by
  have h' : (b2Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (conjGenOK (rmT ()) ρM) (by simp [b2Checks])
  rwa [id_eq] at hx

theorem b2OK_tm (h : b2OK = true) : conjGenOK (tmT ()) τM = true := by
  have h' : (b2Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (conjGenOK (tmT ()) τM) (by simp [b2Checks])
  rwa [id_eq] at hx

theorem bm_cube (h : b3OK = true) : tblEq 315 (powT 315 3 (bmT ())) (idT 315) = true := by
  have h' : (b3Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (tblEq 315 (powT 315 3 (bmT ())) (idT 315))
    (by simp [b3Checks])
  rwa [id_eq] at hx

theorem tm_square (h : b3OK = true) : tblEq 315 (powT 315 2 (tmT ())) (idT 315) = true := by
  have h' : (b3Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (tblEq 315 (powT 315 2 (tmT ())) (idT 315))
    (by simp [b3Checks])
  rwa [id_eq] at hx

theorem tm_bm_commute (h : b3OK = true) :
    tblEq 315 (compT 315 (tmT ()) (bmT ())) (compT 315 (bmT ()) (tmT ())) = true := by
  have h' : (b3Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h'
    (tblEq 315 (compT 315 (tmT ()) (bmT ())) (compT 315 (bmT ()) (tmT ())))
    (by simp [b3Checks])
  rwa [id_eq] at hx

theorem enumOK_T0m (h : b4OK = true) :
    enumOK 315 200 128 [e1T, e2T, f1T, f2T, tmT] = true := by
  have h' : (b4Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (enumOK 315 200 128 [e1T, e2T, f1T, f2T, tmT])
    (by simp [b4Checks])
  rwa [id_eq] at hx

theorem enumOK_Am (h : b4OK = true) :
    enumOK 315 100 18 [rmT, bmT, tmT] = true := by
  have h' : (b4Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h' (enumOK 315 100 18 [rmT, bmT, tmT]) (by simp [b4Checks])
  rwa [id_eq] at hx

theorem enumOK_X2m (h : b4OK = true) :
    enumOK 315 3000 1152 [e1T, e2T, f1T, f2T, rmT, bmT, tmT] = true := by
  have h' : (b4Checks ()).all id = true := h
  have hx := List.all_eq_true.mp h'
    (enumOK 315 3000 1152 [e1T, e2T, f1T, f2T, rmT, bmT, tmT]) (by simp [b4Checks])
  rwa [id_eq] at hx

theorem sift_rmT (h : b5OK = true) : j2Sift (rmT ()) = true := h

end CFSG.Quasithin.F112R.St84.J2Model
