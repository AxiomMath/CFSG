module

public import CFSG.RankThree.Native.ONTripleModelInputs

public section

namespace CFSG.RankThree.Native.ONTriple

open CFSG.KC.Misc.F7 CFSG.KC.Loop

@[expose] def omegaN (i j : ℕ) : ℕ :=
  ([[0, 0, 0, 1], [0, 0, 2, 2], [0, 1, 0, 0], [2, 1, 0, 0]].getD i []).getD j 0

@[expose] def conjData : List (ℕ × ℕ × ℕ × List ℕ) :=
  [(rN1, 0, 2, [2, 0, 0, 0]), (rN1, 1, 0, [0, 0, 1, 0]), (rN1, 2, 2, [0, 2, 0, 0]),
    (rN1, 3, 0, [0, 2, 1, 2]), (rN2, 0, 2, [0, 0, 0, 2]), (rN2, 1, 0, [1, 1, 2, 1]),
    (rN2, 2, 0, [2, 2, 2, 0]), (rN2, 3, 0, [1, 0, 0, 0])]

@[expose] def sigK1 : List ℕ := [3, 0, 2, 1, 4, 5]

@[expose] def sigK2 : List ℕ := [5, 3, 0, 4, 1, 2]

@[expose] def sigV : List (List (List (List ℕ))) :=
  [[[[1, 0, 4, 3, 2, 5], [2, 4, 0, 3, 1, 5], [4, 2, 1, 3, 0, 5]],
      [[1, 0, 3, 2, 4, 5], [2, 3, 0, 1, 4, 5], [3, 2, 1, 0, 4, 5]],
      [[1, 0, 5, 3, 4, 2], [2, 5, 0, 3, 4, 1], [5, 2, 1, 3, 4, 0]]],
    [[[0, 5, 4, 3, 2, 1], [3, 1, 4, 0, 2, 5], [3, 5, 2, 0, 4, 1]],
      [[0, 3, 5, 1, 4, 2], [4, 1, 5, 3, 0, 2], [4, 3, 2, 1, 0, 5]],
      [[0, 4, 3, 2, 1, 5], [5, 1, 3, 2, 4, 0], [5, 4, 2, 3, 1, 0]]]]

@[expose] noncomputable def commM (x xi y yi : Nat) : Nat := mmul x (mmul y (mmul xi yi))

@[expose] noncomputable def conjM (n ni x : Nat) : Nat := mmul ni (mmul x n)

@[expose] noncomputable def nfM (c : Nat) (e : List Nat) : Nat :=
  mmul (powM (rM (nthN rX 3)) (nthN e 3)) (mmul (powM (rM (nthN rX 2)) (nthN e 2))
    (mmul (powM (rM (nthN rX 1)) (nthN e 1)) (mmul (powM (rM (nthN rX 0)) (nthN e 0))
      (powM (rM 7) c))))

@[expose, irreducible] noncomputable def ptM (t : Nat) : Nat := widenR 8 (nthN ptsC t)
@[expose] noncomputable def pvM (t : Nat) : List Nat := nthLN pivM t

@[expose] noncomputable def mapsBlocksM (gI : Nat) (σ : List Nat) (k : Nat) : Bool :=
  allN 60 (mapsPt gI σ k)
where
  mapsPt (gI : Nat) (σ : List Nat) (k t : Nat) : Bool :=
    strictB (nthN (nthLN blkPerms k) t) (mapsAt gI σ t)
  mapsAt (gI : Nat) (σ : List Nat) (t u : Nat) : Bool :=
    andB (Nat.blt u 60) (andB (Nat.beq (Nat.div u 10) (nthN σ (Nat.div t 10)))
      (inSpan (imgS (ptM t) gI) (ptM u) (pvM u)))

@[expose] noncomputable def chkPtsM (lo cnt : Nat) : Bool :=
  allN cnt fun d => strictB (Nat.add lo d) fun s => (andB (pivOK (ptM s) (pvM s)) (allN 60 fun t => (ifB (Nat.beq s t) (true) ((notB (inSpan (ptM s) (ptM t) (pvM t)))))))

@[expose] noncomputable def chkP0M : Bool :=
  (andB (allL rX fun r => Nat.beq (powM (rM r) 3) idM) (allN 4 fun i => allN 4 fun j => (ifB (Nat.beq i j) (true) (Nat.beq (commM (rM (nthN rX i)) (rIM (nthN rX i)) (rM (nthN rX j)) (rIM (nthN rX j)))
        (powM (rM 7) (omegaN i j))))))

@[expose] noncomputable def conjOKM (d : ℕ × ℕ × ℕ × List ℕ) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun n rest => Prod.rec (motive := fun _ => Bool)
    (fun i rest2 => Prod.rec (motive := fun _ => Bool)
      (fun c e => Nat.beq (conjM (rM n) (rIM n) (rM (nthN rX i))) (nfM c e)) rest2) rest) d

@[expose] noncomputable def chkConjM : Bool := allL conjData conjOKM

@[expose] noncomputable def chkK0M : Bool :=
  (andB (allL [rK1, rK2] fun k =>
      Nat.beq (mmul (rM k) (rM (nthN rX 0))) (mmul (rM (nthN rX 0)) (rM k))) ((andB (Nat.beq (rM rY1) (rM (nthN rX 1))) (Nat.beq (rM rY3) (rM rX12)))))

@[expose] noncomputable def chkBlocksM : Bool :=
  (andB (mapsBlocksM (rIM rK1) sigK1 0) ((andB (mapsBlocksM (rIM rK2) sigK2 1) ((andB (mapsBlocksM (rIM 7) [0, 1, 2, 3, 4, 5] 2) (strictB (imgS (ptM 0) (rIM (nthN rX 0))) fun U =>
        allN 60 fun t => (notB (inSpan U (ptM t) (pvM t)))))))))

@[expose] noncomputable def vRegs (j m : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih k => Nat.rec (motive := fun _ => List Nat) (nthLN x m) (fun k' _ => ih k') k) rV j

@[expose] noncomputable def yRegM (j : Nat) : Nat := (ifN (Nat.beq j 0) (nthN rX 1) (rX12))

@[expose] noncomputable def sigVM (j m i : Nat) : List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => List.nil)
    (fun x _ ih k => Nat.rec (motive := fun _ => List Nat) (nthLN (nthLLN x m) i)
      (fun k' _ => ih k') k) sigV j
where
  nthLLN (l : List (List (List Nat))) (m : Nat) : List (List Nat) :=
    List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => List.nil)
      (fun x _ ih k => Nat.rec (motive := fun _ => List (List Nat)) x (fun k' _ => ih k') k) l m

@[expose] noncomputable def vOKM (j m : Nat) : Bool :=
  strictB (rM (nthN (vRegs j m) 0)) fun t0 => strictB (rM (nthN (vRegs j m) 1)) fun t1 =>
  strictB (rM (nthN (vRegs j m) 2)) fun t2 =>
    (andB (Nat.beq (mmul t0 t1) t2) ((andB (Nat.beq (mmul t1 t0) t2) ((andB (allL [t0, t1, t2] (fun t => (andB (Nat.beq (mmul t t) idM) ((notB (Nat.beq t idM)))))) ((andB (allL [t0, t1, t2] (fun t => anyLN [t0, t1, t2] fun t' =>
          Nat.beq (conjM (rM (yRegM j)) (rIM (yRegM j)) t) t')) (allN 3 fun i => mapsBlocksM (rIM (nthN (vRegs j m) i)) (sigVM j m i)
          (Nat.add 3 (Nat.add (Nat.mul 9 j) (Nat.add (Nat.mul 3 m) i)))))))))))

@[expose] noncomputable def chkVM : Bool := allN 2 fun j => allN 3 fun m => vOKM j m

@[expose] noncomputable def witOKM (d : ℕ × ℕ × ℕ × ℕ × ℕ) : Bool :=
  strictB (witT d.1 d.2.1 d.2.2.2.1 0) (witS0 d.1 d.2.2.1 d.2.2.2.2)
where
  witS0 (j l2 v2 t0 : Nat) : Bool := strictB (witT j l2 v2 0) (witS1 j l2 v2 t0)
  witS1 (j l2 v2 t0 s0 : Nat) : Bool := strictB (witT j l2 v2 1) (witU t0 s0)
  witU (t0 s0 s1 : Nat) : Bool := strictB (mmul s1 (mmul t0 (mmul s0 t0))) witB
  witT (j l v i : Nat) : Nat :=
    conjM (rM (nthN (nthLN rL j) l)) (rIM (nthN (nthLN rL j) l)) (rM (nthN (vRegs j v) i))
  witB (u : Nat) : Bool := andB (Nat.beq (powM u 3) idM) (notB (Nat.beq u idM))

@[expose] noncomputable def chkWitM (lo cnt : Nat) : Bool :=
  allN cnt fun t => witOKM (nthW witData (Nat.add lo t))
where
  nthW (l : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (t : Nat) : ℕ × ℕ × ℕ × ℕ × ℕ :=
    List.rec (motive := fun _ => Nat → ℕ × ℕ × ℕ × ℕ × ℕ) (fun _ => (0, 0, 0, 0, 0))
      (fun x _ ih j => Nat.rec (motive := fun _ => ℕ × ℕ × ℕ × ℕ × ℕ) x (fun j' _ => ih j') j) l t

end CFSG.RankThree.Native.ONTriple

end
