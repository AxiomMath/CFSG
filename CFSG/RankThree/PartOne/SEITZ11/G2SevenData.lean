module

public import CFSG.LieType.Steinberg.RankTwo.G2CommData

public section

namespace CFSG.RankThree.PartOne.SEITZ11.G2Seven

open CFSG.LieType.Steinberg.RankTwo CFSG.LieType.Chevalley.RootOps

abbrev SPoly := List (ℕ × ℕ × ℤ)

@[expose] def pneg (p : SPoly) : SPoly := p.map fun m => (m.1, m.2.1, -m.2.2)

@[expose] def pmulMono (m : ℕ × ℕ × ℤ) (p : SPoly) : SPoly :=
  p.map fun n => (m.1 + n.1, m.2.1 + n.2.1, m.2.2 * n.2.2)

@[expose] def pinsert (m : ℕ × ℕ × ℤ) : SPoly → SPoly
  | [] => [m]
  | n :: p => if n.1 = m.1 ∧ n.2.1 = m.2.1 then (n.1, n.2.1, n.2.2 + m.2.2) :: p
      else n :: pinsert m p

@[expose] def pcanon (p : SPoly) : SPoly := p.foldr pinsert []

@[expose] def pIsZero (p : SPoly) : Bool := (pcanon p).all fun m => m.2.2 == 0

variable {R : Type*} [CommRing R]

@[expose] def peval (p : SPoly) (c d : R) : R :=
  (p.map fun m => (m.2.2 : R) * c ^ m.1 * d ^ m.2.1).sum

theorem peval_cons (m : ℕ × ℕ × ℤ) (p : SPoly) (c d : R) :
    peval (m :: p) c d = (m.2.2 : R) * c ^ m.1 * d ^ m.2.1 + peval p c d := by
  simp [peval]

theorem peval_append (p q : SPoly) (c d : R) :
    peval (p ++ q) c d = peval p c d + peval q c d := by
  simp [peval]

theorem pneg_cons (m : ℕ × ℕ × ℤ) (p : SPoly) :
    pneg (m :: p) = (m.1, m.2.1, -m.2.2) :: pneg p := rfl

theorem peval_pneg (p : SPoly) (c d : R) : peval (pneg p) c d = - peval p c d := by
  induction p with
  | nil => simp [pneg, peval]
  | cons m p ih =>
    rw [pneg_cons, peval_cons, ih, peval_cons]
    push_cast; ring

theorem pmulMono_cons (m n : ℕ × ℕ × ℤ) (p : SPoly) :
    pmulMono m (n :: p) = (m.1 + n.1, m.2.1 + n.2.1, m.2.2 * n.2.2) :: pmulMono m p := rfl

theorem peval_pmulMono (m : ℕ × ℕ × ℤ) (p : SPoly) (c d : R) :
    peval (pmulMono m p) c d = ((m.2.2 : R) * c ^ m.1 * d ^ m.2.1) * peval p c d := by
  induction p with
  | nil => simp [pmulMono, peval]
  | cons n p ih =>
    rw [pmulMono_cons, peval_cons, ih, peval_cons]
    push_cast; ring

theorem peval_pinsert (m : ℕ × ℕ × ℤ) (p : SPoly) (c d : R) :
    peval (pinsert m p) c d = (m.2.2 : R) * c ^ m.1 * d ^ m.2.1 + peval p c d := by
  induction p with
  | nil => simp [pinsert, peval]
  | cons n p ih =>
    unfold pinsert
    split_ifs with h
    · obtain ⟨h1, h2⟩ := h
      simp only [peval_cons, h1, h2]; push_cast; ring
    · simp only [peval_cons, ih]; ring

theorem peval_pcanon (p : SPoly) (c d : R) : peval (pcanon p) c d = peval p c d := by
  induction p with
  | nil => rfl
  | cons m p ih =>
    simp only [pcanon, List.foldr_cons] at ih ⊢
    rw [peval_pinsert, peval_cons, ih]

theorem pIsZero_sound {p : SPoly} (h : pIsZero p = true) (c d : R) : peval p c d = 0 := by
  rw [← peval_pcanon]
  unfold pIsZero at h
  generalize pcanon p = q at h ⊢
  induction q with
  | nil => rfl
  | cons m q ih =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at h
    rw [peval_cons, h.1, ih h.2]; simp

abbrev Ent7 := Fin 7 × Fin 7 × ℤ

@[expose] def ent7 : ℕ → List Ent7
  | 0 => [(2, 1, 1), (3, 5, 1)]
  | 1 => [(0, 3, 1), (1, 0, 2), (4, 2, 1), (5, 6, 1)]
  | 2 => [(1, 2, 1), (5, 3, 1)]
  | 3 => [(1, 6, -1), (4, 3, 1)]
  | 4 => [(0, 5, -1), (2, 0, 2), (3, 6, 1), (4, 1, -1)]
  | 5 => [(0, 1, 1), (2, 4, 1), (3, 0, 2), (6, 5, 1)]
  | 6 => [(3, 4, 1), (6, 1, -1)]
  | 7 => [(2, 6, -1), (4, 5, -1)]
  | 8 => [(0, 6, -1), (1, 5, 1), (2, 3, 1), (4, 0, -2)]
  | 9 => [(0, 2, 1), (1, 4, -1), (5, 0, -2), (6, 3, 1)]
  | 10 => [(5, 4, -1), (6, 2, -1)]
  | 11 => [(0, 4, -1), (3, 2, 1), (5, 1, 1), (6, 0, -2)]
  | _ => []

@[expose] def ent7sq : ℕ → List Ent7
  | 1 => [(1, 3, 1)]
  | 4 => [(2, 5, -1)]
  | 5 => [(3, 1, 1)]
  | 8 => [(4, 6, 1)]
  | 9 => [(5, 2, -1)]
  | 11 => [(6, 4, 1)]
  | _ => []

@[expose] def entMat (R : Type*) [CommRing R] (l : List Ent7) : Matrix (Fin 7) (Fin 7) R :=
  Matrix.of fun i j => (l.map fun e => if e.1 = i ∧ e.2.1 = j then (e.2.2 : R) else 0).sum

@[expose] def opMat (R : Type*) [CommRing R] (g : ℕ) : Matrix (Fin 7) (Fin 7) R :=
  entMat R (ent7 g)

@[expose] def opMatSq (R : Type*) [CommRing R] (g : ℕ) : Matrix (Fin 7) (Fin 7) R :=
  entMat R (ent7sq g)

@[expose] def rootMat (g : ℕ) (t : R) : Matrix (Fin 7) (Fin 7) R :=
  1 + t • opMat R g + (t * t) • opMatSq R g

theorem int_ident : ∀ g : Fin 12,
    opMat ℤ g.val * opMat ℤ g.val = opMatSq ℤ g.val + opMatSq ℤ g.val ∧
    opMat ℤ g.val * opMatSq ℤ g.val = 0 ∧ opMatSq ℤ g.val * opMat ℤ g.val = 0 ∧
    opMatSq ℤ g.val * opMatSq ℤ g.val = 0 := by
  decide +kernel

theorem entMat_eq_map (R : Type*) [CommRing R] (l : List Ent7) :
    entMat R l = (entMat ℤ l).map (Int.castRingHom R) := by
  ext i j
  simp only [entMat, Matrix.of_apply, Matrix.map_apply, map_list_sum, List.map_map]
  congr 1
  refine List.map_congr_left fun e _ => ?_
  by_cases h : e.1 = i ∧ e.2.1 = j <;> simp [h]

theorem opMat_map (R : Type*) [CommRing R] (g : ℕ) :
    (opMat ℤ g).map (Int.castRingHom R) = opMat R g := (entMat_eq_map R _).symm

theorem opMatSq_map (R : Type*) [CommRing R] (g : ℕ) :
    (opMatSq ℤ g).map (Int.castRingHom R) = opMatSq R g := (entMat_eq_map R _).symm

theorem opMat_mul_opMat (g : ℕ) (hg : g < 12) :
    opMat R g * opMat R g = opMatSq R g + opMatSq R g := by
  have h := congrArg (Int.castRingHom R).mapMatrix (int_ident ⟨g, hg⟩).1
  simpa only [map_mul, map_add, RingHom.mapMatrix_apply, opMat_map, opMatSq_map] using h

theorem opMat_mul_opMatSq (g : ℕ) (hg : g < 12) : opMat R g * opMatSq R g = 0 := by
  have h := congrArg (Int.castRingHom R).mapMatrix (int_ident ⟨g, hg⟩).2.1
  simpa only [map_mul, map_zero, RingHom.mapMatrix_apply, opMat_map, opMatSq_map] using h

theorem opMatSq_mul_opMat (g : ℕ) (hg : g < 12) : opMatSq R g * opMat R g = 0 := by
  have h := congrArg (Int.castRingHom R).mapMatrix (int_ident ⟨g, hg⟩).2.2.1
  simpa only [map_mul, map_zero, RingHom.mapMatrix_apply, opMat_map, opMatSq_map] using h

theorem opMatSq_mul_opMatSq (g : ℕ) (hg : g < 12) : opMatSq R g * opMatSq R g = 0 := by
  have h := congrArg (Int.castRingHom R).mapMatrix (int_ident ⟨g, hg⟩).2.2.2
  simpa only [map_mul, map_zero, RingHom.mapMatrix_apply, opMat_map, opMatSq_map] using h

theorem rootMat_add (g : ℕ) (hg : g < 12) (s t : R) :
    rootMat g (s + t) = rootMat g s * rootMat g t := by
  have h1 := opMat_mul_opMat (R := R) g hg
  have h2 := opMat_mul_opMatSq (R := R) g hg
  have h3 := opMatSq_mul_opMat (R := R) g hg
  have h4 := opMatSq_mul_opMatSq (R := R) g hg
  simp only [rootMat, mul_add, add_mul, one_mul, mul_one, smul_mul_assoc, mul_smul_comm, smul_smul,
    h1, h2, h3, h4, smul_zero, add_zero, smul_add]
  module

theorem rootMat_zero (g : ℕ) : rootMat g (0 : R) = 1 := by simp [rootMat]

abbrev Vec := List SPoly

@[expose] def evalV (v : Vec) (c d : R) : Fin 7 → R := fun i => peval (v.getD i.val []) c d

@[expose] def applyY (g : ℕ) (C : ℤ) (p q : ℕ) (v : Vec) : Vec :=
  (List.finRange 7).map fun i => pcanon (
    v.getD i.val [] ++
    ((ent7 g).map fun e => if e.1 = i then pmulMono (p, q, C * e.2.2) (v.getD e.2.1.val [])
      else []).flatten ++
    ((ent7sq g).map fun e => if e.1 = i then
      pmulMono (2 * p, 2 * q, C * C * e.2.2) (v.getD e.2.1.val []) else []).flatten)

@[expose] def basisV (j : Fin 7) : Vec :=
  (List.finRange 7).map fun i => if i = j then [(0, 0, 1)] else []

theorem getD_finRange_map {α : Type*} (f : Fin 7 → α) (i : Fin 7) (d : α) :
    ((List.finRange 7).map f).getD i.val d = f i := by
  simp [List.getD_eq_getElem?_getD]

theorem peval_flatten (L : List SPoly) (c d : R) :
    peval L.flatten c d = (L.map fun p => peval p c d).sum := by
  induction L with
  | nil => rfl
  | cons p L ih => simp [peval_append, ih]

theorem evalV_basisV (j : Fin 7) (c d : R) : evalV (basisV j) c d = Pi.single j 1 := by
  funext i
  simp only [evalV, basisV, getD_finRange_map]
  by_cases h : i = j
  · subst h; simp [peval]
  · simp [h, peval]

theorem entMat_mulVec (l : List Ent7) (w : Fin 7 → R) (i : Fin 7) :
    (entMat R l).mulVec w i =
      (l.map fun e => if e.1 = i then (e.2.2 : R) * w e.2.1 else 0).sum := by
  induction l with
  | nil => simp [entMat, Matrix.mulVec, dotProduct]
  | cons e l ih =>
    have : entMat R (e :: l) = Matrix.of (fun i j =>
        (if e.1 = i ∧ e.2.1 = j then (e.2.2 : R) else 0)) + entMat R l := by
      ext a b; simp [entMat]
    rw [this, Matrix.add_mulVec, Pi.add_apply, ih, List.map_cons, List.sum_cons]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    by_cases h : e.1 = i
    · simp [h, mul_comm]
    · simp [h]

theorem peval_part (l : List Ent7) (i : Fin 7) (a b : ℕ) (K : ℤ) (v : Vec) (c d : R) :
    peval ((l.map fun e => if e.1 = i then pmulMono (a, b, K * e.2.2) (v.getD e.2.1.val [])
      else []).flatten) c d =
    ((K : R) * c ^ a * d ^ b) *
      (l.map fun e => if e.1 = i then (e.2.2 : R) * peval (v.getD e.2.1.val []) c d
        else 0).sum := by
  rw [peval_flatten, List.map_map, ← List.sum_map_mul_left]
  refine congrArg List.sum (List.map_congr_left fun e _ => ?_)
  by_cases h : e.1 = i
  · simp only [Function.comp_apply, h, ite_true, peval_pmulMono]; push_cast; ring
  · simp [h, peval]

theorem applyY_sound (g : ℕ) (C : ℤ) (p q : ℕ) (v : Vec) (c d : R) :
    evalV (applyY g C p q v) c d =
      (rootMat g ((C : R) * c ^ p * d ^ q)).mulVec (evalV v c d) := by
  funext i
  simp only [applyY, evalV, getD_finRange_map, peval_pcanon, peval_append, rootMat, opMat,
    opMatSq, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, entMat_mulVec]
  rw [peval_part, peval_part]
  push_cast
  ring

@[expose] def repCheck7 (a b : ℕ) (fs : List Factor) : Bool := (List.finRange 7).all fun j =>
  (List.finRange 7).all fun i =>
    pIsZero ((applyY a 1 1 0 (applyY b 1 0 1 (basisV j))).getD i.val [] ++
      pneg ((fs.reverse.foldl (fun v f => applyY f.2.2.1 f.2.2.2 f.1 f.2.1 v)
        (applyY b 1 0 1 (applyY a 1 1 0 (basisV j)))).getD i.val []))

@[expose] def facMat (f : Factor) (c d : R) : Matrix (Fin 7) (Fin 7) R :=
  rootMat f.2.2.1 ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)

theorem foldl_sound (L : List Factor) (v : Vec) (c d : R) :
    evalV (L.foldl (fun v f => applyY f.2.2.1 f.2.2.2 f.1 f.2.1 v) v) c d =
      ((L.reverse.map fun f => facMat f c d).prod).mulVec (evalV v c d) := by
  induction L generalizing v with
  | nil => simp [Matrix.one_mulVec]
  | cons f L ih =>
    rw [List.foldl_cons, ih, applyY_sound, Matrix.mulVec_mulVec, List.reverse_cons,
      List.map_append, List.prod_append]
    simp [facMat]

theorem repCheck7_sound {a b : ℕ} {fs : List Factor} (h : repCheck7 a b fs = true) (c d : R) :
    rootMat a c * rootMat b d =
      (fs.map fun f => facMat f c d).prod * (rootMat b d * rootMat a c) := by
  ext i j
  have hj := List.all_eq_true.1 h j (List.mem_finRange j)
  have hL : evalV (applyY a 1 1 0 (applyY b 1 0 1 (basisV j))) c d =
      (rootMat a c * rootMat b d).mulVec (Pi.single j 1) := by
    rw [applyY_sound, applyY_sound, evalV_basisV, Matrix.mulVec_mulVec]; simp
  have hR : evalV (fs.reverse.foldl (fun v f => applyY f.2.2.1 f.2.2.2 f.1 f.2.1 v)
      (applyY b 1 0 1 (applyY a 1 1 0 (basisV j)))) c d =
      ((fs.map fun f => facMat f c d).prod * (rootMat b d * rootMat a c)).mulVec
        (Pi.single j 1) := by
    rw [foldl_sound, applyY_sound, applyY_sound, evalV_basisV, List.reverse_reverse,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    simp [Matrix.mul_assoc]
  have hi := List.all_eq_true.1 hj i (List.mem_finRange i)
  have h0 := pIsZero_sound (R := R) hi c d
  rw [peval_append, peval_pneg] at h0
  have h1 : evalV (applyY a 1 1 0 (applyY b 1 0 1 (basisV j))) c d i =
      evalV (fs.reverse.foldl (fun v f => applyY f.2.2.1 f.2.2.2 f.1 f.2.1 v)
        (applyY b 1 0 1 (applyY a 1 1 0 (basisV j)))) c d i := by
    simp only [evalV]; exact add_neg_eq_zero.1 h0
  rw [hL, hR] at h1
  simpa [Matrix.mulVec_single_one] using h1

@[expose] def tableOk : Bool := g2CommPairs.all fun e => repCheck7 e.1.1 e.1.2 e.2

@[expose] def commOk : Bool := (List.range 12).all fun a => (List.range 12).all fun b =>
  !(decide (a ≠ b ∧ g2CommRoot a + g2CommRoot b ≠ 0 ∧ g2CommFactors a b = [])) ||
    repCheck7 a b []

set_option maxRecDepth 100000 in
theorem tableOk_true : tableOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem commOk_true : commOk = true := by decide +kernel

theorem table_lt : ∀ e ∈ g2CommPairs, e.1.1 < 12 ∧ e.1.2 < 12 ∧ ∀ f ∈ e.2, f.2.2.1 < 12 := by
  decide +kernel

theorem factors_lt : ∀ a < 12, ∀ b < 12, ∀ f ∈ g2CommFactors a b, f.2.2.1 < 12 := by
  decide +kernel

theorem rootMat_table {e : (ℕ × ℕ) × List Factor} (he : e ∈ g2CommPairs) (c d : R) :
    rootMat e.1.1 c * rootMat e.1.2 d =
      (e.2.map fun f => rootMat f.2.2.1 ((f.2.2.2 : R) * c ^ f.1 * d ^ f.2.1)).prod *
        (rootMat e.1.2 d * rootMat e.1.1 c) :=
  repCheck7_sound (List.all_eq_true.1 tableOk_true e he) c d

theorem rootMat_comm_of_nil {a b : ℕ} (ha : a < 12) (hb : b < 12) (hab : a ≠ b)
    (hs : g2CommRoot a + g2CommRoot b ≠ 0) (h0 : g2CommFactors a b = []) (c d : R) :
    rootMat a c * rootMat b d = rootMat b d * rootMat a c := by
  have hc := List.all_eq_true.1 (List.all_eq_true.1 commOk_true a (List.mem_range.2 ha)) b
    (List.mem_range.2 hb)
  have hr : repCheck7 a b [] = true := by
    simpa [hab, hs, h0] using hc
  simpa using repCheck7_sound (R := R) hr c d

end CFSG.RankThree.PartOne.SEITZ11.G2Seven
