module

public import CFSG.Sporadic.Schreier.J1ClosureSpec
public import CFSG.Monster.B.Mathieu.CertData
public import CFSG.Assembly.Defs
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore

public section

namespace CFSG.Sporadic.Schreier

open CFSG.Certificates CFSG.Monster.B.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Schreier.Native

theorem letterValue_eq {M : Type*} [Group M] (gs : List M) (l : ℤ) :
    letterValue gs l = if 0 < l then gs.getD (l.natAbs - 1) 1 else (gs.getD (l.natAbs - 1) 1)⁻¹ :=
  rfl

theorem wordValue_cons' {M : Type*} [Group M] (gs : List M) (l : ℤ) (w : List ℤ) :
    wordValue gs (l :: w) = letterValue gs l * wordValue gs w := by
  simp [wordValue]

theorem wordValue_mem' {M : Type*} [Group M] (gs : List M) (H : Subgroup M)
    (hgs : ∀ g ∈ gs, g ∈ H) (w : List ℤ) : wordValue gs w ∈ H := by
  induction w with
  | nil => exact H.one_mem
  | cons l w ih =>
    rw [wordValue_cons']
    refine H.mul_mem ?_ ih
    have hg : gs.getD (l.natAbs - 1) 1 ∈ H := by
      rw [List.getD_eq_getElem?_getD]
      cases h : gs[l.natAbs - 1]? with
      | none => exact H.one_mem
      | some g => exact hgs g (List.mem_of_getElem? h)
    rw [letterValue_eq]
    split
    · exact hg
    · exact H.inv_mem hg

@[expose] def slpVals {M : Type*} [Group M] (x y : M) (ds : List (List ℤ)) : List M :=
  ds.foldl (fun vs w => vs ++ [wordValue vs w]) [x, y]

@[expose] def slpExpr {M : Type*} [Group M] (x y : M) (ds : List (List ℤ)) (e : List ℤ) : M :=
  wordValue (slpVals x y ds) e

theorem getD_map {α β : Type*} (f : α → β) (l : List α) (k : ℕ) (d : α) :
    (l.map f).getD k (f d) = f (l.getD k d) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getD_eq_getElem?_getD]
  cases l[k]? <;> rfl

theorem letterValue_map {M N : Type*} [Group M] [Group N] (φ : M →* N) (gs : List M) (l : ℤ) :
    letterValue (gs.map φ) l = φ (letterValue gs l) := by
  have h : (gs.map φ).getD (l.natAbs - 1) 1 = φ (gs.getD (l.natAbs - 1) 1) := by
    rw [← map_one φ, getD_map]
  simp only [letterValue_eq, h]
  split_ifs
  · rfl
  · rw [map_inv]

theorem wordValue_map {M N : Type*} [Group M] [Group N] (φ : M →* N) (gs : List M)
    (w : List ℤ) : wordValue (gs.map φ) w = φ (wordValue gs w) := by
  induction w with
  | nil => simp [wordValue]
  | cons l w ih => rw [wordValue_cons', wordValue_cons', map_mul, letterValue_map, ih]

theorem slpVals_map {M N : Type*} [Group M] [Group N] (φ : M →* N) (x y : M)
    (ds : List (List ℤ)) : slpVals (φ x) (φ y) ds = (slpVals x y ds).map φ := by
  unfold slpVals
  suffices h : ∀ vs : List M, ds.foldl (fun vs w => vs ++ [wordValue vs w]) (vs.map φ) =
      (ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs).map φ by
    simpa using h [x, y]
  induction ds with
  | nil => intro vs; rfl
  | cons w ds ih =>
    intro vs
    simp only [List.foldl_cons]
    rw [← ih, List.map_append, wordValue_map]
    rfl

theorem slpExpr_map {M N : Type*} [Group M] [Group N] (φ : M →* N) (x y : M)
    (ds : List (List ℤ)) (e : List ℤ) : slpExpr (φ x) (φ y) ds e = φ (slpExpr x y ds e) := by
  rw [slpExpr, slpVals_map, wordValue_map, slpExpr]

theorem slpVals_mem {M : Type*} [Group M] (H : Subgroup M) {x y : M} (hx : x ∈ H) (hy : y ∈ H)
    (ds : List (List ℤ)) : ∀ g ∈ slpVals x y ds, g ∈ H := by
  unfold slpVals
  suffices h : ∀ vs : List M, (∀ g ∈ vs, g ∈ H) →
      ∀ g ∈ ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs, g ∈ H by
    refine h [x, y] ?_
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hx
    · exact hy
  induction ds with
  | nil => intro vs hvs; exact hvs
  | cons w ds ih =>
    intro vs hvs
    refine ih _ fun g hg => ?_
    rcases List.mem_append.1 hg with hg | hg
    · exact hvs g hg
    · rw [List.mem_singleton] at hg
      rw [hg]
      exact wordValue_mem' vs H hvs w

theorem slpExpr_mem {M : Type*} [Group M] (H : Subgroup M) {x y : M} (hx : x ∈ H) (hy : y ∈ H)
    (ds : List (List ℤ)) (e : List ℤ) : slpExpr x y ds e ∈ H :=
  wordValue_mem' _ H (slpVals_mem H hx hy ds) e

variable {n : ℕ}

@[expose] def tblWord (n : ℕ) (Ts : List Table) : List ℤ → Table × Bool
  | [] => (idT n, true)
  | l :: w =>
    let R := tblWord n Ts w
    let T := Ts.getD (l.natAbs - 1) (idT n)
    if 0 < l then (compT n T R.1, R.2) else
      (compT n (invT n T) R.1, R.2 && invOK n T (invT n T))

theorem rep_getD_tables (hn : n < 2 ^ 32) {Ts : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) Ts gs) (k : ℕ) : Rep n (Ts.getD k (idT n)) (gs.getD k 1) := by
  induction h generalizing k with
  | nil => exact Rep.idT hn
  | @cons T g Ts gs hTg _ ih =>
    cases k with
    | zero => exact hTg
    | succ k => exact ih k

theorem rep_tblWord (hn : n < 2 ^ 32) {Ts : List Table} {gs : List (Equiv.Perm (Fin n))}
    (h : List.Forall₂ (Rep n) Ts gs) :
    ∀ w : List ℤ, (tblWord n Ts w).2 = true → Rep n (tblWord n Ts w).1 (wordValue gs w)
  | [], _ => by simpa [tblWord, wordValue] using Rep.idT (G := Equiv.Perm (Fin n)) hn
  | l :: w, hok => by
    have hT := rep_getD_tables hn h (l.natAbs - 1)
    by_cases hl : 0 < l
    · simp only [tblWord, hl, ↓reduceIte] at hok ⊢
      rw [wordValue_cons', letterValue_eq]
      simp only [hl, ↓reduceIte]
      exact Rep.compT hT (rep_tblWord hn h w hok)
    · simp only [tblWord, hl, ↓reduceIte, Bool.and_eq_true] at hok ⊢
      rw [wordValue_cons', letterValue_eq]
      simp only [hl, ↓reduceIte]
      exact Rep.compT (hT.inv_of_invOK hok.2) (rep_tblWord hn h w hok.1)

@[expose] def tblSlp (n : ℕ) (x y : Table) (ds : List (List ℤ)) : List Table × Bool :=
  ds.foldl (fun acc w => (acc.1 ++ [(tblWord n acc.1 w).1], acc.2 && (tblWord n acc.1 w).2))
    ([x, y], true)

theorem tblSlp_flag {ds : List (List ℤ)} :
    ∀ acc : List Table × Bool,
      (ds.foldl (fun acc w => (acc.1 ++ [(tblWord n acc.1 w).1], acc.2 && (tblWord n acc.1 w).2))
        acc).2 = true → acc.2 = true := by
  induction ds with
  | nil => intro acc h; exact h
  | cons w ds ih =>
    intro acc h
    have := ih _ h
    simp only [Bool.and_eq_true] at this
    exact this.1

theorem rep_tblSlp_aux (hn : n < 2 ^ 32) (ds : List (List ℤ)) :
    ∀ (acc : List Table × Bool) (vs : List (Equiv.Perm (Fin n))),
      List.Forall₂ (Rep n) acc.1 vs →
      (ds.foldl (fun acc w => (acc.1 ++ [(tblWord n acc.1 w).1], acc.2 && (tblWord n acc.1 w).2))
        acc).2 = true →
      List.Forall₂ (Rep n)
        (ds.foldl (fun acc w => (acc.1 ++ [(tblWord n acc.1 w).1], acc.2 && (tblWord n acc.1 w).2))
          acc).1 (ds.foldl (fun vs w => vs ++ [wordValue vs w]) vs) := by
  induction ds with
  | nil => intro acc vs hacc _; exact hacc
  | cons w ds ih =>
    intro acc vs hacc hfl
    simp only [List.foldl_cons] at hfl ⊢
    have hf := tblSlp_flag _ hfl
    simp only [Bool.and_eq_true] at hf
    refine ih _ _ ?_ hfl
    exact forall₂_append hacc (.cons (rep_tblWord hn hacc w hf.2) .nil)

theorem rep_tblSlp (hn : n < 2 ^ 32) {xT yT : Table} {x y : Equiv.Perm (Fin n)}
    (hx : Rep n xT x) (hy : Rep n yT y) (ds : List (List ℤ))
    (h : (tblSlp n xT yT ds).2 = true) :
    List.Forall₂ (Rep n) (tblSlp n xT yT ds).1 (slpVals x y ds) :=
  rep_tblSlp_aux hn ds _ _ (.cons hx (.cons hy .nil)) h

@[expose] def natTbl (n : ℕ) (l : List ℕ) : Table :=
  Array.ofFn (n := n) fun j => UInt32.ofNat (l.getD j 0)

@[expose] def sylowGens (n : ℕ) (aT bT : Table) (ds exprs : List (List ℤ)) : Array Table :=
  (exprs.map fun e => (tblWord n (tblSlp n aT bT ds).1 e).1).toArray

@[expose] def sylowAutOK (n : ℕ) (aT bT : Table) (ds exprs : List (List ℤ)) (z0T : Table)
    (cap N k : ℕ) : Bool :=
  let V := tblSlp n aT bT ds
  let pT := sylowGens n aT bT ds exprs
  let pInv := pT.map (invT n)
  let clo := mulClosure n pT cap
  V.2 && exprs.all (fun e => (tblWord n V.1 e).2) &&
    (List.range pT.size).all (fun i => invOK n pT[i]! pInv[i]!) &&
    mulTreeOK n pT clo.1 clo.2.1 clo.2.2 && mulClosedOK n pT pInv clo.1 &&
    keysDistinct n clo.1.toList && clo.1.size == 2 ^ k && N % 2 ^ k == 0 &&
    N / 2 ^ k % 2 == 1 && clo.1.any (fun e => tblEq n e aT) &&
    clo.1.any (fun e => tblEq n z0T e) && pT.all (fun p => commT n z0T p) &&
    invOK n z0T (invT n z0T)

@[expose] def survivorsOK (n : ℕ) (aT bT z0T : Table) (ds exprs : List (List ℤ)) (r s mb : ℕ)
    (Y : List Table) : Bool :=
  let pT := (sylowGens n aT bT ds exprs).toList
  let zb := conjT n z0T (invT n z0T) bT
  Y.all fun y => !(pairTest n r s 2 mb aT y) ||
    (let V := tblSlp n aT y ds
     let ws := exprs.map (tblWord n V.1)
     V.2 && ws.all (·.2) &&
       (!((ws.zip pT).all fun q => tblEq n q.1.1 q.2) || tblEq n y bT || tblEq n y zb))

end CFSG.Sporadic.Schreier
