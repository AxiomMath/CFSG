
module


public import CFSG.Sporadic.Th.Setup

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native

namespace Slp

@[expose] noncomputable def t3 : J := a * b

@[expose] noncomputable def t4 : J := t3 * b

@[expose] noncomputable def t5 : J := t3 * t4

@[expose] noncomputable def t6 : J := t3 * t5

@[expose] noncomputable def t7 : J := a * t6

@[expose] noncomputable def t8 : J := t6 * a

@[expose] noncomputable def u : J := t8⁻¹ * t7

@[expose] noncomputable def s8 : J := t6 * t5

@[expose] noncomputable def s9 : J := t3 * s8

@[expose] noncomputable def s10 : J := s9 * t4

@[expose] noncomputable def s7 : J := a * s10

@[expose] noncomputable def s8' : J := s10 * a

@[expose] noncomputable def v : J := s8'⁻¹ * s7

end Slp

@[expose] noncomputable def x : J := Slp.v ^ 14

@[expose] noncomputable def y : J := Slp.t7 * Slp.u ^ 9

@[expose] noncomputable def wordProd
    (w : List Gen) : J := (w.map (Gen.eval x y)).prod

@[expose] noncomputable def M : Subgroup J := Subgroup.closure {x, y}

@[expose] def zWord : List Gen := [.x, .y, .y, .y]

@[expose] noncomputable def z : J := wordProd zWord ^ zExp

@[expose] def qWord : Fin 8 → List Gen :=
  ![[.x, .y], [.y, .x], [.y, .y, .y, .y, .x, .y],
    [.y, .x, .y, .x, .y, .y, .y, .y, .x, .y, .y], [.y, .y, .y, .x, .y, .y],
    [.y, .x, .y, .y, .y, .x, .y, .y, .y, .y], [.x, .y, .y, .y, .x, .y, .y, .x],
    [.y, .x, .y, .y, .y, .y, .x, .y, .y, .y, .x]]

@[expose] noncomputable def q
    (i : Fin 8) : J := wordProd (qWord i) ^ qExp i

@[expose] noncomputable def Q :
    Subgroup J := Subgroup.closure (insert z (Set.range q))

@[expose] noncomputable def nf
    (s : ZMod 2) (v : Fin 8 → ZMod 2) : J :=
  z ^ s.val * (List.ofFn fun i => q i ^ (v i).val).prod

abbrev toMat (g : J) : Matrix (Fin 248) (Fin 248) (ZMod 2) :=
  ((g : GL (Fin 248) (ZMod 2)) : Matrix (Fin 248) (Fin 248) (ZMod 2))

theorem toMat_mul
    (g h : J) : toMat (g * h) = toMat g * toMat h := rfl

theorem toMat_one : toMat (1 : J) = 1 := rfl

theorem toMat_pow (g : J) (n : ℕ) : toMat (g ^ n) = toMat g ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, toMat_mul, ih, pow_succ]

theorem toMat_injective :
    Function.Injective toMat := fun _ _ e => Subtype.ext (Units.ext e)

structure IsRows (R : Array V4) (g : J) : Prop where
  size : R.size = 248
  wf : ∀ r ∈ R, r.wf = true
  eq : rowsMatrix R = toMat g

namespace IsRows

variable {R S : Array V4} {g h : J}

theorem one : IsRows idRows 1 := ⟨idRows_size, idRows_wf, by rw [rowsMatrix_idRows]; rfl⟩

theorem mul (hR : IsRows R g) (hS : IsRows S h) : IsRows (mulRows R S) (g * h) where
  size := by rw [mulRows_size, hR.size]
  wf := mulRows_wf R hS.wf
  eq := by rw [rowsMatrix_mulRows, hR.eq, hS.eq, toMat_mul]

theorem rows_eq (hR : IsRows R g) (hS : IsRows S g) : R = S := by
  refine Array.ext (by rw [hR.size, hS.size]) fun i h1 h2 => ?_
  apply V4.eq_of_toVec_eq (hR.wf _ (Array.getElem_mem h1)) (hS.wf _ (Array.getElem_mem h2))
  funext j
  have hi : i < 248 := hR.size ▸ h1
  have := congrFun (congrFun (hR.eq.trans hS.eq.symm) ⟨i, hi⟩) j
  rwa [rowsMatrix_apply, rowsMatrix_apply, Array.getElem?_eq_getElem h1,
    Array.getElem?_eq_getElem h2, Option.getD_some, Option.getD_some] at this

theorem eq_of_eqRows (hR : IsRows R g) (hS : IsRows S h) (e : eqRows R S = true) : g = h := by
  have := rowsMatrix_eq_of_eqRows e
  rw [hR.eq, hS.eq] at this
  exact toMat_injective this

theorem ne_of_eqRows (hR : IsRows R g) (hS : IsRows S h) (e : eqRows R S = false) : g ≠ h := by
  rintro rfl
  rw [hR.rows_eq hS, eqRows_iff.2 rfl] at e
  exact Bool.noConfusion e

end IsRows

theorem IsRows.pow {R : Array V4} {g : J} (hR : IsRows R g) (n : ℕ) :
    IsRows (powRows R n) (g ^ n) := by
  induction n with
  | zero => exact IsRows.one
  | succ n ih =>
    cases n with
    | zero => simpa [powRows] using hR
    | succ m => rw [pow_succ]; exact ih.mul hR

theorem prodRows_cons (R : Array V4) (l : List (Array V4)) :
    prodRows (R :: l) = mulRows R (prodRows l) := List.foldr_cons

theorem IsRows.prod
    {Rs : List (Array V4)} {gs : List J} (h : List.Forall₂ IsRows Rs gs) :
    IsRows (prodRows Rs) gs.prod := by
  induction h with
  | nil => rw [prodRows_nil, List.prod_nil]; exact IsRows.one
  | cons hR _ ih => rw [prodRows_cons, List.prod_cons]; exact hR.mul ih

theorem IsRows.word
    {rx ry : Array V4} (hx : IsRows rx x) (hy : IsRows ry y) (w : List Gen) :
    IsRows (wordRows rx ry w) (wordProd w) := by
  refine IsRows.prod ?_
  induction w with
  | nil => exact List.Forall₂.nil
  | cons l w ih =>
    refine List.Forall₂.cons ?_ ih
    cases l
    · exact hx
    · exact hy

theorem isRows_a : IsRows rowsA a :=
  ⟨rowsOf_size _, rowsOf_wf _, by rw [rowsA, rowsMatrix_rowsOf_seedA]; rfl⟩

theorem isRows_b : IsRows rowsB b :=
  ⟨rowsOf_size _, rowsOf_wf _, by rw [rowsB, rowsMatrix_rowsOf_seedB]; rfl⟩

namespace Slp

theorem isRows_t3 : IsRows rowsT3 t3 := isRows_a.mul isRows_b

theorem isRows_t4 : IsRows rowsT4 t4 := isRows_t3.mul isRows_b

theorem isRows_t5 : IsRows rowsT5 t5 := isRows_t3.mul isRows_t4

theorem isRows_t6 : IsRows rowsT6 t6 := isRows_t3.mul isRows_t5

theorem isRows_t7 : IsRows rowsT7 t7 := isRows_a.mul isRows_t6

theorem isRows_t8 : IsRows rowsT8 t8 := isRows_t6.mul isRows_a

theorem isRows_s8 : IsRows rowsS8 s8 := isRows_t6.mul isRows_t5

theorem isRows_s9 : IsRows rowsS9 s9 := isRows_t3.mul isRows_s8

theorem isRows_s10 : IsRows rowsS10 s10 := isRows_s9.mul isRows_t4

theorem isRows_s7 : IsRows rowsS7 s7 := isRows_a.mul isRows_s10

theorem isRows_s8' : IsRows rowsS8' s8' := isRows_s10.mul isRows_a

end Slp

@[expose] def rowsZ
    : Array V4 := powRows (wordRows rowsX rowsY zWord) zExp

@[expose] def rowsQs : Array (Array V4) :=
  Array.ofFn fun i : Fin 8 => powRows (wordRows rowsX rowsY (qWord i)) (qExp i)

@[expose] def rowsQ
    (i : Fin 8) : Array V4 := rowsQs[i.val]'(by simp [rowsQs])

theorem rowsQ_eq (i : Fin 8) :
    rowsQ i = powRows (wordRows rowsX rowsY (qWord i)) (qExp i) := by
  simp [rowsQ, rowsQs]

@[expose] noncomputable def nfN (s : ℕ) (e : Fin 8 → ℕ) : J :=
  z ^ s * (List.ofFn fun i => q i ^ e i).prod

theorem nf_eq_nfN (s : ZMod 2) (v : Fin 8 → ZMod 2) :
    nf s v = nfN s.val fun i => (v i).val := rfl

@[expose] def rowsNf (s : ℕ) (e : Fin 8 → ℕ) : Array V4 :=
  mulRows (powRows rowsZ s) (prodRows (List.ofFn fun i => powRows (rowsQ i) (e i)))

@[expose] def rowsNfTab : Array (Array V4) :=
  Array.ofFn fun k : Fin 512 => rowsNf (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2

@[expose] def rowsNfAt
    (k : Fin 512) : Array V4 := rowsNfTab[k.val]'(by simp [rowsNfTab])

theorem rowsNfAt_eq (k : Fin 512) :
    rowsNfAt k = rowsNf (k.val % 2) fun i => k.val / 2 ^ (i.val + 1) % 2 := by
  simp [rowsNfAt, rowsNfTab]

end CFSG.Sporadic.Th.Max3
