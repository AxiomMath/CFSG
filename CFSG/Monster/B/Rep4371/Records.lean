module

public import CFSG.Monster.B.Rep4371.Raw
public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.B.Short.AxisOrbit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.Griess CFSG.Monster.ScalarKernel
  CFSG.Monster.B.Rep4371

@[expose] noncomputable def TQ (a : C) : Q := spinEquiv ⟨0, a, 0⟩

@[expose] def deltaBasis (j : Fin 12) : Cocode := Submodule.Quotient.mk (bvec 24 (Umask j))

theorem pair_deltaBasis (i j : Fin 12) : pair (basisC i) (deltaBasis j) = if i = j then 1 else 0 := by
  rw [deltaBasis, pair_mk, basisC_apply, B_dot_Umask]

@[expose] def epsStar (j : ℕ) : ZMod 2 := boolZ ((191 : ℕ).testBit j)

@[expose] noncomputable def qElt (i : Fin 23) : Q :=
  if (i : ℕ) = 0 then zQ
  else if h : (i : ℕ) ≤ 11 then TQ (basisC ⟨i, by omega⟩ + epsStar i • basisC 0)
  else DQ (deltaBasis ⟨i - 11, by omega⟩)

theorem toD_two_pow (j : Fin 12) : toD (2 ^ (j : ℕ)) = deltaBasis j := by
  refine (eq_toD_of_pair fun i => ?_).symm
  rw [pair_deltaBasis, Nat.testBit_two_pow]
  by_cases h : i = j
  · subst h; simp [boolZ]
  · rw [ite_eq_right h, decide_eq_false (fun h' => h (Fin.ext h'.symm)), boolZ_false]

theorem qElt_eq (i : Fin 23) : qElt i = pauliQ (Model.qPauli i) := by
  unfold qElt Model.qPauli
  by_cases h0 : (i : ℕ) = 0
  · rw [ite_eq_left h0, ite_eq_left h0, zQ, pauliQ]
    congr 1
    exact SpinCoord.ext rfl toC_zero.symm toD_zero.symm
  rw [ite_eq_right h0, ite_eq_right h0]
  by_cases h11 : (i : ℕ) ≤ 11
  · rw [dite_eq_left h11, ite_eq_left h11, TQ, pauliQ]
    congr 1
    refine SpinCoord.ext rfl ?_ toD_zero.symm
    show basisC ⟨i, _⟩ + epsStar i • basisC 0 = toC (2 ^ (i : ℕ) ^^^ _)
    rw [toC_xor, toC_ite, ← toC_two_pow ⟨i, by omega⟩, ← toC_two_pow 0, epsStar]
    rfl
  · rw [dite_eq_right h11, ite_eq_right h11, DQ_eq, pauliQ]
    congr 1
    refine SpinCoord.ext rfl toC_zero.symm ?_
    show deltaBasis ⟨i - 11, _⟩ = toD (2 ^ ((i : ℕ) - 11))
    exact (toD_two_pow ⟨i - 11, by omega⟩).symm

theorem rStar_eq : Short.rStar = pauliQ (false, 0, 191) := by
  have hd : Model.dualN (2 ^ ((0 : Fin 24) : ℕ) ||| 2 ^ ((1 : Fin 24) : ℕ)) = 191 := by decide
  have h := pauliQ_minus (i := 0) (j := 1) (by decide)
  rw [hd] at h
  rw [Short.rStar, h]
  rfl

theorem qElt_mul_rStar (i : Fin 23) : qElt i * Short.rStar = Short.rStar * qElt i := by
  have h : Model.Pauli.mul (Model.qPauli i) (false, 0, 191) =
      Model.Pauli.mul (false, 0, 191) (Model.qPauli i) := by
    revert i
    decide
  rw [qElt_eq, rStar_eq, ← pauliQ_mul, ← pauliQ_mul, h]

end CFSG.Monster.B

namespace CFSG.Monster.B.Rep4371

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice CFSG.Monster.Lifts
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.Griess CFSG.Monster.ScalarKernel

@[expose] noncomputable def letterPerm (l : ℤ) : AutPerm :=
  if 0 < l then (if l.natAbs = 1 then pAAut else if l.natAbs = 2 then pBAut else 1)
  else (if l.natAbs = 1 then pAAut else if l.natAbs = 2 then pBAut else 1)⁻¹

@[expose] noncomputable def wordPerm : List ℤ → AutPerm
  | [] => 1
  | l :: w => wordPerm w * letterPerm l

theorem PO_wordPerm_cons (l : ℤ) (w : List ℤ) :
    PO (wordPerm (l :: w)) = PO (letterPerm l) * PO (wordPerm w) := by
  rw [wordPerm, VisQuot.PO_mul]

@[expose] noncomputable def permPair (p : AutPerm) : Pvis := ⟨(sU p, PO p), sU_PO_mem_Pvis p⟩

@[expose] noncomputable def frameSum (w : List ℤ) : C :=
  (w.map fun k => if h : k.toNat - 3 < 12 then basisC ⟨k.toNat - 3, h⟩ else 0).sum

theorem toC_foldl_frame (w : List ℤ) (hw : ∀ k ∈ w, k.toNat - 3 < 12) (a : ℕ) :
    toC (w.foldl (fun a k => a ^^^ 2 ^ (k.toNat - 3)) a) = toC a + frameSum w := by
  induction w generalizing a with
  | nil => simp [frameSum]
  | cons k w ih =>
    have hk := hw k List.mem_cons_self
    rw [List.foldl_cons, ih (fun k' hk' => hw k' (List.mem_cons_of_mem _ hk')), toC_xor,
      toC_two_pow ⟨k.toNat - 3, hk⟩, add_assoc]
    congr 1
    simp only [frameSum, List.map_cons, List.sum_cons, dite_eq_left hk]

theorem frameSum_eq (w : List ℤ) (hw : ∀ k ∈ w, k.toNat - 3 < 12) :
    frameSum w = toC (Model.frameCode w) := by
  rw [Model.frameCode, toC_foldl_frame w hw, toC_zero, zero_add]

theorem toC_one_eq : toC 1 = basisC 0 := toC_two_pow 0

end CFSG.Monster.B.Rep4371
