
module

public import CFSG.Monster.B.TwoA.Co2Inv.Data
public import CFSG.Monster.B.TwoA.Co2Inv.RowsBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.Short
  CFSG.Monster.Visible CFSG.Monster.ScalarKernel CFSG.Monster.VisQuot CFSG.Monster.SpinLattice
  CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census CFSG.Monster.Lifts

attribute [local instance] wLeftAction

theorem cRows_comm : ∀ k < 21, rowsMul (cRows k) (gRows 12) = rowsMul (gRows 12) (cRows k) := by
  decide +kernel

theorem cRows_fix_w : ∀ k < 20, Native.actD 22 (cRows k) 31 = 31 := by decide +kernel

theorem gRows12_sq : rowsMul (gRows 12) (gRows 12) = idRows := by decide +kernel

theorem gRows12_one : (gRows 12)[1]! = 12317 := by decide +kernel

@[expose] def bCN (l : ℤ) : C := if h : 3 ≤ l ∧ l ≤ 14 then bC ⟨l.toNat - 3, by omega⟩ else 0

@[expose] def wordC : List ℤ → C
  | [] => 0
  | l :: w => bCN l + wordC w

theorem frameWordQ_sign : ∀ w : List ℤ, (∀ l ∈ w, 3 ≤ l ∧ l ≤ 14) →
    frameWordQ w = QuotientGroup.mk (gO (wordC w))
  | [], _ => by
    rw [frameWordQ, wordC, gO_zero, QuotientGroup.mk_one]
  | l :: w, hw => by
    have hl := hw l List.mem_cons_self
    rw [frameWordQ, frameWordQ_sign w (fun l' h => hw l' (List.mem_cons_of_mem _ h)), wordC,
      gO_add, QuotientGroup.mk_mul, frameQ_sign (by omega) (by omega), bCN, dite_eq_left hl]

theorem signRecords : ∀ j : ℕ, ∀ hj : j < 11,
    (genRecord ⟨12 + j, by omega⟩).kind = .codeSign ∧
      ∀ l ∈ (genRecord ⟨12 + j, by omega⟩).word, 3 ≤ l ∧ l ≤ 14 := by decide +kernel

theorem alpha_sign (j : Fin 11) : alpha ⟨12 + j, by omega⟩ =
    QuotientGroup.mk (gO (wordC (genRecord ⟨12 + j, by omega⟩).word)) := by
  unfold alpha
  rw [(signRecords j j.2).1]
  exact frameWordQ_sign (genRecord ⟨12 + j, by omega⟩).word (signRecords j j.2).2

@[expose] def signMasks : List ℕ :=
  [255, 3855, 61455, 983055, 15728655, 10928140, 8237332, 6996160, 13017248, 13421568, 11184640]

theorem wordC_eq_bvec : ∀ j : Fin 11,
    ((wordC (genRecord ⟨12 + j, by omega⟩).word : C) : Fin 24 → ZMod 2) =
      bvec 24 (signMasks.getD j 0) := by decide +kernel

theorem signMasks_ceq : ∀ j : Fin 11,
    bvec 24 (signMasks.getD j 0) 0 = bvec 24 (signMasks.getD j 0) 1 := by
  decide +kernel

@[expose] def signVec (j : Fin 11) : Fin 24 → ZMod 2 := bvec 24 (signMasks.getD j 0)

@[expose] def dualMasks : List ℕ := [28, 268, 4108, 65548, 69905, 9, 12, 92, 60, 1292, 780]

@[expose] def dualMat : Matrix (Fin 11) (Fin 24) (ZMod 2) :=
  Matrix.of fun k i => bvec 24 (dualMasks.getD k 0) i

theorem dualMat_signVec : ∀ j : Fin 11, dualMat.mulVecLin (signVec j) = Pi.single j 1 := by
  decide +kernel

theorem linearIndependent_signVec : LinearIndependent (ZMod 2) signVec := by
  refine LinearIndependent.of_comp dualMat.mulVecLin ?_
  have : dualMat.mulVecLin ∘ signVec = ⇑(Pi.basisFun (ZMod 2) (Fin 11)) := by
    funext j
    rw [Function.comp_apply, dualMat_signVec, Pi.basisFun_apply]
  rw [this]
  exact (Pi.basisFun (ZMod 2) (Fin 11)).linearIndependent

theorem span_signVec : Submodule.span (ZMod 2) (Set.range signVec) = Ceq := by
  have hle : Submodule.span (ZMod 2) (Set.range signVec) ≤ Ceq := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, mem_Ceq]
    refine ⟨?_, signMasks_ceq j⟩
    rw [signVec, ← wordC_eq_bvec j]
    exact (wordC _).2
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [finrank_span_eq_card linearIndependent_signVec, Fintype.card_fin, finrank_Ceq]

theorem cRows_eq_candRows : ∀ k < 21, cRows k = candRows[k]! := by decide +kernel

end CFSG.Monster.B.TwoA.Co2Inv
