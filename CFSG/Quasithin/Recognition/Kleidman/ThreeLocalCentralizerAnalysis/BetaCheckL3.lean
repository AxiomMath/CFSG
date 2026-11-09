module

public import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaModels
import CFSG.Quasithin.Recognition.Kleidman.ThreeLocalCentralizerAnalysis.BetaTransport
import CFSG.LinearAlgebra.F2SL3Code

public section

namespace CFSG.Quasithin.Kleidman.ThreeLocal

open Matrix MatrixGroups

@[expose] def c0L3 : SL(3, ZMod 2) := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

private def c0L3c : CFSG.F2NatMat.SL3c := ⟨⟨275, by norm_num⟩, by decide⟩

private theorem d8Rels_eq : d8Rels = [[(1, true), (1, true)], [(3, true), (3, true)],
    [(2, true), (2, true)], [(0, true), (0, true), (0, true)],
    [(0, true), (2, true), (0, false), (2, true)], [(0, true), (1, true), (0, false), (1, true)],
    [(1, true), (3, true), (1, true), (3, true)],
    [(2, true), (1, true), (2, true), (3, true), (1, true)],
    [(2, true), (1, true), (3, true), (2, true), (1, true)],
    [(0, true), (3, true), (0, false), (3, true)]] := by decide

private theorem a2Rels_eq : a2Rels = [[(6, false), (2, true), (0, false), (6, false)],
    [(6, true), (0, true), (6, true), (2, true)], [(6, false), (6, false), (0, false), (2, true)],
    [(6, false), (3, true), (6, false), (3, true), (0, false)],
    [(6, false), (1, true), (6, false), (1, true), (6, false), (1, true)],
    [(2, true), (6, true), (2, true), (6, false)], [(6, true), (3, true), (0, true), (6, true), (3, true)]] := by
  decide

attribute [local instance 2000] Finset.decidableDforallFinset Finset.decidableDExistsFinset
  List.decidableBAll List.decidableBEx in
set_option maxRecDepth 100000 in
set_option synthInstance.maxSize 2000 in
set_option synthInstance.maxHeartbeats 400000 in
private theorem betaCheck_L3c : BetaCheck CFSG.F2NatMat.SL3c c0L3c := by
  unfold BetaCheck
  simp only [normSet_eq_all, d8Rels_eq, a2Rels_eq, List.forall_mem_cons, List.not_mem_nil,
    IsEmpty.forall_iff, forall_const, and_true, evalWord, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, betaTup, Matrix.cons_val, ite_true, ite_false,
    Bool.false_eq_true, inv_one, one_mul, mul_one]
  decide +kernel

private theorem equiv_c0L3c : CFSG.F2NatMat.SL3c.equiv c0L3c = c0L3 := by
  rw [CFSG.F2NatMat.SL3c.equiv_apply]
  exact Subtype.ext (by decide)

theorem betaCheck_L3 : BetaCheck SL(3, ZMod 2) c0L3 := by
  rw [← equiv_c0L3c]
  exact BetaCheck.of_mulEquiv CFSG.F2NatMat.SL3c.equiv.symm
    (by rw [MulEquiv.symm_apply_apply]; exact betaCheck_L3c)

end CFSG.Quasithin.Kleidman.ThreeLocal
