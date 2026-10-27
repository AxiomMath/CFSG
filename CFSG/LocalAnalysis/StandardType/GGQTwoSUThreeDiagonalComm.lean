module

public import CFSG.ClassicalGroups.Unitary.SUThreeTwoDiagonalCommutator
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeBlock
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermUniBlocksDiag
import CFSG.LocalAnalysis.StandardType.GGTorusGenRkComp

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.ClassicalGroups.SpecialLinear
  CFSG.LocalAnalysis.ComponentInitial LineU
open scoped commutatorElement MatrixGroups

theorem GGSecFiveBPermUniLFrame.map_blockSU_triple_le_ggBlockComm
    {G : Type} [Group G] {p n : ℕ} {K : Type} [Field K] {Bs X : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Equiv.Perm (Fin n)}
    {σ : ↥(unitarySU 2 1 K n) →* G} {χ : Multiplicative (ZMod p) →* Kˣ}
    (hF : GGSecFiveBPermUniLFrame Bs X eta π σ χ) (h : UnitaryFieldData 2 1 K)
    (hp : p.Prime) (S : Finset (Fin n)) (hS : S.card = 3) :
    (TableBUE.blockSU (K := K) (n := 1) S).map σ ≤
      ggBlockComm Bs eta (π '' (S : Set (Fin n))) := by
  have hK : Nat.card K = 4 := by simpa using h.card
  have hsmall : unitarySU 2 1 K S.card ≤
      ⁅unitarySU 2 1 K S.card, (diagGLHom S.card K).range⁆ := by
    have heq : ⁅unitarySU 2 1 K S.card, (diagGLHom S.card K).range⁆ =
        unitarySU 2 1 K S.card := by
      rw [hS]
      exact commutator_unitarySU_three_two_diagonal h
    rw [heq]
  exact hF.map_blockSU_le_ggBlockComm_of_le_commutator
    (hF.surjective_of_card_eq_four hK hp)
    (TableBUE.map_blockSU_le_commutator_diagGLHom_range h S hsmall)

end CFSG.StandardType

end
