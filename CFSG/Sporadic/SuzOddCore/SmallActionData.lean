module

public import CFSG.Sporadic.SuzOddCore.Perms

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2

theorem CTUC_Suz_small_action_data :
    mtxHeader suzP1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M1Text).length = 1782 ∧
    mtxHeader suzP1782M2Text = [12, 1, 1782, 1] ∧ (mtxImages suzP1782M2Text).length = 1782 ∧
    mtxHeader suzd2P1782M1Text = [12, 1, 1782, 1] ∧ (mtxImages suzd2P1782M1Text).length = 1782 ∧
    Rep 1782 (mtxArr suzP1782M1Text) suzB0 ∧ Rep 1782 (mtxArr suzP1782M2Text) suzB1 ∧
    Rep 1782 (mtxArr suzd2P1782M1Text) suzV ∧
    suzM = Subgroup.closure {suzB0, suzB1} ∧
    suzT = Subgroup.closure (insert suzV (suzM : Set (Equiv.Perm (Fin 1782)))) ∧
    suzP = Subgroup.closure {suzA0, suzA1} ∧ certChain.originalSubgroup = suzP ∧
    certChain.base.toList = [0, 1, 2, 3, 4, 5] ∧
    (∀ i : Fin certChain.originalCount,
      certChain.original.get i = ![suzA0, suzA1] (Fin.cast certChain_originalCount i)) ∧
    (∀ j : Fin certChain.strongCount, Rep 22880 (certArr (j + 2)) (certChain.strong.get j)) ∧
    smallChain.originalSubgroup = suzM ∧ smallChain.base.toList = [0, 1, 2, 3, 4, 8] ∧
    (∀ i : Fin smallChain.originalCount,
      smallChain.original.get i = ![suzB0, suzB1] (Fin.cast smallChain_originalCount i)) ∧
    (∀ j : Fin smallChain.strongCount, Rep 1782 (smallArr (j + 2)) (smallChain.strong.get j)) ∧
    suzPhi = MonoidHom.fst (Equiv.Perm (Fin 22880)) (Equiv.Perm (Fin 1782)) ∧
    (∀ i : Fin certChain.originalCount, suzU.get i = (certChain.original.get i, suzBGen i)) ∧
    (∀ i : Fin certChain.originalCount, suzPhi (suzU.get i) = certChain.original.get i) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5, h6, -⟩ := arrays_check
  refine ⟨h1, h2, h3, h4, h5, h6, decoders_check.1 ▸ rep_b0, decoders_check.2.1 ▸ rep_b1,
    decoders_check.2.2.1 ▸ rep_v, rfl, rfl,
    rfl, certChain_originalSubgroup, certChain_base_toList, certChain_original_eq,
    fun j => ?_, smallChain_originalSubgroup, smallChain_base_toList, smallChain_original_eq,
    fun j => ?_, rfl, suzU_get, fun i => ?_⟩
  · rw [certChain_strong_get]
    exact rep_suzS j.2
  · rw [smallChain_strong_get]
    exact rep_smallArr (by have := lt_of_lt_of_eq j.2 smallChain_strongCount; omega)
  · rw [suzU_get]
    rfl

end CFSG.Sporadic.SuzOddCore
