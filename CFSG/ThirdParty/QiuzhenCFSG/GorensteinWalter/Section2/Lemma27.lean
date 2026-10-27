module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970API
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma23Core
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27TwoCoreTrivial
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27PiCentralizes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorCentralizes
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorInPiCompl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27ComponentLayer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27PiCoreInversion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorLePiCompl
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27CommutatorNotLeFU
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Solvable
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Theorem26

namespace CFSG
end CFSG
open CFSG

/-!
# Lemma 2.7 (Bender, "Finite Groups with Dihedral Sylow 2-Subgroups")

Pinned statement (verbatim from `tasks/gw-lemma27.md`).  The owner imports
the acyclic Theorem 2.6 module directly; the three conjuncts are proved in
the lower leaf modules and assembled here.
-/

namespace CFSG.GorensteinWalter

universe u

noncomputable section

open scoped Pointwise

/-! ## Pinned statement -/

public theorem lemma_2_7
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G) (M : Subgroup G)
    (hM : Lemma27Hypothesis c M) :
    let π := primesOfOrder (fittingSubgroupOf c.Hhat)
    let Fπ' := piCoreOf (fittingSubgroupOf M) πᶜ
    ⁅M, Subgroup.zpowers c.t⁆ ≤ Fπ' ∧
      ¬ ⁅(c.S : Subgroup G), c.U⁆ ≤ c.FU ∧
        IsSolvable M := by
  classical
  let π := primesOfOrder (fittingSubgroupOf c.Hhat)
  let Fπ' := piCoreOf (fittingSubgroupOf M) πᶜ
  have hFirst : ⁅M, Subgroup.zpowers c.t⁆ ≤ Fπ' :=
    lemma_2_7_commutator_le_piCore_compl hmin c M hM
  constructor
  · exact hFirst
  · constructor
    · exact lemma_2_7_commutator_S_U_not_le_FU hmin c M hM
    · exact isSolvable_of_Lemma27Hypothesis hmin c M hM

end

end CFSG.GorensteinWalter
