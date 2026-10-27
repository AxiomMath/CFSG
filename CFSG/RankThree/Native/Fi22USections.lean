module

public import CFSG.RankThree.Native.Fi22UCentralizer
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Foundations.Basic

public noncomputable section

namespace CFSG.RankThree.Native.Fi22U

open CFSG.Monster.B.Fischer CFSG.Fischer CFSG.Assembly.LowTwoRank
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem fi22CentralQuot_not_comm :
    ∃ a b : fi22OuterM ⧸ Subgroup.center fi22OuterM, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := fi22OuterX_not_comm
  refine ⟨fi22CentralQuotEquiv.symm a, fi22CentralQuotEquiv.symm b, fun h => hab ?_⟩
  have := congrArg fi22CentralQuotEquiv h
  simpa using this

instance fi22CentralQuot_isSimpleGroup :
    IsSimpleGroup (fi22OuterM ⧸ Subgroup.center fi22OuterM) :=
  fi22CentralQuotEquiv.isSimpleGroup

theorem fi22OuterM_isQuasisimple : CFSG.IsQuasisimple fi22OuterM :=
  ⟨inferInstance, inferInstance, fi22CentralQuot_not_comm⟩

theorem card_center_fi22OuterM : Nat.card (Subgroup.center fi22OuterM) = 2 := by
  rw [center_fi22OuterM, Nat.card_zpowers, orderOf_fi22OuterZM]

end CFSG.RankThree.Native.Fi22U
