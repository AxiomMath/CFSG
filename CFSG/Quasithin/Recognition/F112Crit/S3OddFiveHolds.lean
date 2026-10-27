module

public import CFSG.Quasithin.Recognition.F112Crit.S3OddFive
public import CFSG.Quasithin.Recognition.F112Crit.OddFiveTrich
public import CFSG.Quasithin.Recognition.F112Crit.R1QPlusRed

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

theorem s3OddB_five : S3OddB (5 ≤ ·) := by
  intro G _ _ L1 L2 S hH hs hS3 hBig hL2 hb hb5
  have hL : IsRankOneListed (oTwoQuot ↥L2) := hH.1.h2.listed
  have hns : ¬ Group.IsSolvable (oTwoQuot ↥L2) := fun h =>
    VBig.not_isSolvable hL hBig (isSolvable_vertex_of_oTwoQuot h)
  exact hs.false_of_odd_five_of_trich hS3 hL hns hb hb5 fun μ' hμ' hne =>
    hs.pCoreOf_inf_trichotomy hS3 hL hns CosetGeom.vtype_γ₁
      (CosetGeom.mem_nbrs_symm CosetGeom.adj_γ₀_γ₁) hμ' hne

end CFSG.Quasithin.F112Crit

end
