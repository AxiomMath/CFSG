module

public import CFSG.Quasithin.Recognition.F112Crit.OddThreeFour
public import CFSG.Quasithin.Recognition.F112Crit.R1QPlusRed

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.MS93 (oddGen)

theorem s3OddB_three : S3OddB (· = 3) := by
  intro G _ _ L1 L2 S hH hs hS3 hBig hL2 _ hb3
  have hL : IsRankOneListed (oTwoQuot ↥L2) := hH.1.h2.listed
  have hns : ¬ Group.IsSolvable (oTwoQuot ↥L2) := fun h =>
    VBig.not_isSolvable hL hBig (isSolvable_vertex_of_oTwoQuot h)
  obtain ⟨n, i, -, hK, htype⟩ := exists_isBenderQuot_of_listed hL hns
  have h65 : 65 ≤ (2 ^ n) ^ i + 1 := htype.resolve_left fun h => hL2 ⟨n, h.2⟩
  have hcr := hs.toCritAmalgam
  have hcard := card_oTwoQuot_of_vS3 hS3
  have hX := hs.isLocalRegGrp (oddGen_inf_borelOf_le hs.hyp (Or.inl hcard))
  rw [relIndex_borelOf_eq_three hs.hyp hcard] at hX
  exact false_of_three hcr hb3 (hs.benderLocal hK) (hX.isLocalReg hcr)
    (by rw [hs.card_nbrs_γ₀ hK]; omega)

theorem f112R1QPlus_of_center_five (hC : R1QCenter)
    (h5 : S3OddB (5 ≤ ·)) : CFSG.Quasithin.H13.F112R1QPlus :=
  f112R1QPlus_of_parts hC s3OddB_three h5

end CFSG.Quasithin.F112Crit

end
