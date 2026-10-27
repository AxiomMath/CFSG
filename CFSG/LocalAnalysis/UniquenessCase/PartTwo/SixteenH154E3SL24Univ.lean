module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3SL24UnivA
public import CFSG.Milestones.ASVolI.I2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W]

theorem s16h_sl24_univ (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hrow : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ L ⊓ fixV L))
    (hU : ∀ l ∈ L, ∀ u ∈ commSub ⊤ L, l u ∈ commSub ⊤ L) :
    CFSG.ASVolI.ChIJK.IsUniversalCovering
      (CFSG.Quasithin.H13.VolI.resHom L (commSub ⊤ L) hU).range
      ((commSub ⊤ L ⊓ fixV L).subgroupOf (commSub ⊤ L)) := by
  have hperf : Group.IsPerfect ↥L := by
    have hBN := hrow.2
    obtain ⟨K, hKf, hKfin, hKcard, hreal⟩ := hBN
    letI := hKf
    letI := hKfin
    obtain ⟨π, hπ⟩ := hreal
    have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
    haveI : Group.IsPerfect (FFModel.nat (StatedSL 2 K)).Gam :=
      CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
    exact Group.IsPerfect.ofSurjective (f := π) hπ.1
  have hUc : commSub (commSub ⊤ L) L = commSub ⊤ L :=
    s16jp_commSub_commSub hperf (Y := ⊤) (fun l _ y _ => Subgroup.mem_top (l y))
  have hcomm : XMod.commOf ↥L (commSub ⊤ L) = commSub ⊤ L := by
    rw [commOf_eq_commSub, hUc]
  refine ⟨?_, ?_, s16h_sl24_univ_universal hW hrow hZ4 hU⟩
  · exact CFSG.Quasithin.H13.VolI.subgroupOf_le_fixV_resHom_range hU inf_le_right
  · exact CFSG.Quasithin.H13.VolI.commV_resHom_range hU hcomm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
