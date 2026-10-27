module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.Adapters.StatedSLPerfect

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W]

theorem s16h_sl28_commSub_commSub_self [Finite W] {L : Subgroup (MulAut W)}
    (h : s16h_H5RowSL2 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L) 3) :
    commSub (commSub ⊤ L) L = commSub ⊤ L := by
  obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h.1
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hK4 : 4 ≤ Nat.card K := by rw [hKcard]; norm_num
  haveI : Group.IsPerfect ↥(StatedSL 2 K) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_two_of_four_le_card hK4
  have hperf : Group.IsPerfect ↥L :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact s16jp_commSub_commSub hperf (Y := ⊤) (fun l _ y _ => Subgroup.mem_top (l y))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
