module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPStA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPStB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5Cfg
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5JPBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.ASVolI.ChH

variable {W : Type} [CommGroup W]

theorem s16jp_row_St8 [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (h : s16h_H5RowSt8 L (commSub ⊤ L) (commSub ⊤ L ⊓ fixV L))
    (hirr : commSub ⊤ L ∈ irrSet L) : commSub ⊤ L ⊓ fixV L = ⊥ := by
  obtain ⟨π, β, hπ, hβs, hβk, hβe⟩ := s16jp_st_section hW2 h.1 hirr h.2
  obtain ⟨ι, ρ, hρι, hρQ, hι, hρ⟩ := CFSG.ASVolI.as_H_6_3.1
  exact s16jp_eq_bot_of_regular_summand (W := W) hW2 (U := commSub ⊤ L)
    (Z := commSub ⊤ L ⊓ fixV L)
    (s16jp_commSub_stable (L := L) (Y := ⊤) (fun _ _ _ _ => Subgroup.mem_top _))
    hirr.1 inf_le_left (fun z hz l hl => mem_fixV.1 hz.2 l hl)
    π hπ adjAmbAct Adj3 β hβs hβk hβe ι ρ hρι hρQ hι hρ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
