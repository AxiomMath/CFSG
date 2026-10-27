module

public import CFSG.Quasithin.Vol2.Ch5Sec1Basic
public import CFSG.Quasithin.H13.StatementsL3S
public import CFSG.Quasithin.Background.E2TwoLieQuotDetect

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Hyp5_0_1

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G} {n : ℕ}

theorem not_isSolvable_and_sqtk_of_lie (h : Hyp5_0_1 G T M L n) {H : Subgroup G}
    (hH : IsHStar T M H) (hq : ∃ K ∈ cComp H, E2.HasE22LieQuot K) :
    ¬ Group.IsSolvable ↥H ∧ SQTKGroup ↥H := by
  obtain ⟨K, hK, -⟩ := hq
  refine ⟨fun hs => not_isSolvable_of_mem_cComp hK ?_, ?_⟩
  · have := hs
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (le_of_mem_cComp hK))
      (Subgroup.inclusion_injective _)
  · obtain ⟨hk, hsq⟩ := isSQTKSub_of_inH h.qtke h.simple h.nonabelian hH.1
    exact ⟨hsq, hk⟩

end Hyp5_0_1

theorem stmt5_2_3_of_S (h331 : Stmt3_3_1) (hE22 : E2.E22StatementC) (h : Stmt5_2_3S) :
    Stmt5_2_3 := by
  intro G _ _ T M L H V m hsimple hnab hqtke hT hM hTM hLmax hLf hLM hMN h2m hlie hH hn hV
    hVred hVL
  have h501 : Hyp5_0_1 G T M L m :=
    ⟨hsimple, hnab, hqtke, hT, hM, hTM, hLmax, hLf, hLM, hMN, h2m, hlie⟩
  obtain ⟨hmp, hns⟩ := h501.minParabolic_of_isHStar h331 hH
  obtain ⟨-, hsq⟩ := hns hn
  exact h G T M L H V m hsimple hnab hqtke hT hM hTM hLmax hLf hLM hMN h2m hlie hH
    (E2.exists_hasE22LieQuot_of_one_lt_nParam hE22 hmp hsq hn) hV hVred hVL

end CFSG.Quasithin.H13
