module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec17

variable {G : Type} [Group G] [Finite G]

theorem false_of_ctx1514_of_sec17Std {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}
    (h : Sec17Std G A c L Y₀) {Y : Subgroup G} (hctx : Ctx1514 A (lB A) c L Y) : False := by
  have hY : Y = Y₀ := h.eq_of_mem_y0Star hctx.mem_y0Star
  exact hctx.not_le (hY ▸ h.le_y0)

theorem step1519S17 : Step1519S17 :=
  fun _ _ _ _ _ _ _ hs _ hctx => (false_of_ctx1514_of_sec17Std hs hctx).elim

theorem step1521S17 : Step1521S17 :=
  fun _ _ _ _ _ _ _ hs _ hctx _ _ _ _ _ => (false_of_ctx1514_of_sec17Std hs hctx).elim

theorem step1522S17 : Step1522S17 :=
  fun _ _ _ _ _ _ _ hs _ hctx _ _ _ => (false_of_ctx1514_of_sec17Std hs hctx).elim

end CFSG.RankThree.PartTwo.Sec15
