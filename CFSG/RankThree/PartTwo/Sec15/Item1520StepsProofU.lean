module

public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec15.Item1520StepsProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

theorem step1521U_of_ctx (hU : Step1521UConj)
    (hnorm : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → ∀ Y, Ctx1514 A (lB A) c L Y → Claim153Normal A (lB A))
    (hgen : Step1521Gen) : Step1521U := by
  intro G _ _ A c L h Y hctx p P hP X hX hPX hP0
  exfalso
  obtain ⟨Y', P', U, hctx', hP', hU1, hU2, hAU, hPU, hYU⟩ :=
    hU G A c L h Y hctx p P hP X hX hPX hP0
  have hloc : IsPLocal 2 (Subgroup.normalizer (U : Set G)) := ⟨U, hU1, hU2, rfl⟩
  obtain ⟨M, hUM, hM⟩ := Finite.exists_le_maximal (p := IsPLocal 2) hloc
  have hMmax : IsMaximalTwoLocal M :=
    ⟨hM.prop, fun H hMH hH => (not_le_of_gt hMH) (hM.2 hH hMH.le)⟩
  have hMYA : M ∈ maximalTwoLocalsContaining ((Y' ⊔ A : Subgroup G) : Set G) :=
    ⟨hMmax, fun x hx => hUM (sup_le hYU hAU hx)⟩
  have hPY : P' ≤ Subgroup.normalizer (Y' : Set G) :=
    hPU.trans (hUM.trans (hnorm G A c L h Y hctx Y' hctx'.mem_y0Star M hMYA))
  have hLN : L ≤ Subgroup.normalizer (Y' : Set G) :=
    (hgen G A c L h Y' hctx' p P' hP' hPY).trans
      (sup_le hPY (inf_le_left.trans Subgroup.le_normalizer))
  exact hctx'.not_le_normalizer h.mem_thetaComponentsAt hLN

theorem step1521U_of (hU : Step1521UConj) (hnorm : Claim153NormalR) (hgen : Step1521Gen) :
    Step1521U :=
  step1521U_of_ctx hU (by intro G _ _ A c L h _ _; exact hnorm G A c L h) hgen

end CFSG.RankThree.PartTwo.Sec15
