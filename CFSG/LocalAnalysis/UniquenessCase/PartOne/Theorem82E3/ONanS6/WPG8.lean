module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL10
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL11
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPL8b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG
open CFSG.RankThree.LocalRank
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
variable {G : Type} [Group G] [Finite G] {D : Data G}

theorem suzukiComponentStep_input''
    (hK : K332Z3) (hK12 : K12SL) (hK9o : K9J2Order) (hK9out : K9J2Out)
    (hK9f : K9Five) (hK9r : K9G2Rank) (hK2 : K2ONanCentralizer) (hK9b : K9bIn)
    (hK4 : K4) (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hPSz : CFSG.RankThree.PartTwo.KFacts.KPSz)
    (hSzB : Sz.SzBorel) (hSzO : Sz.SzOutOdd) (hSzF : Sz.SzFix) (c : Ctx82E3 D)
    (hON : ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    (P : Subgroup G) (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M)
    (e : G) (hP3 : CFSG.Open.pRank 7 (Subgroup.centralizer ({e} : Set G)) = 1)
    (hZ3 : ∀ J ∈ thetaComponentsAt 3 e, 3 ∣ Nat.card J →
      Nat.card (autThetaQuot (zSub P c.L) J) = 1)
    (he : e ∈ P ⊓ c.L) (he3 : orderOf e = 3) (heZ : e ∉ zSub P c.L) :
    SuzukiComponentStepInput (D := D) c P e := by
  classical
  have he1 : e ≠ 1 := by rintro rfl; rw [orderOf_one] at he3; norm_num at he3
  intro J hJ hntriv
  obtain ⟨f, hSz⟩ := exists_suzukiModel_component hPSz c P hZ3 he1 hJ hntriv
  have hf3 : 3 ≤ f := by
    obtain ⟨-, a, ha, K, -, -, hf, -, -⟩ := hSz
    omega
  rcases lt_or_eq_of_le hf3 with hf | hf
  · exact Or.inl (suzukiBridgeData_of_three_lt' c hON P hP hNZ e hP3 hZ3 hSzF
      he he3 heZ hJ hntriv hSz hf)
  · exact Or.inr (suzukiComponents_centralize_of_f_eq_three' c hON h7 P hP hNZ e hP3 hZ3
      he he3 heZ hJ hntriv hSz hf.symm)

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
