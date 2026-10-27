module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Step1
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Step2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23NeO2Step3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem c23ne_false_of_cond {M V₀ V N₁ N₂ Y : Subgroup G} {g : G}
    (h : C23NeO2 M V₀ V N₁ N₂ Y g) : False := by
  obtain ⟨h1, -⟩ := c23ne_step1 h (c23ne_step0_le h) (c23ne_step0_cent h)
  obtain ⟨h1', h1blk'⟩ := c23ne_step1' h (c23ne_step0_le' h) (c23ne_step0_cent' h)
  exact c23ne_step3 h h1 (c23ne_step2 h (c23ne_step0_comm' h) h1blk') h1'

theorem c23ne_false_of_inCalO2 {M V₀ V N₁ N₂ Y : Subgroup G} {n : ℕ} {g : G} (hn : n ≤ 2)
    (hP : C23NePair M V₀ V N₁ N₂ Y)
    (hP' : C23NePair (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g)
      (conjSubgroup N₁ g) (conjSubgroup N₂ g) (conjSubgroup Y g))
    (h : InCalO2 n M V₀ V g) : False := by
  unfold InCalO2 InCalO OFirst ODual at h
  obtain ⟨⟨⟨hVgM, hmUg, -⟩, ⟨hVMg, hmB, -⟩⟩, -⟩ := h
  exact c23ne_false_of_cond ⟨hP, hP', hVgM, hVMg, hmUg.trans hn, hmB.trans hn⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
