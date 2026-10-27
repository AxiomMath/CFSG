module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1ChoiceDefs
import CFSG.LocalAnalysis.UniquenessCase.UC22P22f
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem r16_47_ne_one_holds (D : Data G) : R16_47_ne_one D := by
  intro V₀ V L hV hS hc hL hU4 hne x hx hSyl h47 hch
  have hP := hS.setting.hyp151.hyp125.pairFacts
  have hzV : x.val ∈ V := x.val_mem
  have hz2 : x.val ^ 2 = 1 := by simpa using hP.elemAbelian.2 x.val hzV
  have hchar : CFSG.QuasithinUnique.CharTwo (centralizer ({x.val} : Set G)) :=
    D.standing.charTwo _ (uc22p22f_isTwoLocal_centralizer hx.ne_one hz2)
  have hQS : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤
      D.T ⊓ centralizer ({x.val} : Set G) :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSyl
  intro c hcmem
  obtain ⟨hcV₀, hcS⟩ := Subgroup.mem_inf.1 hcmem
  have hcH : c ∈ centralizer ({x.val} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact IsElemAbelian.comm hP.elemAbelian hzV (hP.le hcV₀)
  have hcent : c ∈ centralizer
      ((pCoreOf 2 (centralizer ({x.val} : Set G)) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    exact Subgroup.mem_centralizer_iff.1 hcS r (hQS hr)
  exact hchar (Subgroup.mem_inf.2 ⟨hcH, hcent⟩)

theorem r16_47_ne_gap_of_two (D : Data G) (h2 : R16_47_ne_two D) : R16_47_ne_gap D :=
  ⟨r16_47_ne_one_holds D, h2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
