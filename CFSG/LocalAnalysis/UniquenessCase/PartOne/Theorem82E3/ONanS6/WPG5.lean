module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPF9I

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPK3H
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONanS6.WPH7

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K3)
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

theorem exists_E27_frame' (c : Ctx82E3 D)
    (hON : UCK.ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar) (h7 : D.sig = {7})
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M)
    (hNZ : Subgroup.normalizer ((zSub P c.L : Subgroup G) : Set G) ≤ D.M) :
    ∃ A : Subgroup G, CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 27 ∧
      zSub P c.L ≤ A ∧ A ≤ P ⊓ c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcardQ : Nat.card ↥(P ⊓ c.L) = 3 ^ 5 := card_inf_L_of_onan_wPH7 c hON hP
  have hZcard : Nat.card ↥(zSub P c.L) = 3 := c.card_inf_centralizer_of_onan hON hP
  have hex : ∃ a : G, a ∈ P ⊓ c.L ∧ a ∉ zSub P c.L := by
    by_contra h
    push Not at h
    have hle : P ⊓ c.L ≤ zSub P c.L := fun a ha => h a ha
    have hdvd : Nat.card ↥(P ⊓ c.L) ∣ Nat.card ↥(zSub P c.L) := Subgroup.card_dvd_of_le hle
    rw [hcardQ, hZcard] at hdvd
    norm_num at hdvd
  obtain ⟨a, haQ, haZ⟩ := hex
  obtain ⟨A, hAea, hA27, -, hAPL, hZA⟩ :=
    exists_elemAbelian_27_of_mem_inf_L K3_holds' c hON hP haQ haZ
  exact ⟨A, hAea, hA27, hZA, hAPL⟩

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
