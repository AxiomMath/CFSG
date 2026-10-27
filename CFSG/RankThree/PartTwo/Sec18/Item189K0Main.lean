module

public import CFSG.RankThree.PartTwo.Sec18.Item189K0Closure
public import CFSG.RankThree.PartTwo.Sec18.Item189Steps
public import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Item183OneProofRem
public import CFSG.RankThree.PartTwo.Sec18.Item189K0Member

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

section Certified


variable {G : Type} [Group G] [Finite G] {A M : Subgroup G} {c : G}

theorem k0Setting_of_sec18H (h1812 : Item181_2) (h184 : Item184_1) (h185 : Item185)
    {H : Subgroup G} (hH : Sec18H G A M H c) :
    K0Setting G A (A ⊓ inSubgroup perfectResidual H)
      (lc H c ⊓ Subgroup.normalizer (A : Set G)) M c := by
  have : IsSimpleGroup G := hH.isSimpleGroup
  have hMtop : M ≠ ⊤ :=
    ne_top_of_pCoreOf_ne_bot hH.nonabelian (pCoreOf_ne_bot_of_isMaximalTwoLocal hH.mem_scriptM.1)
  exact
    { plane := planeQ8_of_sec18H h1812 h184 hH
      hAM := sec18Std_le hH.toSec18Std
      hXM := inf_le_right.trans (Rem187QProof.normalizer_le hH.toSec18Std)
      oTwoThree := h185 G A M H c hH
      sec4 := hH.toTheoremFourHyp.sectionFourHyp hMtop
      thm4 := hH.toTheoremFourHyp
      rank := (pRank_le_localRank_of_isTwoLocal Nat.prime_three hH.mem_scriptM.1.1).trans
        hH.toTheoremFourHyp.localRank_three.le }

theorem step189K0_of (h1812 : Item181_2) (h184 : Item184_1) (h185 : Item185) (h188 : Item188)
    (h45 : Sec4.Item4_5) (h46 : Sec4.Item4_6) (hC : Sec13.KS131CenterList46)
    (hSz : KFacts.KPSz) : Step189K0 := by
  intro G _ _ A M H c hH hHyp
  have h := k0Setting_of_sec18H h1812 h184 h185 hH
  have hnc : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥M := fun hcon =>
    hHyp.2.1 (h188 G A M hH.toSec18Std hcon H hHyp.1)
  obtain ⟨K₀, hK₀, h3⟩ := exists_mem_thetaComponentsIn_three_dvd hSz h.sec4 hnc
  have huniq : ∀ K ∈ thetaComponentsIn M, 3 ∣ Nat.card K → K = K₀ := fun K hK h3K =>
    h.eq_of_three_dvd h45 hK hK₀ h3K h3
  have hn := le_normalizer_of_unique hK₀ huniq h3
  rw [h.normalClosureIn_eq h46 hC h45 hK₀ h3 hn]
  exact ⟨hK₀, h.pRank_eq_one h46 hC h45 hK₀ h3 hn⟩

end Certified

end CFSG.RankThree.PartTwo.Sec18
