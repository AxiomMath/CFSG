module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Rep
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.LeviSec
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Numerics
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Transfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KMinDegLow.Shapes

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartTwo.Sec4.Ronan148V
open MinDegLow Subgroup

theorem kMinDegLow_of
    (hSz : ∀ (X : Type) [Group X] (f : ℕ), IsSz X f → Nat.card X = CFSG.Open.ordSuzuki (2 ^ f))
    (hG2 : ∀ (X : Type) [Group X] (f : ℕ), IsG2 X f → IsSimpleGroup X)
    (h3D4 : ∀ (X : Type) [Group X] (f : ℕ), Is3D4 X f → IsSimpleGroup X)
    (h2F4 : ∀ (X : Type) [Group X] (f : ℕ), LieModel X .twistedF4 0 2 f → IsSimpleGroup X) :
    KMinDegLow := by
  intro G _ _ L K P n hL hK hP hN hn
  obtain ⟨T, _, _, hTL, hT⟩ := exists_leviData_sec hSz hP.2.1 hN hn
  haveI := hT.simple
  have hKq : CFSG.Open.IsQuasisimple (Bar2 K) := hK.2.2
  haveI := nontrivial_of_isQuasisimple hKq
  suffices h : n + 2 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.dMinDeg (Bar2 K) by omega
  apply le_dMinDeg
  intro d f hf
  rcases shape_cases hG2 h3D4 h2F4 hL with hX | ⟨K₁, K₂, hsup, hcomm, h₁, h₂, hfac⟩
  · obtain ⟨⟨ψ, hψ⟩, hcen⟩ := exists_surjective_single hK hX
    have hTS : IsSec T (Bar2 L ⧸ center (Bar2 L)) :=
      hTL.quotient_of_isSolvable (not_isSolvable_of_isSimpleGroup hT.nonab)
        (Group.isSolvable_of_comm fun a b => Subtype.ext (mem_center_iff.mp b.2 a))
    obtain ⟨m, hm2, -, ⟨t, ht⟩, -⟩ := hT.bound
    obtain ⟨s, hs⟩ := exists_orderOf_eq_of_isSec hTS t
    obtain ⟨g, hg⟩ := exists_orderOf_eq_of_quotient hKq ψ hψ hcen f hf s
    have hd := ht d g (hg.trans hs)
    nlinarith
  · obtain ⟨K', hK', ψ, hψ⟩ := exists_surjective_sup hK hsup hcomm h₁ h₂
    obtain ⟨K'', hK'', hTK''⟩ := isSec_quotient_center_of_sup hT.nonab hsup hcomm hTL
    have hq : ∀ J ∈ ({K₁, K₂} : Set (Subgroup (Bar2 L))), CFSG.Open.IsQuasisimple ↥J := by
      rintro J (rfl | rfl)
      exacts [h₁, h₂]
    have hcen : center (↥K' ⧸ center ↥K') = ⊥ := center_quotient_center_eq_bot (hq K' hK')
    have hcard := hTK''.card_dvd
    rcases hfac with ⟨n₀, hn₀, hfac⟩ | hfac
    · have hnn₀ : n ≤ n₀ := by
        rcases hfac K'' hK'' with hA | hA
        · exact le_of_dvd_card_sz hSz hT hn hA hn₀ hcard
        · exact le_of_dvd_card_l2 hT hn hA hn₀ hcard
      have hS : LeviData (↥K' ⧸ center ↥K') n₀ := by
        rcases hfac K' hK' with hA | hA
        · exact leviData_sz hSz hA hn₀
        · exact leviData_l2 hA hn₀
      obtain ⟨m₀, hm₀, -, ⟨t₀, ht₀⟩, -⟩ := hS.bound
      obtain ⟨g, hg⟩ := exists_orderOf_eq_of_quotient hKq ψ hψ hcen f hf t₀
      have hd := ht₀ d g hg
      nlinarith
    · have hn9 : n ≤ 9 := le_nine_of_dvd_card_u3_three hT hn (hfac K'' hK'') hcard
      obtain ⟨t₀, ht₀⟩ := exists_orderOf_u3_three (hfac K' hK')
      obtain ⟨g, hg⟩ := exists_orderOf_eq_of_quotient hKq ψ hψ hcen f hf t₀
      have hd := ht₀ d g hg
      omega

end CFSG.LocalAnalysis.UniquenessCase.UC22
