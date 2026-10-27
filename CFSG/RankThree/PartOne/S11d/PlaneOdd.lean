module

public import CFSG.RankThree.PartOne.S11d.PlaneCases
public import CFSG.RankThree.PartOne.S11d.OddRank
public import CFSG.RankThree.PartOne.S11d.OddOutPSL2
public import CFSG.RankThree.PartOne.MB3.OddOutLinear
public import CFSG.RankThree.PartOne.MB3.OddOutSymplectic
public import CFSG.RankThree.PartOne.MB3.OddOutOrthogonal

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo PlaneT)
open CFSG.RankThree.PartOne.OutStructure (OutPNice OutPChain)

@[expose] def OddOutGaps : Prop :=
  (∀ (p : ℕ) (X : Type) [Group X] (ℓ f : ℕ), p.Prime → 5 ≤ p → ℓ ≠ 2 →
      StatedClassicalModel X .PSp 2 ℓ f → OutPChain p X) ∧
    (∀ (p : ℕ) (X : Type) [Group X] (f : ℕ), p.Prime → 5 ≤ p →
      ReeTitsModel X .twistedG2 3 f → OutPChain p X)

@[expose] def OddExceptionalOut : Prop :=
  ∀ (p : ℕ) (T : Type) [Group T] (t : StatedLieTag) (ℓ f : ℕ), p.Prime → 5 ≤ p → ℓ.Prime →
    ℓ ≠ 2 → t ∈ chevalleyExceptionalTags → ChevalleyExceptionalModel T t ℓ f → OutPNice p T

@[expose] def OddLiePlaneT : Prop :=
  ∀ (T : Type) [Group T] [Finite T] (t : StatedLieTag) (n ℓ f p : ℕ), p.Prime → 5 ≤ p →
    ℓ.Prime → ℓ ≠ 2 → StatedLieAdmissible t n ℓ f → LieModel T t n ℓ f → PlaneT p T

theorem oddLiePlaneT_of (hGap : OddOutGaps) (hExc : OddExceptionalOut) : OddLiePlaneT := by
  intro T _ _ t n ℓ f p hp hp5 hℓ hℓ2 hadm hmodel
  have hp3 : 3 < p := by omega
  have hp2 : p ≠ 2 := by omega
  rcases hmodel with ⟨ht, hcl⟩ | ⟨hn0, ht, hch⟩ | ⟨hn0, ht, hree⟩ | ⟨hn0, ht, hsz⟩
  · cases t
    ·
      by_cases hn2 : n = 2
      · subst hn2
        exact PlaneCases.planeT_of_outPChain hp
          (OutStructure.outPNice_PSL_two_odd hp hp3 hℓ2 hcl).toChain
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        by_cases hdiag : p ∣ Nat.gcd n (ℓ ^ f - 1)
        · exact fun hrank => (OddRank.not_localRankLeTwo_psl_odd hp hp3 hℓ2 hcl
            (hdiag.trans (Nat.gcd_dvd_left _ _)) (hdiag.trans (Nat.gcd_dvd_right _ _))
            hrank).elim
        · exact PlaneCases.planeT_of_outPChain hp
            (OutStructure.outPNice_PSL_ge_three_odd hp hp2 hn3 hcl hdiag).toChain
    ·
      by_cases hdiag : p ∣ Nat.gcd n (ℓ ^ f + 1)
      · exact fun hrank => (OddRank.not_localRankLeTwo_psu_odd hp hp3 hℓ2 hcl
          (hdiag.trans (Nat.gcd_dvd_left _ _)) (hdiag.trans (Nat.gcd_dvd_right _ _))
          hrank).elim
      · exact PlaneCases.planeT_of_outPChain hp
          (OutStructure.outPNice_PSU_odd hp hcl hdiag).toChain
    ·
      by_cases hn2 : n = 2
      · subst hn2
        exact PlaneCases.planeT_of_outPChain hp (hGap.1 p T ℓ f hp hp5 hℓ2 hcl)
      · have hn3 : 3 ≤ n := by
          have := hcl.1.2.2.1
          omega
        exact PlaneCases.planeT_of_outPChain hp
          (OutStructure.outPNice_PSp_ge_three_odd hp hp2 hn3 hcl).toChain
    · exact PlaneCases.planeT_of_outPChain hp
        (OutStructure.outPNice_POmegaOdd_gen hp hp5 hcl).toChain
    ·
      by_cases hn4 : n = 4
      · subst hn4
        exact PlaneCases.planeT_of_outPChain hp
          (OutStructure.outPChain_POmegaPlus_four_gen hp hp5 hcl)
      · have hn5 : 5 ≤ n := by
          have := hcl.1.2.2
          omega
        exact PlaneCases.planeT_of_outPChain hp
          (OutStructure.outPNice_POmegaPlus_gen_ge_five hp hp5 hn5 hcl).toChain
    · exact PlaneCases.planeT_of_outPChain hp
        (OutStructure.outPNice_POmegaMinus_gen hp hp5 hcl).toChain
    all_goals exact hcl.2.elim
  · exact PlaneCases.planeT_of_outPChain hp (hExc p T t ℓ f hp hp5 hℓ hℓ2 ht hch).toChain
  · cases t
    case twistedG2 =>
      have h3 : ℓ = 3 := hree.1.2.2.2.1
      subst h3
      exact PlaneCases.planeT_of_outPChain hp (hGap.2 p T f hp hp5 hree)
    case twistedF4 => exact absurd hree.1.2.2.2.1 hℓ2
    case Tits => exact absurd hree.1.2.2.2.1 hℓ2
    all_goals
      obtain ⟨-, a, -, hm⟩ := hree
      exact hm.elim
  · exact absurd hsz.1 hℓ2

end CFSG.RankThree.PartOne
