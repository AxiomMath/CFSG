module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamDefs
public import CFSG.Sporadic.He.Setup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)

theorem sevenRankFree_of_noSevenCent {J : Type} [Group J] [Finite J] (h : NoSevenCent J) :
    SevenRankFree J := by
  intro X R hX hXea hX9 hR hRne _ hRcent
  exact h X R hX hXea hX9 hR.isPGroup hRne hRcent

theorem sevenRankFree_of_two_le_pRank {J : Type} [Group J] [Finite J]
    (h : 2 ≤ CFSG.Open.pRank 7 (⊤ : Subgroup J)) : SevenRankFree J := by
  intro X R _ _ _ hR _ hRcyc _
  let P : Sylow 7 J :=
    ⟨R, hR.isPGroup, fun {Q} hQ hRQ => hR.eq_of_le hRQ le_top hQ⟩
  have hPcyc : IsCyclic ↥(P : Subgroup J) := hRcyc
  have hle : CFSG.Open.pRank 7 (⊤ : Subgroup J) ≤ 1 := by
    refine CFSG.SectionRank.pRank_le (by norm_num) ?_
    intro E _ hE
    have hEpg : IsPGroup 7 E :=
      IsPGroup.of_exponent_dvd_pow (n := 1) (by
        rw [pow_one]
        exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
          apply Subtype.ext
          simpa using hE.2 (x : J) x.2)
    obtain ⟨Q, hEQ⟩ := hEpg.exists_le_sylow
    haveI : IsCyclic ↥(Q : Subgroup J) := (Sylow.equiv P Q).isCyclic.mp hPcyc
    haveI : IsCyclic ↥E := Subgroup.isCyclic_of_le hEQ
    have hcard : Nat.card ↥E ∣ 7 := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        apply Subtype.ext
        simpa using hE.2 (x : J) x.2
    have := Nat.le_of_dvd (by norm_num) hcard
    simpa using this
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
