module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Good
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.QuasithinUnique.CatalogBridgeLinear
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvableQ StronglyEmbeddedThree Sec7Core4)

variable {G : Type} [Group G] [Finite G]

theorem kf7Use_dataOfSetup (hSQ : StronglyEmbeddedSolvableQ) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G) :
    KF7Use (PartTwo.Three.dataOfSetup hS S) := by
  intro p hp H hH
  obtain ⟨hpp, hp2, hsp, htop, hHM, hrank⟩ := hH
  haveI : Fact p.Prime := ⟨hpp⟩
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpp hp2 hsp
    (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hk : k.Config H := ⟨htop, hHM, hrank⟩
  by_cases hp3 : p = 3
  · exact Or.inl (k.kInputThree hp3 hK3 hk).2.2.2
  have h5 : 5 ≤ k.p := Nat.Prime.five_le_of_ne_two_of_ne_three hpp hp2 hp3
  have hno : k.KIDExcluded := k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper htop
  rcases hSQ k.p hpp h5 _
      (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH (CFSG.pPrimeCore k.p ↥H))
      (CFSG.pPrimeCore_quotient_eq_bot hpp) (k.two_le_pRank_quotient_pPrimeCore hk) _
      (k.isStronglyPEmbedded_map_quotient_pPrimeCore hk) (hno H hk (k.step75 h5 hSE)) with
    hsol | ⟨hp5, -, -, hY⟩
  · exact Or.inl hsol
  refine Or.inr ⟨hp5, fun Y hYN hYp T _ hT f hf => ?_⟩
  haveI : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hYp
  haveI : Group.IsPerfect T := Group.IsPerfect.ofSurjective hf
  haveI : IsSimpleGroup T := hT
  haveI : Finite T := Finite.of_surjective f hf
  have hnab : ∃ a b : T, a * b ≠ b * a := by
    by_contra hc
    haveI : IsMulCommutative T := ⟨⟨fun a b => not_not.mp fun h => hc ⟨a, b, h⟩⟩⟩
    exact false_of_nontrivial_of_subsingleton T
  exact CFSG.QuasithinUnique.nonempty_mulEquiv_alternatingGroup_five_of_card_sixty
    (hY Y hYN hYp ↥Y T (MonoidHom.id ↥Y) Function.injective_id hT hnab f hf)

end CFSG.LocalAnalysis.UniquenessCase.UC22
