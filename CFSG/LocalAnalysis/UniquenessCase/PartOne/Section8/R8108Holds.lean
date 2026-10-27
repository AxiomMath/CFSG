module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.CentralizerPSubQ108Final
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.NormalizerSylow108

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (R8_108 IsSL3Four)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem r8_108_holds
    (hS : Standing4 G) (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hC : CFSG.Yardstones.Mf4cdcdf2e013.TheoremCAt S.M)
    (hnot : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hSE : StronglyEmbeddedFive) :
    R8_108 (CFSG.LocalAnalysis.UniquenessCase.UC6.dataOfSetup4 hS hU S) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro L hL hSL hclass
  obtain ⟨L', hne, hset⟩ := hclass
  have hLL' : L ≠ L' := fun h => hne h.symm
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf 3 S.M
  let Q : Subgroup G := (P ⊓ L) ⊔ (P ⊓ L')
  have hfacts := q8108_explicit hS hU S hMS hC hnot hSE hL hset hne hSL hP
  dsimp only at hfacts
  obtain ⟨-, hQP, -, -, -, -, -, -, hΓ⟩ := hfacts
  have hA : ∀ A : Subgroup G, A ≤ P → Nat.card A = 3 → A ⊓ Q = ⊥ →
      Subgroup.centralizer (A : Set G) ≤ S.M := by
    intro A hAP hAcard hAQ
    exact centralizer_le_of_order_three_of_P_sub_Q_of_ne hS hU S hMS hC hnot hSE
      hL hset hSL hP hAP hAcard hAQ hLL'
  have hNS : Subgroup.normalizer (P : Set G) ≤ S.M :=
    normalizer_sylow_le_8108 hS hU S hMS hC hnot hSE hL hset hne hSL hP
  exact r8_108_of_gamma_and_normalizer hS hU S P Q hP (by simpa [Q] using hΓ) hA hNS
    L hL hSL ⟨L', hne, hset⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
