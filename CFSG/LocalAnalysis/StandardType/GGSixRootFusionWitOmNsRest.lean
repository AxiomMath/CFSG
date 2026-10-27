module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNsD4

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Inputs

@[expose] def GGSixRootFusionWitOmPlusQ1D4Small : Prop :=
  GGSixRootFusionWitnessOn fun t n f p =>
    t = .POmegaPlus ∧ n = 4 ∧ ((f = 1 ∧ p = 3) ∨ (f = 2 ∧ p = 5))

theorem ggSixRootFusionWitOmPlusQ1_of_small (h : GGSixRootFusionWitOmPlusQ1D4Small) :
    GGSixRootFusionWitOmPlusQ1 := by
  intro G _ _ p B Bs x L D J t n f ψ hP hctx
  obtain ⟨rfl, hpq⟩ := hP
  have hn4 : 4 ≤ n := hctx.2.2.2.1.1.2.2
  have hf1 : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  rcases Nat.lt_or_ge n 5 with hn | hn
  · obtain rfl : n = 4 := by omega
    rcases Nat.lt_or_ge f 3 with hf | hf
    · refine h G p B Bs x L D J .POmegaPlus 4 f ψ ⟨rfl, rfl, ?_⟩ hctx
      rcases (show f = 1 ∨ f = 2 by omega) with rfl | rfl
      · exact Or.inl ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hpq⟩
      · exact Or.inr ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hpq⟩
    · exact ggSixRootFusionWitnessOn_POmegaPlusQ1FourBig G p B Bs x L D J .POmegaPlus 4 f ψ
        ⟨rfl, hpq, rfl, hf⟩ hctx
  · exact ggSixRootFusionWitnessOn_POmegaPlusQ1Five G p B Bs x L D J .POmegaPlus n f ψ
      ⟨rfl, hpq, hn⟩ hctx

end Inputs

end CFSG.StandardType
