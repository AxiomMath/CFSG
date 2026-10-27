module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qg
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

structure Standing22 (D : Data G) : Prop where
  dataExt : DataExt D
  sigmaStd : UC6S846.SigmaStd D
  sigma23 : Sigma23Std D
  sigma2 : Sigma2Print D
  cent : UC6.R613Cent D
  r6_1 : UC6.R6_1 D
  r6_3 : UC6.R6_3 D
  r6_6 : UC6.R6_6 D
  r6_7 : UC6.R6_7 D
  r6_11 : UC6.R6_11Used D
  three_mem_sig : 3 < CFSG.Open.pRank 3 D.M → 3 ∈ D.sig

theorem Standing22.hyp612 {D : Data G} (hs : Standing22 D) :
    ∀ p ∈ D.sig2, ∃ P P₀ : Subgroup G, UC6.Hyp612 D p P P₀ := fun p hp => by
  obtain ⟨P, P₀, hH, -⟩ := hs.sigma2 p hp
  exact ⟨P, P₀, hH⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
