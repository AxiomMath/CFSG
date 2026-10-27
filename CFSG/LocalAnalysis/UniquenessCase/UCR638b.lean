module

public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

@[expose] def R6_38Sigma23 (D : Data G) : Prop :=
  ∀ p ∈ D.sig2 ∪ D.sig3, UC22.F10.OpRes p D.M = D.M

theorem r6_38_of_sigma23 (D : Data G) (h1 : ∀ p ∈ D.sig1, IsStronglyPEmbedded p D.M)
    (h : R6_38Sigma23 D) : R6_38 D := by
  refine r6_38_of_sigma D ?_
  intro p hp
  have hp' : p ∈ D.sig1 ∪ D.sig2 ∪ D.sig3 := by
    rw [← D.sig_sub]
    exact hp
  rcases hp' with (hp1 | hp2) | hp3
  · exact opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab (D.sig_prime p hp).1
      (h1 p hp1)
  · exact h p (Or.inl hp2)
  · exact h p (Or.inr hp3)

theorem r6_38_of_sigma23_dataOfSetup4 (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (h : R6_38Sigma23 (dataOfSetup4 hS hU S)) : R6_38 (dataOfSetup4 hS hU S) :=
  r6_38_of_sigma23 _ (fun _ hp => isStronglyPEmbedded_of_sigmaOne hU S.maxLocal hp.1 hp.2) h

end CFSG.LocalAnalysis.UniquenessCase.UC6
