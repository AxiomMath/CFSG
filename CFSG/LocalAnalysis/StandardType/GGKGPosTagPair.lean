module

public import CFSG.LocalAnalysis.StandardType.GGKGPosTagPairAD
public import CFSG.LocalAnalysis.StandardType.GGKGPosTagPairE

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section TagPair

theorem ggTag_adjStdPair {t : StatedLieTag} {n f : ℕ}
    (ht : t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8)
    (hadm : StatedLieAdmissible t n 2 f) (h3 : 3 ≤ bnRank t n) :
    ∃ a b : Fin (ggU t n f).D.rank,
      (coxeterMatrix (ggU t n f).D.isFiniteType).M a b = 3 ∧
        ∀ {G : Type} [Group G] (ψ : (ggU t n f).K →* G),
          ψ.ker ≤ Subgroup.center (ggU t n f).K →
            ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 2 f) W
              ((ggRootLevi (ggU t n f).D (Pi.single a 1)).map ψ)
              ((ggRootLevi (ggU t n f).D (Pi.single b 1)).map ψ) := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · exact ggTagAD_adjStdPair (Or.inl rfl) hadm h3
  · exact ggTagAD_adjStdPair (Or.inr rfl) hadm h3
  · exact ggTagE_adjStdPair (Or.inl rfl) hadm
  · exact ggTagE_adjStdPair (Or.inr (Or.inl rfl)) hadm
  · exact ggTagE_adjStdPair (Or.inr (Or.inr rfl)) hadm

end TagPair

end CFSG.StandardType
