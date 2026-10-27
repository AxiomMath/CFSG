module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs
public import CFSG.LieType.AschbacherSeitz.ToralFrameF3

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.AschbacherSeitz

section Universal

@[expose] def GGExcKGSFOutput : Prop :=
  ∀ (t : StatedLieTag) (n f : ℕ), GGExcFive t → ∀ (G : Type) [Group G] [Finite G]
    (ψ : (ggU t n f).K →* G), GGKnownSetting t n f ψ →
    ∀ p : ℕ, p.Prime → p ≠ 2 → GGExcRegime p f →
    ∀ Bs : Subgroup G, IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs →
      Bs ≤ Subgroup.normalizer (ψ.range : Set G) →
      (∀ b ∈ Bs, GGPsiInnerDiag (ggU t n f).D ψ b) →
      (∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
        Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
          (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
        ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
          (Subgroup.normalizer (ψ.range : Set G)).subtype →
          IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs) →
      ∃ (S : Matrix (Fin (ggU (absTag t) 6 f).D.rank) (Fin (ggU (absTag t) 6 f).D.rank) ℤ)
        (π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank))
        (F : GGStdForm p Bs ψ.range (ggU (absTag t) 6 f).D S π f),
        IsRootGram (ggU (absTag t) 6 f).D S ∧ GGPiCond t p f π ∧
        GGRankOneFrame t n f ψ p Bs S π F ∧ GGClauseF5 t n f p ψ Bs S π F.coord ∧
        GGClauseW t n f p ψ Bs π F.coord ∧ GGClauseA t n f p ψ Bs S π F.coord ∧
        GGClauseAU t n f p ψ Bs S π F.coord

end Universal

end CFSG.StandardType
