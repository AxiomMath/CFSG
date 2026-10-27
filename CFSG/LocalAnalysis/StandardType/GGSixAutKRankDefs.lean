module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatStepTwo
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFlatRootCent

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Item1Statements

@[expose] def GGAutKRank {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (t : StatedLieTag)
    (f : ℕ) (L₁ : Subgroup G) : Prop :=
  Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 ∨
    ¬ GGSixSeventeenExcluded p t f L₁

@[expose] def GGAutKCanonIIIFlatInputRk : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      GGAutKRank p Bs t f L₁ →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestIIIFlat p
          (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))
          (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))

@[expose] def GGAutKCanonIIIFlatInputRkTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestIIIFlat p
          (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))
          (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))

@[expose] def GGAutKCanonIIIFlatInputTable : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ (b : G) (L₁ K : Subgroup G) (m : G), GGAutKConjConfig p B Bs x L D J b L₁ K m →
      ¬ GGSixSeventeenExcluded p t f L₁ →
      ∀ [((ggAutKV D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).Normal],
        GGHypRestIIIFlat p
          (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))
          (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map
            (ggAutKPi D K (ggM p B x L D J) m))

end Item1Statements

end CFSG.StandardType
