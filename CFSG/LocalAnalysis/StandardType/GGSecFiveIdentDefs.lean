module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveCompatRestDefs
public import CFSG.LocalAnalysis.StandardType.GGSixRootCentralizerBasic
public import CFSG.ClassicalInvolution.WeakCT.Defs
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.ClassicalInvolution.Phan.Blocks

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.ClassicalInvolution.WeakCT

section Vocab

variable {G : Type} [Group G] [Finite G]

@[expose] def GGNbrSet (p : ℕ) (B : Subgroup G) (x : G) (D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop :=
  𝒦.card ≤ 2 ∧ ∀ K ∈ 𝒦, ∃ y : G, GGNbr p B x D J y K

@[expose] noncomputable def ggAutomizerJoin (L Bs : Subgroup G) (𝒦 : Finset (Subgroup G)) :
    Subgroup (MulAut ↥Bs) :=
  ggAutomizer L Bs ⊔ ⨆ K ∈ 𝒦, ggAutomizer K Bs

@[expose] def GGMaximalJoin (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop :=
  GGNbrSet p B x D J 𝒦 ∧ GGWeylReflectionGroup p (ggAutomizerJoin L Bs 𝒦) ∧
    ∀ 𝒦' : Finset (Subgroup G), GGNbrSet p B x D J 𝒦' →
      GGWeylReflectionGroup p (ggAutomizerJoin L Bs 𝒦') →
        Nat.card (ggAutomizerJoin L Bs 𝒦') ≤ Nat.card (ggAutomizerJoin L Bs 𝒦)

@[expose] def GGSecFiveRouteCfg (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)) : Prop :=
  GGSecFiveRestHyp p B Bs x L D J ∧ GGSecFiveWeylCase' p B Bs x D J ∧
    ¬ GGSecFiveLeviCase p B Bs x L D J ∧ GGMaximalJoin p B Bs x L D J 𝒦

@[expose] def ggHyperplane (Bs : Subgroup G) (r : MulAut ↥Bs) : Subgroup G :=
  (MonoidHom.eqLocus (r : ↥Bs →* ↥Bs) (MonoidHom.id ↥Bs)).map Bs.subtype

@[expose] def ggRankOne (Bs : Subgroup G) (r : MulAut ↥Bs) : Subgroup G :=
  ggOTwoPrime (Subgroup.centralizer (ggHyperplane Bs r : Set G))

@[expose] def ggRankOnePerf (Bs : Subgroup G) (r : MulAut ↥Bs) : Subgroup G :=
  CFSG.Quasithin.perfectCore (Subgroup.centralizer (ggHyperplane Bs r : Set G))

@[expose] def ggRankOneIn (X Bs : Subgroup G) (r : MulAut ↥Bs) : Subgroup G :=
  ggOTwoPrime (X ⊓ Subgroup.centralizer (ggHyperplane Bs r : Set G))

@[expose] def GGCoxeterPres (p : ℕ) {Bs : Subgroup G} (A : Subgroup (MulAut ↥Bs)) {ι : Type}
    (M : CoxeterMatrix ι) (e : M.Group ≃* ↥A) : Prop :=
  GGIsWeylMatrix M ∧ ∀ i : ι, GGIsReflection p ((e (M.simple i) : ↥A) : MulAut ↥Bs)

@[expose] def GGOrbPair (L Bs : Subgroup G) (𝒦 : Finset (Subgroup G)) {ι : Type}
    (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)) (i j : ι) : Prop :=
  ∃ (w : M.Group) (X : Subgroup G), (X = L ∨ X ∈ 𝒦) ∧
    ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer X Bs ∧
    ((e (w * M.simple j * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ∈ ggAutomizer X Bs

end Vocab

section Inputs

@[expose] def GGSecFiveIdentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
        GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ

@[expose] def GGSecFiveIdentCompatInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G), 3 ≤ bnRank t n ∧
        GGPresentsG0 (L ⊔ ⨆ K ∈ 𝒦, K) (ggU t n f).D t n f ψ ∧
          GGCompatPresented (ggU t n f).D ψ L

@[expose] def GGSecFiveJoinInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 →
      ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K

@[expose] def GGSplitLie {G : Type} [Group G] (p : ℕ) (L : Subgroup G) : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    StatedLieAdmissible t n 2 f ∧ ψ.ker ≤ Subgroup.center (ggU t n f).K ∧ ψ.range = L ∧
      (t = .PSL ∨ t = .POmegaPlus ∨ t = .E6 ∨ t = .E7 ∨ t = .E8) ∧ p ∣ 2 ^ f - 1

@[expose] def GGSecFiveLeviData : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGSecFiveRestHyp p B Bs x L D J → GGSecFiveWeylCase' p B Bs x D J →
      GGSecFiveLeviCase p B Bs x L D J → GGSecFiveData p B x L D J

end Inputs

end CFSG.StandardType

end
