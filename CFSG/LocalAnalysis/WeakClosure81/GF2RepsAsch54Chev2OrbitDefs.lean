module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A1bBasic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open CFSG.LieType.Universal CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub Subgroup

@[expose] def HasBQRank (X : Type) [Group X] (r : ℕ) : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* X) (e : ℕ), BorelQuotient D n H π e ∧ D.rank = r

@[expose] def HasBQUneven (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* X) (e : ℕ), BorelQuotient D n H π e ∧
      ∃ i j : Fin D.rank,
        Nat.card ↥(D.rootGroup (Pi.single i 1)) ≠ Nat.card ↥(D.rootGroup (Pi.single j 1))

structure UMaxBQ {Q : Type} [Group Q] (L T M : Subgroup Q) {K : Type} [Group K]
    (D : UniversalRootDatum K) (n : Fin D.rank → K) (H : Fin D.rank → Subgroup K)
    (π : K →* ↥L) (e : ℕ) : Prop where
  normal : L.Normal
  simple : IsSimpleGroup ↥L
  nonabelian : ∃ a b : ↥L, a * b ≠ b * a
  sylow : IsSylowIn 2 T ⊤
  lt_top : M < ⊤
  le_of_le : ∀ X : Subgroup Q, T ≤ X → X < ⊤ → X ≤ M
  bq : BorelQuotient D n H π e
  unip : (T ⊓ L).subgroupOf L = (posUnipotent D).map π

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
