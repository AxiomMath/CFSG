module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinParK
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit

open CFSG.Quasithin CFSG.Open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

@[expose] def SmallEdge {K : Type} [Group K] (D : UniversalRootDatum K) (u v : Fin D.rank) :
    Prop :=
  ¬ HasCompFactor (rankOne D.rootGroup u ⊔ rankOne D.rootGroup v) IsCalL0 ∨
    (TauCeti.diagramGraph D.cartan).degree u ≠ (TauCeti.diagramGraph D.cartan).degree v ∨
    Nat.card ↥(D.rootGroup (Pi.single u 1)) ≠ Nat.card ↥(D.rootGroup (Pi.single v 1))

@[expose] def BQSmall {K : Type} [Group K] (D : UniversalRootDatum K) : Prop :=
  (∀ i, ¬ HasCompFactor (rankOne D.rootGroup i) IsCalL0) ∧
    (3 ≤ D.rank → ∀ u v, (TauCeti.diagramGraph D.cartan).Adj u v → SmallEdge D u v)

@[expose] def HasBQSmall (X : Type) [Group X] : Prop :=
  ∃ (K : Type) (_ : Group K) (_ : Finite K) (D : UniversalRootDatum K) (n : Fin D.rank → K)
    (H : Fin D.rank → Subgroup K) (π : K →* X) (e : ℕ), BorelQuotient D n H π e ∧ BQSmall D ∧
      (3 ≤ D.rank ∨ ∃ i j : Fin D.rank,
        Nat.card ↥(D.rootGroup (Pi.single i 1)) ≠ Nat.card ↥(D.rootGroup (Pi.single j 1)))

@[expose] def NodeTransitive {Q : Type} [Group Q] (L T : Subgroup Q) {K : Type} [Group K]
    (D : UniversalRootDatum K) (H : Fin D.rank → Subgroup K) (π : K →* ↥L) : Prop :=
  ∀ i j : Fin D.rank, ∃ t ∈ T,
    (((parJ D H {i}).map π).map L.subtype).map (MulAut.conj t).toMonoidHom =
      ((parJ D H {j}).map π).map L.subtype

end CFSG.LocalAnalysis.WeakClosure81.Chev2Orbit
