module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThreeBasic
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.RealThree (Real3)

@[expose] def WeaklyClosed {G : Type} [Group G] (Z : Subgroup G) : Prop :=
  ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) →
    Z.map (MulAut.conj g).toMonoidHom = Z

@[expose] def AutWeaklyClosed {S : Type} [Group S] (σ : MulAut S) : Prop :=
  ∀ x : S, MulAut.conj x * σ * (MulAut.conj x)⁻¹ ∈
      Subgroup.normalizer ((Subgroup.zpowers σ : Subgroup (MulAut S)) : Set (MulAut S)) →
    MulAut.conj x * σ * (MulAut.conj x)⁻¹ ∈ Subgroup.zpowers σ

@[expose] def NoCover3 (S : Type) [Group S] : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → IsPGroup 3 (Subgroup.center L) →
    Nonempty (L ⧸ Subgroup.center L ≃* S) → Subgroup.center L = ⊥

@[expose] def ListRow (S : Type) [Group S] [Finite S] : Prop :=
  ∀ z : S, orderOf z = 3 → WeaklyClosed (Subgroup.zpowers z) →
    CFSG.Open.pRank 3 (⊤ : Subgroup S) = 1 ∨ (IsoGTwoPrime S ∧ Real3 S ∧ NoCover3 S) ∨
      (Nonempty (S ≃* Blueprint.NativeSporadic.J2) ∧ Real3 S ∧ NoCover3 S)

@[expose] def OuterRow (S : Type) [Group S] [Finite S] : Prop :=
  3 ∣ Nat.card S → ∀ σ : MulAut S, σ ^ 3 = 1 → σ ∉ (MulAut.conj : S →* MulAut S).range →
    ¬ AutWeaklyClosed σ

@[expose] def GoodRow (S : Type) [Group S] [Finite S] : Prop :=
  ListRow S ∧ OuterRow S

end CFSG.RankThree.PartTwo.Sec4.RonanK432
