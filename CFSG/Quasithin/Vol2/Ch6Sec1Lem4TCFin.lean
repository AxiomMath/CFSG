module

public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Vol2.Ch6Defs

public section

namespace CFSG.Quasithin.H13.T614

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement

@[expose] def TitsOrderFact : Prop :=
  ∀ (Y : Type) [Group Y], IsTits Y → Nat.card Y = 17971200

@[expose] def TitsRankThreeFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsTits Y →
    ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9

@[expose] def TitsParabolicNormalizerFact : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsTits Y → ∀ P : Subgroup Y, Nat.card P = 2 ^ 11 * 5 →
    ∀ φ : MulAut Y, φ ^ 3 = 1 →
      (oTwoUpper P).map φ.toMonoidHom = oTwoUpper P → φ = 1

@[expose] def L216ModuleFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp611 G T M L V 4 →
    IsOrthCh5 L V 4 →
    Nat.card ↥(autOn L V ⊓ Subgroup.normalizer ((autOn (T ⊓ L) V : Subgroup (MulAut V)) :
      Set (MulAut V))) = 240 ∧
    Nat.card ↥(V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) = 4

@[expose] def L216CoreFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V X : Subgroup G), Hyp611 G T M L V 4 →
    IsOrthCh5 L V 4 → X ≤ L → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
    ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
    pCoreOf 2 (autOn (X ⊔ T) V) = autOn (T ⊓ L) V

@[expose] def L216NormalizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V X : Subgroup G), Hyp611 G T M L V 4 →
    IsOrthCh5 L V 4 → X ≤ L → X = oTwoUpper X → (X ⊓ T).relIndex X = 5 →
    ((X ⊓ T).subgroupOf X).Normal → T ≤ Subgroup.normalizer (X : Set G) →
    Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ⊓ L ≤
      Subgroup.normalizer ((X ⊔ pCoreOf 2 L : Subgroup G) : Set G)

@[expose] def FFCentralizerFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V M₁ K₁ : Subgroup G),
    Hyp611 G T M L V 4 → IsOrthCh5 L V 4 → quasithinIsMaxTwoLocal M₁ →
    Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ M₁ →
    K₁ ∈ cComp M₁ → IsTits (ModO2 K₁) → T ≤ Subgroup.normalizer (K₁ : Set G) →
    ¬ thompsonJ T ≤ centralizerMod (pCoreOf 2 K₁) (Subgroup.normalizer (K₁ : Set G)) K₁ →
    K₁ ≤ Subgroup.centralizer (quasithinOmegaOneCenter (pCoreOf 2 (K₁ ⊔ T)) : Set G)

theorem tits_three_rank_exists (h2 : TitsRankThreeFact) {Y : Type} [Group Y] [Finite Y]
    (hY : IsTits Y) : ∃ E : Subgroup Y, IsElemAbelian 3 E ∧ Nat.card E = 9 :=
  h2 Y hY

end CFSG.Quasithin.H13.T614

end
