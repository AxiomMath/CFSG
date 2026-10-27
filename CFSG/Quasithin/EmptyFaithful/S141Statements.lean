module

public import CFSG.Quasithin.EmptyFaithful.Vocabulary
public import CFSG.Quasithin.Background.A3ComponentsCore
public import CFSG.Quasithin.QTFE14Cat

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open

@[expose] def StageLemma1413 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G → quasithinIsQTKECat G →
    quasithinIsSylowTwo T → (∀ L : Subgroup G, ¬ quasithinIsFaithfulLocal T L) →
    ∀ H : Subgroup G, InH T H → ∀ U : Subgroup G, IsTwoReducedIn H U →
      perfectCore H ≤ Subgroup.centralizer (U : Set G)

@[expose] def StageLemma1416 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    (∀ M V : Subgroup G, InM T M → IsTwoReducedIn M V →
      perfectCore M ≤ Subgroup.centralizer (V : Set G)) ∧
    (∀ L : Subgroup G, quasithinIsMaximalLocal T L ↔ L ∈ cComp Mc) ∧
    (∀ K ∈ cComp Mc, IsUniqueM (K ⊔ T) Mc) ∧
    (∀ H : Subgroup G, InH T H →
      perfectCore H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ∧
        Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ Mc)

@[expose] def Lemma1417CaseTwo {G : Type*} [Group G] (T M V : Subgroup G) : Prop :=
  IsOFourPlusAction M V ∧
    ∃ Y₁ Y₂ : Subgroup G, ∃ t : Subgroup.normalizer (V : Set G),
      Y₁ ≤ M ∧ Y₂ ≤ M ∧ (t : G) ∈ M ∧
      Nonempty (autOn Y₁ V ≃* Equiv.Perm (Fin 3)) ∧ Nonempty (autOn Y₂ V ≃* Equiv.Perm (Fin 3)) ∧
      autOn Y₁ V ⊓ autOn Y₂ V = ⊥ ∧
      (∀ a ∈ autOn Y₁ V, ∀ b ∈ autOn Y₂ V, a * b = b * a) ∧
      conjAct V t ^ 2 = 1 ∧ conjAct V t ≠ 1 ∧
      (autOn Y₁ V).map (MulAut.conj (conjAct V t)).toMonoidHom = autOn Y₂ V ∧
      autOn M V = (autOn Y₁ V ⊔ autOn Y₂ V) ⊔ Subgroup.zpowers (conjAct V t) ∧
      autOn (thompsonJ M) V = autOn Y₁ V ⊔ autOn Y₂ V ∧
      ⁅V, Y₁⁆ ⊓ ⁅V, Y₂⁆ = ⊥ ∧ ⁅V, Y₁⁆ ⊔ ⁅V, Y₂⁆ = V ∧
      Nat.card (⁅V, Y₁⁆ : Subgroup G) = 4 ∧ Nat.card (⁅V, Y₂⁆ : Subgroup G) = 4 ∧
      Nat.card (omegaOneCenterOf (thompsonJ T) ⊓ V : Subgroup G) = 4 ∧
      quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) ⊓ V ∧
      Nat.card (quasithinOmegaOneCenter T) = 2

@[expose] def Lemma1417CaseOne {G : Type*} [Group G] (T M V : Subgroup G) : Prop :=
  Nat.card V = 4 ∧ autOn M V = ⊤ ∧
    omegaOneCenterOf (thompsonJ T) ⊓ V = quasithinOmegaOneCenter T ∧
    Nat.card (quasithinOmegaOneCenter T) = 2

@[expose] def StageLemma1417 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∀ M V : Subgroup G, InM T M → IsTwoReducedIn M V →
      ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) →
      (M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2) →
      Lemma1417CaseOne T M V ∨ Lemma1417CaseTwo T M V

end CFSG.Quasithin
