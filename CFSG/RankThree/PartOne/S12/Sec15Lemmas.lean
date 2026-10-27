module

public import CFSG.RankThree.PartOne.S12.Facts
public import CFSG.RankThree.PartOne.S9.Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory

@[expose] def thompsonElem {G : Type} [Group G] (p : ℕ) (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x : G | ∃ F : Subgroup G, F ≤ X ∧ IsElementaryAbelian p F ∧
    (∀ F' : Subgroup G, F' ≤ X → IsElementaryAbelian p F' → Nat.card F' ≤ Nat.card F) ∧ x ∈ F}

@[expose] def Weyl154 {G : Type} [Group G] (p : ℕ) (E : Subgroup G) (W₀ : Subgroup (MulAut E)) :
    Prop :=
  W₀ = Subgroup.closure {t : MulAut E | t ∈ reflectionSet p E ∧
      t ∉ (CFSG.pCore 2 ↥(reflectionGroup p E)).map (reflectionGroup p E).subtype} ∧
    W₀ ≤ reflectionGroup p E ∧
    (Nonempty (↥W₀ ≃* Equiv.Perm (Fin 4)) ∨ Nonempty (↥W₀ ≃* Equiv.Perm (Fin 5))) ∧
    torusWeyl E = (Subgroup.center ↥(torusWeyl E)).map (torusWeyl E).subtype ⊔ W₀ ∧
    (Subgroup.center ↥(torusWeyl E)).map (torusWeyl E).subtype ⊓ W₀ = ⊥ ∧
    ∀ z ∈ Subgroup.center ↥(torusWeyl E), ∃ k : ℤ, ∀ e : E, ((z : MulAut E) e : E) = e ^ k

@[expose] def Node154 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∃ W₀ : Subgroup (MulAut E), Weyl154 p E W₀

@[expose] def Sylow155 {G : Type} [Group G] (p : ℕ) (A E P : Subgroup G) : Prop :=
  omegaOne p P = E ∨
    (Outcome152Five p E A (lieGenerated p E) ∧ p = 5 ∧
      (∀ F : Subgroup G, F ≤ P → IsElementaryAbelian p F → Nat.card F = p ^ 3 → F ≤ E) ∧
      ∀ X : Subgroup G, X ≤ P → (X.subgroupOf P).Normal → thompsonElem p X ≤ E)

@[expose] def Node155 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ P : Subgroup G, IsSylowOf p P (torusNormalizer E) → Sylow155 p A E P

@[expose] def Node156 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ X ∈ thetaCompZeroStarE p E, X ≤ lieGenerated p E

@[expose] def Node158 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E

@[expose] def Node1510 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152 p E A (lieGenerated p E) →
    ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ → Subgroup.normalizer (U : Set G) ≤ lieNormalizer p E

end CFSG.RankThree.PartOne
