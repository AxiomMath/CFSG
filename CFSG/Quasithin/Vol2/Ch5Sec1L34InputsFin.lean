module

public import CFSG.Quasithin.Vol2.Ch5StatementsB

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def L2ModFixTwoFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L T W : Subgroup G) (n : ℕ) (d : G),
    ((IsNatModCh5 L W n ∧ (n = 2 ∨ n = 4)) ∨ (IsOrthCh5 L W n ∧ (n = 4 ∨ n = 8))) →
    IsPGroup 2 T → T ≤ Subgroup.normalizer (L : Set G) →
    T ≤ Subgroup.normalizer (W : Set G) → IsSylowTwoOf (T ⊓ L) L →
    (L ⊔ T) ⊓ Subgroup.centralizer (W : Set G) ≤ T →
    d ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) → orderOf d = 3 →
    d ∉ Subgroup.normalizer (T : Set G) →
      Nat.card ↥(W ⊓ Subgroup.centralizer (T : Set G)) = 2

@[expose] def L4NatSumFact : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L V S : Subgroup G) (v : G),
    IsSumOfTwo L V (fun W => IsNatModCh5 L W 2) →
    (∀ a ∈ V, ∀ b ∈ V, a * b = b * a) →
    (∀ W : Subgroup G, W ≤ V → IsNatModCh5 L W 2 →
      L ⊓ Subgroup.centralizer (W : Set G) ≤ Subgroup.centralizer (V : Set G)) →
    IsSylowTwoOf S L → v ∈ V → v ∈ Subgroup.centralizer (S : Set G) →
      ∃ V₁ : Subgroup G, v ∈ V₁ ∧ IsNatModCh5 L V₁ 2 ∧ IsIrrPlusBase L V V₁

@[expose] def Stmt5_1_14_qBound : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D D₃ Z₁ : Subgroup G) (n : ℕ),
    Hyp5_1_8 G T M L H n → IsNotation5_1_9 T M L H B D → IsCh5Module T L V →
    LieModel (O2Q (oTwoUpper H)) .PSL 3 2 2 → ¬ Concl5_1_14_four T L V B D n →
    D₃ ≤ D → Nat.card D₃ = 3 → IsZ1Choice T L Z₁ →
    ∀ hU : IsElemAbelian 2 (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H)),
      2 < qInt (tildeOf Z₁ H) (tildeOf Z₁ (conjClosure (conjClosure Z₁ D₃) H)) hU

end CFSG.Quasithin.H13
