module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34Inputs517Odd

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def Stmt5_1_17_mNine : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D : Subgroup G) (n : ℕ),
    Setup5_1_17Odd G T M L V H B D n →
    HypF81 T V L (quasithinOmegaOneCenter T ⊓ V) (H ⊔ D) →
      ∀ y ∈ H ⊔ D, y ∉ pCoreOf 2 (H ⊔ D) → y ^ 2 ∈ pCoreOf 2 (H ⊔ D) →
        2 ^ 9 ≤ (centralizerMod (quasithinOmegaOneCenter T ⊓ V) (conjClosure V (H ⊔ D))
          (Subgroup.zpowers y)).relIndex (conjClosure V (H ⊔ D))

@[expose] def L34AutTwoRankFact : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LieModel X .PSL 3 2 2 →
    ∀ A : Subgroup (MulAut X), IsElemAbelian 2 A → Nat.card A ≤ 2 ^ 4

@[expose] def L34TorusCommFact : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (K : Subgroup (MulAut W)) (d t : MulAut W) (n : ℕ), LieModel ↥K .PSL 3 2 2 → Odd n →
      d ^ (2 ^ n - 1) = 1 → (∀ k ∈ K, k * d = d * k) → fixV (Subgroup.zpowers d) = ⊥ →
      t ^ 2 = 1 → t * d = d * t → t ∈ Subgroup.normalizer (K : Set (MulAut W)) →
      t ∉ Subgroup.centralizer (K : Set (MulAut W)) →
        2 ^ 9 ≤ (fixV (Subgroup.zpowers t)).index

end CFSG.Quasithin.H13
