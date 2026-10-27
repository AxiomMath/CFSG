module

public import CFSG.Quasithin.MS93.SkHyp
public import CFSG.Quasithin.Background.C4Defs
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G]

@[expose] def MS93Case2 (M L : Subgroup G) : Prop :=
  Vq M L ≤ Xq M ∧ ∃ N : Subgroup ↥L,
    IsAltNaturalSection L (Vq M L) (Vq M L ⊓ Subgroup.centralizer (L : Set G)) N 6

@[expose] def MS93Case3 (M T L : Subgroup G) : Prop :=
  Vq M L ≤ Xq M ∧
    ∃ (k : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSp 2 F)),
      2 ≤ k ∧ Fintype.card F = 2 ^ k ∧ Function.Surjective α ∧
      IsSumOfNaturalModulesVia L (Vq M L) (Vq M L ⊓ Subgroup.centralizer (L : Set G)) α false 1 ∧
      (IsOddRadical M T → k = 2)

@[expose] def MS93Case4 (M L : Subgroup G) : Prop :=
  Vq M L ≤ Xq M ∧
    ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
      IsSumOfNaturalModulesVia L (Vq M L) ⊥ α false 1

@[expose] def MS93Case5 (V L : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
    Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧ IsSumOfNaturalModulesVia L V ⊥ α false 2

@[expose] def MS93Case6 (M L : Subgroup G) : Prop :=
  Vq M L ≤ Xq M ∧ ∃ hV : IsElemAbelian 2 (Vq M L), TripleA6Six (autI hV L) ⊤ ⊥

@[expose] def MS93Case8 (M T L : Subgroup G) : Prop :=
  (∃ α : ↥M →* ↥(StatedSL 3 (ZMod 2)), Function.Surjective α ∧
      IsSumOfNaturalModulesVia M (Vq M L) (Vq M L ⊓ Subgroup.centralizer (M : Set G)) α false 1) ∧
    Nat.card ↥(Vq M L ⊓ Subgroup.centralizer (M : Set G)) = 2 ∧
    (pCoreOf 2 M).relIndex T = 4 ∧
    (Vq M L ⊓ Subgroup.centralizer (M : Set G)).relIndex
      (⁅Vq M L, T⁆ ⊔ Vq M L ⊓ Subgroup.centralizer (M : Set G)) = 2 ∧
    Vq M L ⊓ Subgroup.centralizer (M : Set G) = Vq M L ⊓ Subgroup.centralizer (L : Set G) ∧
    Vq M L = Uq M T L ∧ Xq M = Zq M L ⊔ Uq M T L ∧
    ∀ S : Subgroup G, IsSylowTwoOf S M →
      Vq M L ⊓ Subgroup.centralizer (S : Set G) = Vq M L ⊓ Subgroup.centralizer (M : Set G)

@[expose] def MS93Case10 (M L : Subgroup G) : Prop :=
  Vq M L ≤ Xq M ∧ ∃ hV : IsElemAbelian 2 (Vq M L), G2NaturalDerived (autI hV L) ⊤ ⊥ 1

@[expose] def QjInfo (T L W : Subgroup G) (q : ℕ) : Prop :=
  ∀ SL : Subgroup G, IsSylowTwoOf SL L → T ≤ Subgroup.normalizer (SL : Set G) →
    ∃ X : Subgroup G, IsParRadOver L SL X ∧
      (W ⊓ Subgroup.centralizer (X : Set G)).relIndex W = q ∧ X ≤ T

@[expose] def MS93Case11 (V T L : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
    Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
    IsSumOfNaturalModulesVia L (centerOf V) ⊥ α false 1 ∧
    IsSumOfNaturalModulesVia L V (centerOf V) α true 2 ∧ QjInfo T L (centerOf V) (2 ^ n)

@[expose] def MS93Case13 (V T L : Subgroup G) : Prop :=
  ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
    Fintype.card F = 2 ^ n ∧ Function.Surjective α ∧
    Nat.card ↥(V ⊓ Subgroup.centralizer (L : Set G)) = (2 ^ n) ^ 2 ∧
    IsElemAbelian 2 (V ⊓ Subgroup.centralizer (L : Set G)) ∧
    centerOf V = V ⊓ Subgroup.centralizer (L : Set G) ⊔ ⁅centerOf V, L⁆ ∧
    V ⊓ Subgroup.centralizer (L : Set G) ⊓ ⁅centerOf V, L⁆ = ⊥ ∧
    IsSumOfNaturalModulesVia L ⁅centerOf V, L⁆ ⊥ α false 1 ∧
    IsSumOfNaturalModulesVia L (frattiniIn V) (centerOf V) α true 1 ∧
    IsSumOfNaturalModulesVia L (V ⊓ Subgroup.centralizer (frattiniIn V : Set G)) (frattiniIn V)
      α true 2 ∧
    IsSumOfNaturalModulesVia L V (V ⊓ Subgroup.centralizer (frattiniIn V : Set G)) α false 2 ∧
    QjInfo T L (centerOf V) (2 ^ n)

@[expose] def MS93ConclAS (M T L : Subgroup G) : Prop :=
  MS93Case2 M L ∨ MS93Case3 M T L ∨ MS93Case4 M L ∨
    (Xq M ≤ Zq M L ⊔ Uq M T L ∧ MS93Case5 (Vq M L) L) ∨ MS93Case6 M L ∨ MS93Case8 M T L ∨
    MS93Case10 M L ∨ (Xq M ≤ Zq M L ⊔ Uq M T L ∧ MS93Case11 (Vq M L) T L) ∨
    (Xq M ≤ Zq M L ⊔ Uq M T L ∧ MS93Case13 (Vq M L) T L)

end CFSG.Quasithin.MS93
