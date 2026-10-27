module

public import CFSG.Quasithin.Background.E2Two
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E6Gamma

public section

open scoped Pointwise commutatorElement

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.E1 CFSG.QuasithinUnique

@[expose] def rootGroupOfParabolicR {Y : Type*} [Group Y] (P : Subgroup Y) : Subgroup Y :=
  Subgroup.closure {x : Y | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} ⊓
    Subgroup.centralizer
      (Subgroup.closure {x : Y | x ∈ P ∧ ∃ k : ℕ, x ^ 2 ^ k = 1} : Set Y)

@[expose] def Three {G : Type} [Group G] [Finite G] (T M V U L X : Subgroup G) : Prop :=
  ((CharTwo (Subgroup.centralizer (U : Set G)) ∧
      IsBlock2 (Subgroup.centralizer (U : Set G)) L ∧ IsLin2Type L (E3.mQuot V U) ∧
      M.relIndex L = 2 ^ E3.mQuot V U + 1) ∨
    ((CFSG.generalizedFitting ↥(Subgroup.centralizer (U : Set G))).map
          (Subgroup.centralizer (U : Set G)).subtype = pCoreOf 2 (Subgroup.centralizer (U : Set G)) ⊔ L ∧
      (CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 2 2 (E3.mQuot V U) ∨
        CFSG.Blueprint.SuzukiModel (↥L ⧸ Subgroup.center ↥L) 2 (E3.mQuot V U) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2
          (E3.mQuot V U) ∨
        CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 3 2
          (E3.mQuot V U)) ∧
      E2.IsBorelIn L (M ⊓ L) ∧
      pCoreOf 2 L ⊔ ⁅V, X⁆ = centerOf (L ⊓ (T ⊓ Subgroup.centralizer (V : Set G)))) ∨
    ((CFSG.generalizedFitting ↥(Subgroup.centralizer (U : Set G))).map
          (Subgroup.centralizer (U : Set G)).subtype = pCoreOf 2 (Subgroup.centralizer (U : Set G)) ⊔ L ∧
      CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 (E3.mQuot V U) ∧
      IsMaxParabolic2 L (L ⊓ M) ∧ perfectCore (L ⊓ M) = L ⊓ Subgroup.centralizer (V : Set G) ∧
      ⁅V, X⁆ = rootGroupOfParabolicR (L ⊓ M)))

@[expose] def Concl {G : Type} [Group G] [Finite G] {T M V : Subgroup G} (h : E6.HypE61 T M V)
    (U L X : Subgroup G) : Prop :=
  (L ≤ Subgroup.centralizer (U : Set G) ∧
    (L.subgroupOf (Subgroup.centralizer (U : Set G))).Normal ∧
    ((Subgroup.centralizer (U : Set G) ⊓ M : Subgroup G) : Set G) * (L : Set G) =
      (Subgroup.centralizer (U : Set G) : Set G)) ∧
  (U ⊓ ⁅V, X⁆ = ⊥ ∧ U ⊔ ⁅V, X⁆ = V ∧ X ≤ L ⊓ M ∧ IsCyclic X ∧
    Nat.card X = 2 ^ E3.mQuot V U - 1 ∧ autI h.isElemAbelian X ≠ ⊥ ∧
    (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v * x⁻¹ = v → x ∈ Subgroup.centralizer (V : Set G)) ∧
    (∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ w ∈ ⁅V, X⁆, w ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = w) ∧
    autI h.isElemAbelian (M ⊓ Subgroup.normalizer (U : Set G)) ≤
      Subgroup.normalizer (autI h.isElemAbelian X : Set (MulAut (IntMod V h.isElemAbelian))) ∧
    autI h.isElemAbelian X ≤ autI h.isElemAbelian (M ⊓ Subgroup.normalizer (U : Set G))) ∧
  Three T M V U L X ∧
  Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (L : Set G) ≤
    M ⊓ Subgroup.centralizer (V : Set G)

@[expose] def Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U : Subgroup G) (h : E6.HypE61 T M V),
    U ∈ E6.gammaE64 V M →
    (∀ W : Subgroup G, W ≤ V → U < W → Subgroup.centralizer (W : Set G) ≤ M) →
    1 < E3.mQuot V U → ∃ L X : Subgroup G, Concl h U L X

end CFSG.Quasithin.RonanE611
