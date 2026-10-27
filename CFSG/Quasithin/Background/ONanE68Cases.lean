module

public import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsTitsFactsInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_8Small
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.E6EightStmt
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.H13.KGFact68Base

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.KG68 CFSG.Assembly
  CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native.L239

section Residual

variable {G : Type} [Group G]

@[expose] def E68Out {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (T M U L : Subgroup G) :
    Prop :=
  E68Case1 hV T M U L ∨ E68Case2 hV T M U L ∨ E68Case3 T M V U L ∨ E68Case4 M V U L ∨
    E68Case5 M V U L

@[expose] def E68LieType (L : Subgroup G) : Prop :=
  (∃ n : ℕ, 2 ≤ n ∧ LowTwoRank.StatedClassicalModel ↥L .PSL 2 2 n) ∨
  (∃ n : ℕ, Odd n ∧ 3 ≤ n ∧ SuzukiModel ↥L 2 n) ∨
  (∃ n : ℕ, 2 ≤ n ∧ LowTwoRank.StatedClassicalModel ↥L .PSL 3 2 n) ∨
  (∃ n : ℕ, 2 ≤ n ∧ LowTwoRank.StatedClassicalModel ↥L .PSU 3 2 n) ∨
  (∃ n : ℕ, 2 ≤ n ∧ LowTwoRank.StatedClassicalModel ↥L .PSp 2 2 n) ∨
  LowTwoRank.StatedClassicalModel ↥L .PSL 2 5 1 ∨
  (Subgroup.center ↥L = CFSG.pCore 2 ↥L ∧ Subgroup.center ↥L ≠ ⊥ ∧
    LowTwoRank.StatedClassicalModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 2)

end Residual

@[expose] def E68LieRankTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G)
    (hV : CFSG.Open.IsElemAbelian 2 V), HypE61 T M V → U ∈ gammaE64 V M →
    IsComponentIn L (Subgroup.centralizer (U : Set G)) → E68LieType L → E68Out hV T M U L

@[expose] def E68A6Case : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G)
    (hV : CFSG.Open.IsElemAbelian 2 V), HypE61 T M V → U ∈ gammaE64 V M →
    IsComponentIn L (Subgroup.centralizer (U : Set G)) →
    Nonempty (↥L ≃* alternatingGroup (Fin 6)) → E68Case2 hV T M U L

@[expose] def E68M22Excl : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M V U L : Subgroup G),
    HypE61 T M V → U ∈ gammaE64 V M → IsComponentIn L (Subgroup.centralizer (U : Set G)) →
    Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M22) ∨
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* NativeSporadic.Carrier .M23) → False

@[expose] def SmallCatL33 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], LowTwoRank.StatedClassicalModel X .PSL 3 3 1 →
    SmallListFacts X ∧ FixPointwiseInner X

@[expose] def SmallCatL2p : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (p : ℕ), Ch1.IsFermatOrMersennePrime p → 7 ≤ p →
    LowTwoRank.StatedClassicalModel X .PSL 2 p 1 → SmallListFacts X ∧ FixPointwiseInner X

section Cases

variable {G : Type} [Group G] [Finite G] {T M V U L : Subgroup G}

theorem psl_two_seven_of_psl_three_two {X : Type} [Group X]
    (h : LowTwoRank.StatedClassicalModel X .PSL 3 2 1) :
    LowTwoRank.StatedClassicalModel X .PSL 2 7 1 := by
  have hmem : (LowTwoRank.StatedLieTag.PSL) ∈ CFSG.Blueprint.classicalTags := by decide
  rcases CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism X
      (Or.inl ⟨hmem, h⟩) with ⟨-, h7⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · exact h7
  all_goals exact absurd h0 (by decide)

theorem isFermatOrMersennePrime_seven : Ch1.IsFermatOrMersennePrime 7 :=
  ⟨by norm_num, Or.inr ⟨3, by norm_num, by norm_num⟩⟩

end Cases

end E68Proof

end E6

end CFSG.Quasithin
