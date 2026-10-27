module

public import CFSG.Quasithin.Background.E1Defs
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.LocalAnalysis.QuasithinUnique.QTKECore
public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.BlueprintB2Defs
public import CFSG.Quasithin.Vol2.Ch3Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open scoped IsMulCommutative

variable {G : Type} [Group G]

@[expose] def Alt12_2_2Lie (G : Type) [Group G] : Prop :=
  (∃ (t : StatedLieTag) (n f : ℕ), 2 ≤ f ∧
      (t = .PSL ∧ n = 3 ∨ t = .PSp ∧ n = 2 ∨ t = .PSU ∧ n = 4 ∨ t = .G2 ∧ n = 0 ∨
        t = .trialityD4 ∧ n = 0 ∨ t = .twistedF4 ∧ n = 0) ∧
      StatedLieAdmissible t n 2 f ∧ LieModel G t n 2 f) ∨
    LieModel G .PSU 5 2 2

@[expose] def IsA5ModuleUnder (L W : Subgroup G) : Prop :=
  L ≤ Subgroup.normalizer (W : Set G) ∧
    ∃ _ : IsMulCommutative ↥W, AlternatingNatural (V := ↥W) (autOn L W) ⊤ ⊥ 5

@[expose] def IsA5ModuleSum (L U : Subgroup G) : Prop :=
  IsA5ModuleUnder L U ∨
    ∃ W₁ W₂ : Subgroup G, IsA5ModuleUnder L W₁ ∧ IsA5ModuleUnder L W₂ ∧ W₁ ⊓ W₂ = ⊥ ∧
      W₁ ⊔ W₂ = U

@[expose] def CentralizerComponentClause (T H : Subgroup G) : Prop :=
  ∃ KZ : Subgroup G,
    quasithinIsCComponent KZ (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) ∧
    oTwoUpper H ≤ KZ ∧ CFSG.IsQuasisimple (↥KZ ⧸ CFSG.pCore 2 ↥KZ) ∧
    ((Nonempty (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H) ≃* alternatingGroup (Fin 5)) ∧
        (Nonempty (↥KZ ⧸ CFSG.pCore 2 ↥KZ ≃* alternatingGroup (Fin 7)) ∨
          Nonempty (↥KZ ⧸ CFSG.pCore 2 ↥KZ ≃* NativeSporadic.J2) ∨
          Nonempty (↥KZ ⧸ CFSG.pCore 2 ↥KZ ≃* NativeSporadic.M23))) ∨
      (oTwoUpper H = KZ ∧ LieModel (↥KZ ⧸ CFSG.pCore 2 ↥KZ) .PSL 3 2 2) ∨
      (LieModel (↥(oTwoUpper H) ⧸ CFSG.pCore 2 ↥(oTwoUpper H)) .PSL 2 2 3 ∧
        Is3D4 2 1 (↥KZ ⧸ CFSG.pCore 2 ↥KZ)))

@[expose] def Stmt5_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L H V : Subgroup G) (m : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    M ≤ Subgroup.normalizer (L : Set G) →
    2 ≤ m → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 m →
    IsHStar T M H → 1 < E1.nParam H →
    V ≤ L ⊔ T → IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) → ⁅V, L⁆ ≠ ⊥ →
      (m = 2 ∧ IsA5ModuleSum L ⁅V, L⁆ ∧ CentralizerComponentClause T H) ∨
      Nonempty (G ≃* NativeSporadic.M23) ∨ Alt12_2_2Lie G

@[expose] def Stmt6_2_20 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (m : ℕ), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    M ≤ Subgroup.normalizer (L : Set G) →
    2 ≤ m → LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 m →
    V ≤ L ⊔ T → IsPrimeReduced 2 (V.subgroupOf (L ⊔ T)) → ⁅V, L⁆ ≠ ⊥ →
      (m = 2 ∧ IsA5ModuleSum L ⁅V, L⁆ ∧
        ∀ H : Subgroup G, IsHStar T M H → 1 < E1.nParam H → CentralizerComponentClause T H) ∨
      Alt12_2_2Lie G ∨
      Nonempty (G ≃* NativeSporadic.M22) ∨ Nonempty (G ≃* NativeSporadic.M23)

end CFSG.Quasithin.H13
