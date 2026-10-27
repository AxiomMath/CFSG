module

public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Background.D2Params
public import CFSG.Quasithin.Background.B4ModelsLie
public import CFSG.Quasithin.H13.StatementsFSU

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSp)
open scoped IsMulCommutative Pointwise

@[expose] def Stmt3_2_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      (quasithinIsMaxTwoLocal (Subgroup.normalizer (conjClosure L T : Set G)) ∧
        T ≤ Subgroup.normalizer (conjClosure L T : Set G)) ∧
      (conjClosure L T ⊔ T ≤ Subgroup.normalizer (conjClosure L T : Set G) ∧
        ∀ M' : Subgroup G, quasithinIsMaxTwoLocal M' → conjClosure L T ⊔ T ≤ M' →
          M' = Subgroup.normalizer (conjClosure L T : Set G)) ∧
      ∀ I : Subgroup G, IsIrrPlusBase (conjClosure L T)
          (reducedAggregate (conjClosure L T ⊔ T)) I →
        ∃ V₀ : Subgroup G,
          IsIrrPlusIn (conjClosure L T) (reducedAggregate (conjClosure L T ⊔ T)) T V₀ ∧
          IsXSectionIso₂ (conjClosure L T)
            V₀ (V₀ ⊓ Subgroup.centralizer (conjClosure L T : Set G))
            I (I ⊓ Subgroup.centralizer (conjClosure L T : Set G)) ∧
          FSU G T L V₀

@[expose] def Stmt3_2_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    L = conjClosure L T →
      (∃ _ : IsMulCommutative ↥(conjClosure V₀ T),
        qhatOf (V := ↥(conjClosure V₀ T)) (autOn (L ⊔ T) (conjClosure V₀ T)) ≤ 2) ∧
      (∃ _ : IsMulCommutative ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))),
        qhatOf (V := ↥(conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))))
          (autOn (Subgroup.normalizer (L : Set G))
            (conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)))) ≤ 2) ∧
      ((V₀ = conjClosure V₀ T ∧
          conjClosure V₀ T = conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G))) ∨
        (V₀ = conjClosure V₀ T ∧ V₀ ≤ T ∧ T ≤ Subgroup.normalizer (V₀ : Set G) ∧
          V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
          ∀ g ∈ Subgroup.normalizer (L : Set G), g ∉ Subgroup.normalizer (V₀ : Set G) →
            V₀ ⊓ CFSG.conjugate V₀ g = ⊥) ∨
        (V₀ ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧
          ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
              Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 3 n) ∨
            (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
              Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* ↥(StatedSp 2 K)) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSp4 (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* alternatingGroup (Fin 6)) ∧
              ∃ _ : IsMulCommutative ↥V₀, AlternatingNatural (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 6) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃*
                Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 4 1) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃*
                Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
              ∃ _ : IsMulCommutative ↥V₀, BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 5 1) ∨
            (Nonempty (↥(autOn L (conjClosure V₀ T)) ≃* alternatingGroup (Fin 7)) ∧
              Nat.card V₀ = 2 ^ 4)) ∧
          (∃ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G)) ∧
          ∀ t ∈ T, t ∉ Subgroup.normalizer (V₀ : Set G) →
            conjClosure (conjClosure V₀ T) (Subgroup.normalizer (L : Set G)) =
                conjClosure V₀ T ∧
              conjClosure V₀ T = V₀ ⊔ CFSG.conjugate V₀ t ∧ V₀ ⊓ CFSG.conjugate V₀ t = ⊥ ∧
              ¬ IsXSectionIso₂ L V₀ ⊥ (CFSG.conjugate V₀ t) ⊥))

@[expose] def Stmt3_2_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V₀ : Subgroup G), FSU G T L V₀ →
    L = conjClosure L T → V₀ = conjClosure V₀ T →
    (∃ _ : IsMulCommutative ↥V₀,
      IsFFModule (V := ↥V₀) (Subgroup.normalizer ((autOn L V₀ : Set (MulAut ↥V₀))))) →
      ∃ _ : IsMulCommutative ↥V₀,
        (∃ n : ℕ, LieModel ↥(autOn L V₀) .PSL 2 2 n ∧
          BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf V₀) 2 n) ∨
        ((∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
            Nonempty (↥(autOn L V₀) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
            BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 3 n) ∨
          (Nonempty (↥(autOn L V₀) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
            Nat.card V₀ = 2 ^ 4 ∧
            BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤
              ((Subgroup.centralizer (L : Set G)).subgroupOf V₀) 3 1)) ∨
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L V₀) ≃* ↥(StatedSp 2 K)) ∧
          BinaryNaturalSp4 (V := ↥V₀) (autOn L V₀) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf V₀) n) ∨
        (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L V₀) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧
          G2NaturalDerived (V := ↥V₀) (autOn L V₀) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf V₀) n) ∨
        ((Nonempty (↥(autOn L V₀) ≃* alternatingGroup (Fin 5)) ∧
            AlternatingNatural (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 5) ∨
          (Nonempty (↥(autOn L V₀) ≃* alternatingGroup (Fin 7)) ∧
            AlternatingNatural (V := ↥V₀) (autOn L V₀) ⊤ ⊥ 7)) ∨
        (Nonempty (↥(autOn L V₀) ≃* alternatingGroup (Fin 6)) ∧
          AlternatingNatural (V := ↥V₀) (autOn L V₀) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf V₀) 6) ∨
        (Nonempty (↥(autOn (L ⊔ T) V₀) ≃* alternatingGroup (Fin 7)) ∧ Nat.card V₀ = 2 ^ 4) ∨
        (Group.IsPerfect ↥(autOn L V₀) ∧ Nat.card (Subgroup.center ↥(autOn L V₀)) = 3 ∧
          Nonempty (↥(autOn L V₀) ⧸ Subgroup.center ↥(autOn L V₀) ≃*
            alternatingGroup (Fin 6)) ∧
          Nat.card V₀ = 2 ^ 6) ∨
        (∃ n : ℕ, (n = 4 ∨ n = 5) ∧
          Nonempty (↥(autOn (L ⊔ T) V₀) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
          BinaryNaturalSL (V := ↥V₀) (autOn L V₀) ⊤ ⊥ n 1) ∨
        (Nonempty (↥(autOn L V₀) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) ∧
          SLExteriorTwo (V := ↥V₀) (autOn L V₀) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf V₀) 4) ∨
        (Nonempty (↥(autOn (L ⊔ T) V₀) ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)) ∧
          Nat.card V₀ = 2 ^ 10)

@[expose] def Stmt4_4_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L B Tp VB : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    B ≤ M → B ≠ ⊥ → IsMulCommutative ↥B → Odd (Nat.card B) →
    ⁅conjClosure L T, B⁆ ≤ pCoreOf 2 (conjClosure L T) →
    Tp ≤ T → (B : Set G) * (Tp : Set G) = (Tp : Set G) * (B : Set G) →
    (L : Set G) * (T : Set G) = (L : Set G) * (Tp : Set G) →
    VB ≤ quasithinOmegaOneCenter (pCoreOf 2 (conjClosure L T ⊔ T)) →
    conjClosure L T ⊔ T ≤ Subgroup.normalizer (VB : Set G) →
    VB = ⁅VB, conjClosure L T⁆ → VB ≠ ⊥ → ⁅VB, B⁆ = ⊥ →
      Subgroup.normalizer (B : Set G) ≤ M ∨
      (M ≤ Subgroup.normalizer (L : Set G) ∧
        ((∃ n : ℕ, 2 ≤ n ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∨
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)) ∨
          Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 7)) ∨
          (Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
            Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
              alternatingGroup (Fin 6))) ∨
          LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) ∧
        (((∃ _ : IsMulCommutative ↥VB, IsFFModule (V := ↥VB) (autOn (L ⊔ T) VB)) ∧
            (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 → IsNaturalSumUnder 3 L VB) ∧
            (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 →
              IsNaturalSumUnder 4 L VB ∨
                ∃ _ : IsMulCommutative ↥VB, SLExteriorTwo (V := ↥VB) (autOn L VB) ⊤ ⊥ 4) ∧
            ((Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
                Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
                Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
                  alternatingGroup (Fin 6))) →
              ∀ z ∈ VB ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G), orderOf z = 2 →
                ¬ VB ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∧
            (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 → Nat.card VB = 2 ^ 6 →
              ∃ V₃ : Subgroup G, V₃ ≤ VB ∧ Nat.card V₃ = 2 ^ 3 ∧
                T ⊓ L ≤ Subgroup.normalizer (V₃ : Set G) ∧
                  ¬ Subgroup.centralizer (V₃ : Set G) ≤ M)) ∨
          (∃ m : ℕ, 1 ≤ m ∧ LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 (2 * m) ∧
            ∃ _ : IsMulCommutative ↥VB, BinaryOrthogonalFour (V := ↥VB) (autOn L VB) ⊤ ⊥ m) ∨
          (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∧
            ∃ _ : IsMulCommutative ↥VB, FanoCoreModule (V := ↥VB) (autOn L VB) ⊤ ⊥)))

end CFSG.Quasithin.H13
