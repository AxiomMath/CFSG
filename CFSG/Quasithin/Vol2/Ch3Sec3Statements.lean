module

public import CFSG.Quasithin.Vol2.Ch3Sec3Setup
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.C2Blocks

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped IsMulCommutative Pointwise

variable {G : Type} [Group G]

abbrev cvPlus (L T : Subgroup G) : Subgroup ↥(vPlus L T) :=
  (Subgroup.centralizer (mPlus L T : Set G)).subgroupOf (vPlus L T)

abbrev commVPlus (L T X : Subgroup G) : Subgroup ↥(vPlus L T) :=
  (⁅vPlus L T, X⁆).subgroupOf (vPlus L T)

abbrev tildeComm (L T X : Subgroup G) : Subgroup ↥(vPlus L T) :=
  commVPlus L T X ⊔ cvPlus L T

@[expose] def Stmt3_3_5 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L : Subgroup G), Setup331 G T M L →
    M = Subgroup.normalizer (mPlus L T : Set G) ∧ IsUniqueM (mPlus L T ⊔ T) M ∧
      quasithinGenFitting (mPlus L T ⊔ T) = pCoreOf 2 (mPlus L T ⊔ T)

@[expose] def Stmt3_3_6 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ¬ D ≤ M ∧
    (pCoreOf 2 (mPlus L T ⊔ T ⊔ D) = ⊥ ∧
      ∀ X : Subgroup G, X ≠ ⊥ → X ≤ mPlus L T ⊔ T →
        mPlus L T ⊔ T ≤ Subgroup.normalizer (X : Set G) →
          ¬ D ≤ Subgroup.normalizer (X : Set G)) ∧
    (∀ C : Subgroup G, C ≤ T → C ≠ ⊥ → (C.subgroupOf T).Characteristic →
      ¬ mPlus L T ⊔ T ≤ Subgroup.normalizer (C : Set G)) ∧
    (IsRankTwoLie2Derived ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) →
      (¬ IsPSL 3 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) → T ≤ Subgroup.normalizer (L : Set G)) ∧
      (T ≤ Subgroup.normalizer (L : Set G) → IsMSPair (L ⊔ T) T))

@[expose] def Stmt3_3_7 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ((mPlus L T ⊔ T) ⊓ Subgroup.centralizer (vPlus L T : Set G) ≤ oTwoPhi (mPlus L T ⊔ T) ∧
      T ⊓ Subgroup.centralizer (vPlus L T : Set G) = pCoreOf 2 (mPlus L T ⊔ T)) ∧
    (¬ thompsonJ T ≤ Subgroup.centralizer (vPlus L T : Set G) ∧
      ∃ _ : IsMulCommutative ↥(vPlus L T),
        IsFFModule (V := ↥(vPlus L T)) (autOn (mPlus L T ⊔ T) (vPlus L T))) ∧
    (vPlus L T ≤ mPlus L T ⊔ T ∧ IsPrimeReduced 2 ((vPlus L T).subgroupOf (mPlus L T ⊔ T)) ∧
      pCoreOf 2 (autOn (mPlus L T ⊔ T) (vPlus L T)) = ⊥) ∧
    (⁅vPlus L T, mPlus L T⁆ = ⁅quasithinOmegaOneCenter T, mPlus L T⁆ ∧
      vPlus L T = ⁅vPlus L T, mPlus L T⁆ ⊔
        quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (mPlus L T : Set G))

@[expose] def Case3_3_8_one (T L : Subgroup G) [IsMulCommutative ↥(vPlus L T)] : Prop :=
  ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧ mPlus L T = L ⊔ CFSG.conjugate L t ∧
    (∀ a ∈ autOn L (vPlus L T), ∀ b ∈ autOn (CFSG.conjugate L t) (vPlus L T), a * b = b * a) ∧
    autOn L (vPlus L T) ⊓ autOn (CFSG.conjugate L t) (vPlus L T) = ⊥ ∧
    ((∃ n : ℕ, LieModel ↥(autOn L (vPlus L T)) .PSL 2 2 n) ∨
      IsPSL 3 2 1 ↥(autOn L (vPlus L T))) ∧
    tildeComm L T (mPlus L T) = tildeComm L T L ⊔ tildeComm L T (CFSG.conjugate L t) ∧
    tildeComm L T L ⊓ tildeComm L T (CFSG.conjugate L t) = cvPlus L T ∧
    ((∃ n : ℕ, BinaryNaturalSL (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) 2 n) ∨
      AlternatingNatural (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) 5 ∨
      BinaryNaturalSL (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T) 3 1 ∨
      DirectSumOfCopies (autOn L (vPlus L T)) (tildeComm L T L) (cvPlus L T)
        (FFModel.nat (StatedSL 3 (ZMod 2))) 2)

@[expose] def Case3_3_8_four (T L : Subgroup G) [IsMulCommutative ↥(vPlus L T)] : Prop :=
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* ↥(StatedSL 3 K)) ∧
      (BinaryNaturalSL (autOn (mPlus L T) (vPlus L T)) (tildeComm L T (mPlus L T))
          (cvPlus L T) 3 n ∨
        DirectSumOfCopies (autOn (mPlus L T) (vPlus L T)) (tildeComm L T (mPlus L T))
          (cvPlus L T) (FFModel.nat (StatedSL 3 K)) 2)) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 < n ∧ Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* ↥(StatedSp 2 K)) ∧
      BinaryNaturalSp4 (autOn (mPlus L T) (vPlus L T)) (tildeComm L T (mPlus L T))
        (cvPlus L T) n) ∨
  (Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 6)) ∧
      AlternatingNatural (autOn (mPlus L T) (vPlus L T)) (tildeComm L T (mPlus L T))
        (cvPlus L T) 6) ∨
  (∃ (n : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧
      G2NaturalDerived (autOn (mPlus L T) (vPlus L T)) (tildeComm L T (mPlus L T))
        (cvPlus L T) n)

@[expose] def Stmt3_3_8 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∃ _ : IsMulCommutative ↥(vPlus L T),
      Case3_3_8_one T L ∨
      (∃ n : ℕ, 1 < n ∧ LieModel ↥(autOn (mPlus L T) (vPlus L T)) .PSL 2 2 n ∧
        BinaryNaturalSL (autOn (mPlus L T) (vPlus L T)) (tildeComm L T (mPlus L T))
          (cvPlus L T) 2 n) ∨
      ((Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 5)) ∧
          AlternatingNatural (autOn (mPlus L T) (vPlus L T)) (commVPlus L T (mPlus L T)) ⊥ 5) ∨
        (Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 7)) ∧
          AlternatingNatural (autOn (mPlus L T) (vPlus L T)) (commVPlus L T (mPlus L T)) ⊥ 7)) ∨
      Case3_3_8_four T L ∨
      (Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 7)) ∧
        Nat.card ↥⁅vPlus L T, mPlus L T⁆ = 2 ^ 4) ∨
      (Group.IsPerfect ↥(autOn (mPlus L T) (vPlus L T)) ∧
        Nat.card (Subgroup.center ↥(autOn (mPlus L T) (vPlus L T))) = 3 ∧
        Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ⧸
          Subgroup.center ↥(autOn (mPlus L T) (vPlus L T)) ≃* alternatingGroup (Fin 6)) ∧
        Nat.card ↥⁅vPlus L T, mPlus L T⁆ = 2 ^ 6) ∨
      (∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (↥(autOn (mPlus L T) (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) ∧
        B51Part1 (ffJ (autOn (mPlus L T ⊔ T) (vPlus L T))) (autOn (mPlus L T) (vPlus L T)))

@[expose] def Stmt3_3_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    mPlus L T ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) =
      mPlus L T ⊓ Subgroup.centralizer
        ((quasithinOmegaOneCenter T ⊓ ⁅vPlus L T, mPlus L T⁆ : Subgroup G) : Set G)

@[expose] def Stmt3_3_10 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    (∀ H : Subgroup G, InH T H → (∃ K : Subgroup G, IsUniqueMaxOver H T K) →
      pCoreOf 2 (H ⊔ D) ≠ ⊥) ∧
    (∀ n : ℕ, ¬ LieModel ↥(autOn (mPlus L T) (vPlus L T)) .PSL 2 2 n) ∧
    (¬ T ≤ Subgroup.normalizer (L : Set G) → IsPSL 3 2 1 ↥(autOn L (vPlus L T)))

@[expose] def OuterU35Action (D K : Subgroup G) : Prop :=
  Nat.card D = 3 ∧
    (∀ d ∈ D, d ≠ 1 → ¬ ∃ k ∈ K, ∀ x ∈ K, (d * x * d⁻¹) * (k * x * k⁻¹)⁻¹ ∈ pCoreOf 2 K) ∧
    ∃ C : Subgroup G, pCoreOf 2 K ≤ C ∧ C ≤ K ∧
      (∀ d ∈ D, ∀ c ∈ C, d * c * d⁻¹ * c⁻¹ ∈ pCoreOf 2 K) ∧
      ∃ _ : ((pCoreOf 2 K).subgroupOf C).Normal,
        IsDoubleCoverS5NotGL25 (↥C ⧸ (pCoreOf 2 K).subgroupOf C)

@[expose] def Stmt3_3_13 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D H : Subgroup G), Hyp331 G T M L D →
    InH T H → Nonempty (↥H ⧸ CFSG.pCore 2 ↥H ≃* ↥wreathS3Z2) →
      D ≤ Subgroup.normalizer (H : Set G)

@[expose] def Stmt3_3_14 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    mPlus L T = L ∧ M ≤ Subgroup.normalizer (L : Set G)

end CFSG.Quasithin.H13
