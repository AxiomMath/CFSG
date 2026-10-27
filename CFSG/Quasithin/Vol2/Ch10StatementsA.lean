module

public import CFSG.Quasithin.H13.StatementsCh7
public import CFSG.Quasithin.H13.StatementsL4
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative

@[expose] def StmtIrrPlusNonempty : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      ∃ I : Subgroup G,
        IsIrrPlusBase (conjClosure L T) (reducedAggregate (conjClosure L T ⊔ T)) I

@[expose] def StmtFSUChoice : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) → ∃ I : Subgroup G, FSU G T L I

theorem stmtFSUChoice_of (h323 : Stmt3_2_3) (hne : StmtIrrPlusNonempty) : StmtFSUChoice := by
  intro G _ _ T L hs hn hq hT hmax hf hqs
  obtain ⟨I, hI⟩ := hne G T L hs hn hq hT hmax hf hqs
  obtain ⟨V₀, -, -, hfsu⟩ := (h323 G T L hs hn hq hT hmax hf hqs).2.2 I hI
  exact ⟨V₀, hfsu⟩

section Notation

variable {G : Type} [Group G]

@[expose] def IsLi (T L K : Subgroup G) : Prop :=
  K = L ∨ ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) ∧ K = CFSG.conjugate L t

abbrev T0 (T L : Subgroup G) : Subgroup G :=
  T ⊓ fsuL0 T L

abbrev T1 (T L : Subgroup G) : Subgroup G :=
  T ⊓ Subgroup.normalizer (L : Set G)

abbrev B0 (T L : Subgroup G) : Subgroup G :=
  oTwoUpper (fsuL0 T L ⊓ Subgroup.normalizer (T0 T L : Set G))

abbrev cV1 (T L I : Subgroup G) : Subgroup ↥(fsuUL T L I) :=
  (Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (fsuUL T L I)

end Notation

structure Hyp10 (G : Type) [Group G] [Finite G] (T L I : Subgroup G) : Prop where
  fsu : FSU G T L I
  not_normal : ¬ T ≤ Subgroup.normalizer (L : Set G)
  lt : L < fsuL0 T L
  three : Concl326Three T L I

section Cases

variable {G : Type} [Group G] (T L I : Subgroup G)

@[expose] def Case10_1_1One (n : ℕ) : Prop :=
  1 < n ∧ (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
    ∃ _ : IsMulCommutative ↥(fsuUL T L I),
      BinaryNaturalSL (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ (cV1 T L I) 2 n

@[expose] def Case10_1_1Two : Prop :=
  Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 5)) ∧
    ∃ _ : IsMulCommutative ↥(fsuUL T L I),
      AlternatingNatural (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥ 5

@[expose] def Case10_1_1Three : Prop :=
  Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    ∃ _ : IsMulCommutative ↥(fsuUL T L I),
      BinaryNaturalSL (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ (cV1 T L I) 3 1

@[expose] def Case10_1_1Four (n : ℕ) : Prop :=
  1 < n ∧ (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * n) ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
    ∃ _ : IsMulCommutative ↥(fsuUL T L I),
      BinaryOrthogonalFour (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥ n

@[expose] def Case10_1_1Five : Prop :=
  Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    ∃ s ∈ T, s ∈ Subgroup.normalizer (L : Set G) ∧ ∃ W : Subgroup G, W ≤ fsuUL T L I ∧
      L ≤ Subgroup.normalizer (W : Set G) ∧ W ⊔ CFSG.conjugate W s = fsuUL T L I ∧
      W ⊓ CFSG.conjugate W s = ⊥ ∧
      (∃ _ : IsMulCommutative ↥W, BinaryNaturalSL (V := ↥W) (autOn L W) ⊤ ⊥ 3 1) ∧
      ¬ IsXSectionIso L ⊥ W (CFSG.conjugate W s)

@[expose] def Case10_1_1Six : Prop :=
  Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) ∧
    ∃ _ : IsMulCommutative ↥(fsuVM T L I),
      DirectSumOfCopies (V := ↥(fsuVM T L I)) (autOn L (fsuVM T L I))
          ((fsuUL T L I).subgroupOf (fsuVM T L I)) ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4 ∧
      (Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
            Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
              Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5)) ∨
        Nonempty (↥(twoResidual (autOn (fsuM T L) (fsuVM T L I) ⊓
            Subgroup.centralizer (autOn (fsuL0 T L) (fsuVM T L I) :
              Set (MulAut ↥(fsuVM T L I))))) ≃* Multiplicative (ZMod 5 × ZMod 5)))

@[expose] def Case10_1_1Seven : Prop :=
  ∃ n : ℕ, CFSG.Blueprint.SuzukiModel (↥L ⧸ CFSG.pCore 2 ↥L) 2 n ∧
    ∃ _ : IsMulCommutative ↥(fsuUL T L I),
      BinaryNaturalSz (V := ↥(fsuUL T L I)) (autOn L (fsuUL T L I)) ⊤ ⊥ n

@[expose] def Cases10_1_1 : Prop :=
  (∃ n, Case10_1_1One T L I n) ∨ Case10_1_1Two T L I ∨ Case10_1_1Three T L I ∨
    (∃ n, Case10_1_1Four T L I n) ∨ Case10_1_1Five T L I ∨ Case10_1_1Six T L I ∨
    Case10_1_1Seven T L I

end Cases

end CFSG.Quasithin.Vol2.Ch10
