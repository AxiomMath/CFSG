module

public import CFSG.Quasithin.H13.StatementsL6
public import CFSG.Quasithin.Vol2.Ch4Sec2W4213Orth

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped IsMulCommutative Pointwise Matrix

@[expose] def Concl443TwoI (G : Type) [Group G] (T M L VB : Subgroup G) : Prop :=
  M ≤ Subgroup.normalizer (L : Set G) ∧
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
    ((∃ _ : IsMulCommutative ↥VB, IsFFModule (V := ↥VB) (autOn (L ⊔ T) VB)) ∧
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
          T ⊓ L ≤ Subgroup.normalizer (V₃ : Set G) ∧ ¬ Subgroup.centralizer (V₃ : Set G) ≤ M))

@[expose] def IrrCase4213 (G : Type) [Group G] (L V : Subgroup G) : Prop :=
  ((Group.IsPerfect (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 6))) ∨
    LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1 ∨
    (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∧
      ∃ _ : IsMulCommutative ↥V, SLExteriorTwo (V := ↥V) (autOn L V) ⊤ ⊥ 4)) →
    ∀ W : Subgroup G, V ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ V →
      L ≤ Subgroup.normalizer (W : Set G) →
        W = V ⊓ Subgroup.centralizer (L : Set G) ∨ W = V

@[expose] def Stmt4_2_13Strong : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L I : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    I ≤ M → (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) →
    (∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i) →
    (∀ i ∈ I, ∃ t ∈ T, CFSG.conjugate L i = CFSG.conjugate L t) →
    pCoreOf 2 I ≠ ⊥ →
      IsUniqueM I M ∨
      ((M ≤ Subgroup.normalizer (L : Set G) ∧
        ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
          IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
            (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) ∧
          ((∃ n : ℕ, LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
            (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∧
              ∃ k : ℕ, 1 ≤ k ∧ DirectSumOfCopies (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
                (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤
                ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅reducedAggregate (L ⊔ T), L⁆)
                (FFModel.nat (StatedSL 3 (ZMod 2))) k) ∨
            (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∧
              ((∃ k : ℕ, 1 ≤ k ∧ DirectSumOfCopies (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
                  (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤
                  ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅reducedAggregate (L ⊔ T), L⁆)
                  (FFModel.nat (StatedSL 4 (ZMod 2))) k) ∨
                SLExteriorTwo (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
                  (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤
                  ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅reducedAggregate (L ⊔ T), L⁆)
                  4)) ∨
            (IsA6Block (oTwoUpper (I ⊓ L)) ∨ IsExcA7Block (oTwoUpper (I ⊓ L))) ∨
            (IsHatA6Block (oTwoUpper (I ⊓ L)) ∧
              ∀ z ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
                ¬ ⁅reducedAggregate (L ⊔ T), L⁆ ≤
                  pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∨
            (IsG2Block (oTwoUpper (I ⊓ L)) ∧
              (Nat.card ↥⁅reducedAggregate (L ⊔ T), L⁆ = 2 ^ 6 →
                ∃ V₃ : Subgroup G, V₃ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ ∧
                  Nat.card V₃ = 2 ^ 3 ∧ T ⊓ I ≤ Subgroup.normalizer (V₃ : Set G) ∧
                    ¬ Subgroup.centralizer (V₃ : Set G) ≤ M)))) ∧
        Concl443TwoI G T M L ⁅reducedAggregate (L ⊔ T), L⁆ ∧
        IrrCase4213 G L ⁅reducedAggregate (L ⊔ T), L⁆)

theorem stmt4_2_13_of_strong (h : Stmt4_2_13Strong) :
    ∀ (G : Type) [Group G] [Finite G] (T M L I : Subgroup G), IsSimpleGroup G →
      (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
      quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
      quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
      CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
      I ≤ M → (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) →
      (∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i) →
      (∀ i ∈ I, ∃ t ∈ T, CFSG.conjugate L i = CFSG.conjugate L t) →
      pCoreOf 2 I ≠ ⊥ →
        IsUniqueM I M ∨
        (M ≤ Subgroup.normalizer (L : Set G) ∧
          ∃ _ : IsMulCommutative ↥⁅reducedAggregate (L ⊔ T), L⁆,
            IsFFModule (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
              (autOn (L ⊔ T) ⁅reducedAggregate (L ⊔ T), L⁆) ∧
            ((∃ n : ℕ, LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 2 2 n) ∨
              (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1 ∧
                ∃ k : ℕ, 1 ≤ k ∧ DirectSumOfCopies (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
                  (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤
                  ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅reducedAggregate (L ⊔ T), L⁆)
                  (FFModel.nat (StatedSL 3 (ZMod 2))) k) ∨
              (LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 4 2 1 ∧
                ((∃ k : ℕ, 1 ≤ k ∧ DirectSumOfCopies (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
                    (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤
                    ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅reducedAggregate (L ⊔ T), L⁆)
                    (FFModel.nat (StatedSL 4 (ZMod 2))) k) ∨
                  SLExteriorTwo (V := ↥⁅reducedAggregate (L ⊔ T), L⁆)
                    (autOn L ⁅reducedAggregate (L ⊔ T), L⁆) ⊤
                    ((Subgroup.centralizer (L : Set G)).subgroupOf ⁅reducedAggregate (L ⊔ T), L⁆)
                    4)) ∨
              (IsA6Block (oTwoUpper (I ⊓ L)) ∨ IsExcA7Block (oTwoUpper (I ⊓ L))) ∨
              (IsHatA6Block (oTwoUpper (I ⊓ L)) ∧
                ∀ z ∈ ⁅reducedAggregate (L ⊔ T), L⁆ ⊓ Subgroup.centralizer (T : Set G), z ≠ 1 →
                  ¬ ⁅reducedAggregate (L ⊔ T), L⁆ ≤
                    pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) ∨
              (IsG2Block (oTwoUpper (I ⊓ L)) ∧
                (Nat.card ↥⁅reducedAggregate (L ⊔ T), L⁆ = 2 ^ 6 →
                  ∃ V₃ : Subgroup G, V₃ ≤ ⁅reducedAggregate (L ⊔ T), L⁆ ∧
                    Nat.card V₃ = 2 ^ 3 ∧ T ⊓ I ≤ Subgroup.normalizer (V₃ : Set G) ∧
                      ¬ Subgroup.centralizer (V₃ : Set G) ≤ M)))) := by
  intro G _ _ T M L I hs hnab hK hT hM hTM hL hLf hLM hq hIM hLI hTI hIT hI
  exact (h G T M L I hs hnab hK hT hM hTM hL hLf hLM hq hIM hLI hTI hIT hI).imp_right And.left

@[expose] def Stmt4_2_13FF : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L I : Subgroup G), IsSimpleGroup G →
    (∃ a b : G, a * b ≠ b * a) → QuasithinUnique.quasithinIsQTKECat G →
    quasithinIsSylowTwo T → quasithinIsMaxTwoLocal M → T ≤ M →
    quasithinIsMaximalLocal T L → quasithinIsFaithfulLocal T L → L ≤ M →
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) →
    I ≤ M → (L : Set G) ⊆ (I : Set G) * (pCoreOf 2 (L ⊔ T) : Set G) →
    (∀ t ∈ T, ∃ i ∈ I, CFSG.conjugate L t = CFSG.conjugate L i) →
    (∀ i ∈ I, ∃ t ∈ T, CFSG.conjugate L i = CFSG.conjugate L t) →
    pCoreOf 2 I ≠ ⊥ →
      IsUniqueM I M ∨ ((Concl443TwoI G T M L ⁅reducedAggregate (L ⊔ T), L⁆ ∧
        IrrCase4213 G L ⁅reducedAggregate (L ⊔ T), L⁆) ∨
        Orth4213 G M L ⁅reducedAggregate (L ⊔ T), L⁆)

theorem stmt4_2_13FF_of_strong (h : Stmt4_2_13Strong) : Stmt4_2_13FF := by
  intro G _ _ T M L I hs hnab hK hT hM hTM hL hLf hLM hq hIM hLI hTI hIT hI
  exact (h G T M L I hs hnab hK hT hM hTM hL hLf hLM hq hIM hLI hTI hIT hI).imp_right
    fun h => Or.inl h.2

end CFSG.Quasithin.H13
