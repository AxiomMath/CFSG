module

public import CFSG.Quasithin.Vol2.Ch11StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch11

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp)
open scoped IsMulCommutative

@[expose] def Stmt11_0_2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ), Hyp11 G T L I n →
    ∃ _ : IsMulCommutative ↥(fsuV T I),
      IsIrrPlusBase L (reducedAggregate (L ⊔ T)) (fsuV T I) ∧
      T ≤ Subgroup.normalizer (fsuV T I : Set G) ∧
      Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* ↥(autOn L (fsuV T I))) ∧
      ((∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin 3) K) ∧
          ∃ π : ↥(StatedSL 3 K) →* ↥(autOn L (fsuV T I)),
            (FFModel.nat (StatedSL 3 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
              ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π ∧
            NoGraphAutomorphism π (autOn T (fsuV T I))) ∨
        (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (fsuV T I)) ≃* ↥(StatedSp 2 K)) ∧
          ∃ π : ↥(StatedSp 2 K) →* ↥(autOn L (fsuV T I)),
            (FFModel.nat (StatedSp 2 K)).RealizesVia (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
              ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) π ∧
            NoGraphAutomorphismSp4 π (autOn T (fsuV T I))) ∨
        (∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
          Nonempty (↥(autOn L (fsuV T I)) ≃* ↥⁅quasithinG2 K, quasithinG2 K⁆) ∧
          G2NaturalDerived (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤
            ((Subgroup.centralizer (L : Set G)).subgroupOf (fsuV T I)) n))

@[expose] def Stmt11_0_3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ), Hyp11 G T L I n →
    (VM T L I ≤ Subgroup.normalizer (L : Set G) ∧
      IsPrimeReduced 2 ((VM T L I).subgroupOf (Subgroup.normalizer (L : Set G)))) ∧
    (∀ m ∈ Subgroup.normalizer (L : Set G),
      IsXSectionIso₂ L (CFSG.conjugate (fsuV T I) m ⊔ cVM T L I) (cVM T L I)
        (fsuV T I ⊔ cVM T L I) (cVM T L I)) ∧
    ((fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥ ∧ cVM T L I = ⊥) ∨
      ((KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧ fsuV T I = VM T L I ∧
        E3.mQuot (fsuV T I ⊓ Subgroup.centralizer (L : Set G)) ⊥ ≤ n ∧
        L = ⁅L, thompsonJ T⁆)) ∧
    IsTISetIn (fsuV T I) (Subgroup.normalizer (L : Set G)) ∧
    (KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n →
      ∀ H : Subgroup G, IsHStar T (Subgroup.normalizer (L : Set G)) H →
        H ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (fsuV T I : Set G))

@[expose] def Stmt11_0_4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ), Hyp11 G T L I n →
    (∀ p : ℕ, p.Prime →
      ((KindSp4 L (fsuV T I) n ∨ KindG2 L (fsuV T I) n) ∧ p ∣ 2 ^ (2 * n) - 1 ∨
          KindSL3 L (fsuV T I) n ∧ p ∣ 2 ^ n - 1 ∧ 3 < p) →
        oPrimeResidualOf p (Subgroup.normalizer (L : Set G)) = L) ∧
    (KindSL3 L (fsuV T I) n → Even n →
      ∀ x ∈ Subgroup.normalizer (L : Set G), orderOf x = 3 →
        (x ∈ Subgroup.normalizer (fsuV T I : Set G) ∨ L = ⁅L, thompsonJ T⁆ ∨
          fsuV T I = VM T L I) → x ∈ L)

@[expose] def Stmt11_1_0 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L I : Subgroup G) (n : ℕ), Hyp11 G T L I n →
    (∀ i : ℕ, 1 ≤ i → i ≤ 3 → ∃! U : Subgroup G, IsVi T L I n i U) ∧
    (∀ i : ℕ, (i = 1 ∨ i = 2) → ∀ U : Subgroup G, IsVi T L I n i U →
      ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
        Nonempty (↥(LOf L U) ⧸ CFSG.pCore 2 ↥(LOf L U) ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧
    ∀ U₁ U₃ : Subgroup G, IsVi T L I n 1 U₁ → IsVi T L I n 3 U₃ →
      (KindSL3 L (fsuV T I) n → U₃ = fsuV T I) ∧
      (¬ KindSL3 L (fsuV T I) n →
        Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (U₃ : Set G) =
          Subgroup.normalizer (L : Set G) ⊓ Subgroup.normalizer (U₁ : Set G))

end CFSG.Quasithin.Vol2.Ch11
