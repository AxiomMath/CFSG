module

public import CFSG.RankThree.PartOne.S12.Sec138Local
public import CFSG.RankThree.PartOne.KF.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne.N143

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.RankThree.PartOne.KFU (torusSU)

@[expose] def HessianCase (p : ℕ) {G : Type} [Group G] (E : Subgroup G) : Prop :=
  ∀ s ∈ reflectionSet p E, ∀ t ∈ reflectionSet p E, s ≠ t → s * t ≠ t * s

@[expose] def IsScalarOrderThree (p : ℕ) {G : Type} [Group G] (A : Subgroup G) (z : G) : Prop :=
  z ∈ torusNormalizer A ∧ orderOf z = 3 ∧
    ∃ k : ℕ, k % p ≠ 1 ∧ k ^ 3 % p = 1 ∧ ∀ a ∈ A, z * a * z⁻¹ = a ^ k

structure HessCtx {G : Type} [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G)
    (L : Subgroup G) : Prop where
  hyp : Sec12Hyp G p A c L A
  facts12 : Sec12Facts G p A c L A
  facts13 : Sec13Facts G p A c L A
  notFive : ¬ Outcome152Five p A A (lieGenerated p A)
  allL3 : ∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J
  threeTransp : ThreeTranspD p A
  hess : HessianCase p A

@[expose] def Node143CommB2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → Sec12Facts G p A c L E → Sec13Facts G p A c L E →
    ¬ Outcome152Five p E A (lieGenerated p E) → E = A →
    (∀ J : Subgroup G, J ∈ sectionTenZeroStar p A → IsLThreeTypeAt p J) →
    ThreeTranspD p E → HessianCase p E →
    (∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 3 2 f ∧ 2 ^ f % 3 = 2) →
    ¬ 3 ∣ Nat.card (Subgroup.centralizer (A : Set G)) →
    ∀ x z : G, x ∈ L ⊓ torusNormalizer A → orderOf x = 3 → IsScalarOrderThree p A z →
      x * z = z * x →
        (Nat.card (Subgroup.centralizer
          ((Subgroup.zpowers x ⊔ Subgroup.zpowers z : Subgroup G) : Set G))).factorization 3 ≤
          (Nat.card L).factorization 3

@[expose] noncomputable def semilinMat {K : Type} [Field K] (g : GL (Fin 3) K) (σ : K ≃+* K)
    (e : Bool) (x : Matrix (Fin 3) (Fin 3) K) : Matrix (Fin 3) (Fin 3) K :=
  (g : Matrix (Fin 3) (Fin 3) K) * ((if e then Matrix.transpose x⁻¹ else x).map σ) *
    ((g⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

@[expose] def KFOut3 : Prop :=
  ∀ (f : ℕ), 3 ≤ f → ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 ^ f →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ∣ 2 ^ f - 1 →
    ∀ φ : StatedProj (StatedSL 3 K) ≃* StatedProj (StatedSL 3 K),
      (∀ x : ↥(StatedSL 3 K), (x : GL (Fin 3) K) ∈ torusSU p 3 K →
        ∃ y : ↥(StatedSL 3 K), (y : GL (Fin 3) K) ∈ torusSU p 3 K ∧
          φ (QuotientGroup.mk x) = QuotientGroup.mk y) →
      ∃ (g : GL (Fin 3) K) (σ : K ≃+* K) (e : Bool), ∀ x : ↥(StatedSL 3 K),
        ∃ y : ↥(StatedSL 3 K),
          ((y : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
            semilinMat g σ e ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ∧
          φ (QuotientGroup.mk x) = QuotientGroup.mk y

@[expose] def KF64W : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → CFSG.Assembly.evenRank H ≤ 3 →
    Group.IsPerfect H → ∀ p : ℕ, p.Prime → 7 ≤ p →
    CFSG.IsQuasisimple (H ⧸ aschbacherSolvableCore p H) →
    CFSG.Blueprint.EvenLieType
      ((H ⧸ aschbacherSolvableCore p H) ⧸ Subgroup.center (H ⧸ aschbacherSolvableCore p H)) →
    ∀ E : Subgroup H, CFSG.IsElementaryAbelian p E → Nat.card E = p ^ 3 →
      (∃ S : Subgroup H, S ≠ ⊥ ∧ IsPGroup 2 S ∧ E ≤ Subgroup.normalizer (S : Set H)) →
      (Nat.card (torusWeyl E)).factorization 3 ≤ 1

@[expose] def Item613 : Prop :=
  SchreierFor InCatalog →
  ∀ (H : Type) [Group H] [Finite H], CFSG.IsKGroup H → CFSG.Assembly.evenRank H ≤ 3 →
    ∀ p : ℕ, p.Prime → 7 ≤ p →
    ∀ L ∈ thetaComponents p H, ∀ E : Subgroup H, CFSG.IsElementaryAbelian p E →
      p ^ 2 ≤ Nat.card E → E ≤ L →
      (∃ S : Subgroup H, S ≠ ⊥ ∧ IsPGroup 2 S ∧ S ≤ L ∧
        ¬ S.subgroupOf L ≤ aschbacherSolvableCore p ↥L ∧
        E ≤ Subgroup.normalizer (S : Set H) ∧ ⁅S, E⁆ = S) →
      CFSG.Blueprint.EvenLieType
        ((L ⧸ aschbacherSolvableCore p L) ⧸ Subgroup.center (L ⧸ aschbacherSolvableCore p L))

end CFSG.RankThree.PartOne.N143
