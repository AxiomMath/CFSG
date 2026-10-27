module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.RankThree.GroupTheory.SteinbergBMSectionTenSetup
public import CFSG.RankThree.GroupTheory.SteinbergCESectionTenStrata

public section

namespace CFSG.RankThree.PartOne.HNRed

open Subgroup CFSG CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.RankThree.GroupTheory
open CFSG.Blueprint.NativeSporadic (Carrier IsSporadic SporadicRep)

@[expose] def fixedSubgroup {T : Type} [Group T] (β : MulAut T) : Subgroup T where
  carrier := {t | β t = t}
  mul_mem' := fun {a b} ha hb => by
    show β (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := map_one β
  inv_mem' := fun {a} ha => by
    show β a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

@[expose] def IsOrdinaryComponentOf {T : Type} [Group T] (K C : Subgroup T) : Prop :=
  K ≤ C ∧ CFSG.IsComponent (K.subgroupOf C)

@[expose] def FiveFixedPSU3 {T : Type} [Group T] (β : MulAut T) (K : Subgroup T) : Prop :=
  orderOf β = 5 ∧ IsOrdinaryComponentOf K (fixedSubgroup β) ∧ StatedClassicalModel K .PSU 3 5 1

@[expose] def HNPerfectCoverCenterless : Prop :=
  ∀ (G : Type) [Group G] [Finite G], CFSG.twoLocalOddRank G ≤ 3 →
    ∀ (X : Subgroup G), Group.IsPerfect X → ∀ (S : Type) [Group S] (π : X →* S),
      Function.Surjective π → IsSporadic S .HN → π.ker ≤ Subgroup.center X → π.ker = ⊥

@[expose] def OriginalHNNotIsomorphic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), SteinbergBM.SectionTenSetup G 5 A →
    ∀ L ∈ sectionTenZeroStar 5 A, ¬ Nonempty (Carrier .HN ≃* L)

@[expose] def AlternatingFullCentralKernel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (K : Type) [Group K] (ι : K →* G), Function.Injective ι →
    ∀ n : ℕ, 5 ≤ n → ∀ π : K →* alternatingGroup (Fin n), Function.Surjective π →
      π.ker ≤ Subgroup.center K → ((10 ≤ n ∧ 3 ∣ Nat.card π.ker) ∨ (12 ≤ n ∧ 2 ∣ Nat.card π.ker)) →
        4 ≤ CFSG.twoLocalOddRank G

@[expose] def HNFiveKernelTrivial : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → ∀ (S : Type) [Group S]
    (f : X →* S), Function.Surjective f → IsSporadic S .HN → f.ker ≤ Subgroup.center X →
      ¬ 5 ∣ Nat.card f.ker

@[expose] def HNSuccessorTransport : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G), SteinbergBM.SectionTenSetup G 5 A →
    ∀ L ∈ sectionTenZeroStar 5 A, Nonempty (Carrier .HN ≃* L) →
      ∃ (H : Subgroup G) (X : Subgroup H) (β : MulAut (X ⧸ Subgroup.center X))
        (Λ : Subgroup (MulAut (X ⧸ Subgroup.center X))) (K Y U : Subgroup (X ⧸ Subgroup.center X)),
        CFSG.twoLocalOddRank H ≤ 3 ∧ CFSG.IsQuasisimple X ∧
        Catalog (X ⧸ Subgroup.center X) ∧
        IsElementaryAbelian 5 Λ ∧ Nat.card Λ = 5 ^ 2 ∧ β ∈ Λ ∧ FiveFixedPSU3 β K ∧
        Y ≤ K ∧ Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) ∧
        U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ u ∈ U, β u ∈ U) ∧ (∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) ∧
        Subgroup.closure {x | ∃ u ∈ U, x = u⁻¹ * β u} = U

@[expose] def FiveFixedExcludesClassical : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      ∀ (β : MulAut (X ⧸ Subgroup.center X)) (K : Subgroup (X ⧸ Subgroup.center X)),
        FiveFixedPSU3 β K → ∀ (τ : StatedLieTag) (n ℓ f : ℕ),
          ¬ StatedClassicalModel (X ⧸ Subgroup.center X) τ n ℓ f

@[expose] def FiveFixedExcludesAlternating : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      ∀ (β : MulAut (X ⧸ Subgroup.center X)) (K : Subgroup (X ⧸ Subgroup.center X)),
        FiveFixedPSU3 β K → ∀ n : ℕ, 5 ≤ n →
          ¬ Nonempty ((X ⧸ Subgroup.center X) ≃* alternatingGroup (Fin n))

@[expose] def FiveFixedExcludesChevalley : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      ∀ (β : MulAut (X ⧸ Subgroup.center X)) (K : Subgroup (X ⧸ Subgroup.center X)),
        FiveFixedPSU3 β K → ∀ τ ∈ chevalleyExceptionalTags, ∀ ℓ f : ℕ,
          ¬ ChevalleyExceptionalModel (X ⧸ Subgroup.center X) τ ℓ f

@[expose] def FiveFixedExcludesSuzukiReeTits : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      ∀ (β : MulAut (X ⧸ Subgroup.center X)) (K : Subgroup (X ⧸ Subgroup.center X)),
        FiveFixedPSU3 β K → (∀ ℓ f : ℕ, ¬ SuzukiModel (X ⧸ Subgroup.center X) ℓ f) ∧
          ∀ τ ∈ reeTitsTags, ∀ ℓ f : ℕ, ¬ ReeTitsModel (X ⧸ Subgroup.center X) τ ℓ f

@[expose] def FiveFixedSporadicOnlyHN : Prop :=
  ∀ (H : Type) [Group H] [Finite H], CFSG.twoLocalOddRank H ≤ 3 →
    ∀ (X : Subgroup H), CFSG.IsQuasisimple X →
      ∀ (Λ : Subgroup (MulAut (X ⧸ Subgroup.center X))), IsElementaryAbelian 5 Λ →
        Nat.card Λ = 5 ^ 2 → ∀ β ∈ Λ, ∀ (K : Subgroup (X ⧸ Subgroup.center X)),
          FiveFixedPSU3 β K → SporadicRep (X ⧸ Subgroup.center X) →
            IsSporadic (X ⧸ Subgroup.center X) .HN

@[expose] def HNPrescribedBlockNormalizedTwo : Prop :=
  ∀ (T : Type) [Group T] [Finite T], IsSimpleGroup T → (∃ a b : T, a * b ≠ b * a) →
    IsSporadic T .HN → ∀ (β : MulAut T), orderOf β = 5 → ∀ K : Subgroup T,
      (∀ k ∈ K, β k = k) → StatedClassicalModel K .PSU 3 5 1 → ∀ Y : Subgroup T, Y ≤ K →
        Nonempty (Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) → ∀ U : Subgroup T,
          IsPGroup 2 U → (∀ u ∈ U, β u ∈ U) → (∀ y ∈ Y, ∀ u ∈ U, y * u * y⁻¹ ∈ U) →
            ∀ u ∈ U, β u = u

end CFSG.RankThree.PartOne.HNRed
