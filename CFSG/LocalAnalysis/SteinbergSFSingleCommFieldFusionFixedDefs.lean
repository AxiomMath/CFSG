module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommFieldFusionDefs
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCElementaryCoset

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace SingleCommParts

open Subgroup GomiFusion
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.ComponentInitial (sectionRightConj)

section FixedDefs

structure ScalarLayer {G : Type*} [Group G] {K : Type*} [Field K] (μ : Kˣ →* G)
    (W W' : Subgroup G) (c : G → K) : Prop where
  map_mul : ∀ x ∈ W, ∀ y ∈ W, c (x * y) = c x + c y
  ker : ∀ x ∈ W, c x = 0 ↔ x ∈ W'
  surj : ∀ k : K, ∃ y ∈ W, c y = k
  equiv : ∀ (l : Kˣ), ∀ x ∈ W, c ((μ l)⁻¹ * x * μ l) = (l : K) * c x

@[expose] def ffUChar {K : Type*} [Field K] (k : Axis) (r s : K) : K :=
  match k with
  | .one => r * s
  | .two => r ^ 2

@[expose] def ffAChar {K : Type*} [Field K] (k : Axis) (r s : K) : K :=
  match k with
  | .one => s ^ 2
  | .two => r * s⁻¹

section OneParam

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]

@[expose] def ffIsOneParam (φ : L ≃* antiSp K) (μ : Kˣ →* G) (f g : Kˣ →* Kˣ) : Prop :=
  ∀ (l : Kˣ) (a b c d : K), (μ l)⁻¹ * ((φ.symm (uElt a b c d) : L) : G) * μ l =
    ((φ.symm (uElt ((f l : K) * (g l : K)⁻¹ * a) ((f l : K) * (g l : K) * b)
      ((f l : K) ^ 2 * c) ((g l : K) ^ 2 * d)) : L) : G)

end OneParam

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2] [Finite K]

@[expose] def FF8FactorConcl (n : ℕ) (φ : L ≃* antiSp K) (t : G) (i : Axis) (k : Fin 6) : Prop :=
  ∀ v₀ : G, v₀ * v₀ = 1 → v₀ ∈ centralizer ({t} : Set G) →
    (∀ l : L, ((φ.symm ((frobAut K ^ (n / 2)) (φ l)) : L) : G) = v₀ * l * v₀⁻¹) → Even n →
      ∀ (h1 : v₀ ∈ normalizer (ffSeries φ t i k.succ : Set G))
        (h0 : v₀ ∈ normalizer (ffSeries φ t i k.castSucc : Set G))
        [((ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ)).Normal],
        Nat.card {q : ↥(ffSeries φ t i k.succ) ⧸
            (ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ) |
          sectionRightConj h1 h0 q = q} ^ 2 =
          Nat.card (↥(ffSeries φ t i k.succ) ⧸
            (ffSeries φ t i k.castSucc).subgroupOf (ffSeries φ t i k.succ))

end FixedDefs

end SingleCommParts

end CFSG.LocalAnalysis.SymplecticFourStandard
