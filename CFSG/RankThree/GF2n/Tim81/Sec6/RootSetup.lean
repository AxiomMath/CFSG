module

public import CFSG.RankThree.GF2n.Tim81.Sec5.Defs

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75

variable {K : Type} [Group K] [Finite K]

structure RootSetup (X : Subgroup K) (Δ : Set (Subgroup K)) (f : ℕ) : Prop where
  normal : X.Normal
  two_le : 2 ≤ f
  nonempty : Δ.Nonempty
  le : ∀ A ∈ Δ, A ≤ X
  gen : X = ⨆ A ∈ Δ, A
  conj : ∀ A ∈ Δ, ∀ B ∈ Δ, ∃ x ∈ X, B = conjSubgroup x A
  conj_mem : ∀ A ∈ Δ, ∀ x ∈ X, conjSubgroup x A ∈ Δ
  card : ∀ A ∈ Δ, Nat.card A = 2 ^ f
  pair : ∀ A ∈ Δ, ∀ B ∈ Δ, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B
  partner : ∀ A ∈ Δ, ∃ B ∈ Δ, IsL2Gen A B
  pCore_eq_bot : pCore 2 ↥X = ⊥
  oddCore_le : pPrimeCore 2 ↥X ≤ Subgroup.center ↥X

abbrev quotY (X : Subgroup K) : Type := ↥X ⧸ Subgroup.center ↥X

abbrev quotMap (X : Subgroup K) : ↥X →* quotY X := QuotientGroup.mk' _

abbrev quotSub (X A : Subgroup K) : Subgroup (quotY X) := (A.subgroupOf X).map (quotMap X)

abbrev quotDelta (X : Subgroup K) (Δ : Set (Subgroup K)) : Set (Subgroup (quotY X)) :=
  quotSub X '' Δ

theorem RootSetup.le_normalizer {X : Subgroup K} {Δ : Set (Subgroup K)} {f : ℕ}
    (h : RootSetup X Δ f) (L : Subgroup K) : L ≤ Subgroup.normalizer (X : Set K) := by
  rw [Subgroup.normalizer_eq_top_iff.mpr h.normal]
  exact le_top
