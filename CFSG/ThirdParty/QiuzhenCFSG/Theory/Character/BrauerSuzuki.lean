module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.GroupTheory.Index
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.ClassFunction
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Induction

namespace CFSG
end CFSG
open CFSG

/-!
# Brauer--Suzuki machinery (Gorenstein 4.4.6)

Reindexing and support lemmas, and the Brauer--Suzuki expansion of the scalar
product of two induced class functions as a double sum over the base group and
the subgroup.
-/

noncomputable section

open scoped BigOperators

namespace CFSG.Theory.Character

universe u

-- This file's sums over subgroups need `Fintype ↥H`.  `Fintype.ofFinite` as a
-- local instance covers statement contexts, but inside `classical` proofs
-- mathlib's `instFintypeSubtypeMemOfDecidablePred` wins (it needs a
-- `DecidablePred`); making `Classical.propDecidable` a local instance too
-- keeps statement and proof contexts synthesizing the *same* instance, so
-- calc chains across the two elaborate consistently.  All local: deliberately
-- not exported, so importing this module does not change instance resolution
-- elsewhere.
attribute [local instance] Fintype.ofFinite
attribute [local instance] Classical.propDecidable

/-- `star (if p then a else b) = if p then star a else star b`. -/
private lemma star_ite {p : Prop} [Decidable p] (a b : ℂ) :
    star (if p then a else b) = (if p then star a else star b) := by
  by_cases h : p <;> simp [h]

/-- Reindexing: `∑_{x,y} f (x⁻¹·y) = |L| · ∑_z f z`. -/
public lemma conj_reindex {L : Type u} [Group L] [Fintype L] (f : L → ℂ) :
    (∑ x : L, ∑ y : L, f (x⁻¹ * y)) = (Nat.card L : ℂ) * ∑ z : L, f z := by
  classical
  calc
    (∑ x : L, ∑ y : L, f (x⁻¹ * y)) = ∑ x : L, ∑ z : L, f z := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      refine (Finset.sum_bij (fun z hz => x * z) ?_ ?_ ?_ ?_).symm
      · intro z hz
        simp
      · intro z₁ h₁ z₂ h₂ hEq
        exact mul_left_cancel hEq
      · intro y hy
        refine ⟨x⁻¹ * y, by simp, ?_⟩
        group
      · intro z hz
        congr 1
        group
    _ = (∑ x : L, 1) * ∑ z : L, f z := by
      rw [Finset.sum_mul]
      simp
    _ = (Nat.card L : ℂ) * ∑ z : L, f z := by
      simp [Finset.sum_const, Nat.card_eq_fintype_card]

/-- A function vanishing off `H` sums over `G` the same as over `H`. -/
public lemma sum_eq_sum_subgroup_of_vanishes {G : Type u} [Group G] [Fintype G]
    (H : Subgroup G) (f : G → ℂ) (hf : ∀ x : G, x ∉ H → f x = 0) :
    (∑ x : G, f x) = ∑ x : ↥H, f (x : G) := by
  classical
  calc
    (∑ x : G, f x) = Finset.sum (Finset.univ.filter (fun x : G => x ∈ H)) f := by
      refine (Finset.sum_subset (by intro x hx; exact Finset.mem_univ x) ?_).symm
      intro x hx hxnot
      have hxH : x ∉ H := by
        intro hxH
        exact hxnot (Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxH⟩)
      exact hf x hxH
    _ = ∑ x : ↥H, f (x : G) := by
      refine Finset.sum_bij (fun x hx => (⟨(x : G), (Finset.mem_filter.mp hx).2⟩ : ↥H)) ?_ ?_ ?_ ?_
      · intro x hx
        simp
      · intro x₁ h₁ x₂ h₂ hEq
        exact congrArg Subtype.val hEq
      · intro x hx
        refine ⟨(x : G), Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.2⟩, ?_⟩
        exact Subtype.ext rfl
      · intro x hx
        rfl

/-- The summand of the pairing of two induced class functions:
`δ₁ h · conj(δ₂(z⁻¹·h·z))` when `z⁻¹·h·z ∈ H`, else `0`. -/
@[expose] public noncomputable def pairingSummand {G : Type u} [Group G] (H : Subgroup G)
    (δ₁ δ₂ : ClassFunction (↥H)) (z : G) (h : ↥H) : ℂ := by
  classical
  exact if hz : z⁻¹ * (h : G) * z ∈ H then δ₁ h * star (δ₂ ⟨z⁻¹ * (h : G) * z, hz⟩) else 0

/-- The Brauer--Suzuki expansion: the scalar product of two induced class
functions is a double sum over the base group and the subgroup. -/
public lemma pairing_induced_expand {L : Type u} [Group L] [Fintype L] (K : Subgroup L)
    (δ₁ δ₂ : ClassFunction (↥K)) :
    scalarProduct L (inducedClassFunction K δ₁) (inducedClassFunction K δ₂) =
      ((Nat.card (↥K) : ℂ)⁻¹ * (Nat.card (↥K) : ℂ)⁻¹) *
        ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
  classical
  let c : ℂ := (Nat.card (↥K) : ℂ)⁻¹
  have hcstar : star c = c := by
    unfold c
    exact (map_inv₀ (starRingEnd ℂ) (Nat.card (↥K) : ℂ)).trans (by simp)
  let A : L → L → ℂ :=
    fun g x => if hx : x⁻¹ * g * x ∈ K then δ₁ ⟨x⁻¹ * g * x, hx⟩ else 0
  let B : L → L → ℂ :=
    fun g y => if hy : y⁻¹ * g * y ∈ K then δ₂ ⟨y⁻¹ * g * y, hy⟩ else 0
  have hsubst : ∀ x y : L,
      (∑ g : L, A g x * star (B g y)) =
        ∑ h : ↥K, pairingSummand K δ₁ δ₂ (x⁻¹ * y) h := by
    intro x y
    let z : L := x⁻¹ * y
    calc
      (∑ g : L, A g x * star (B g y))
          = ∑ h : L, A (x * h * x⁻¹) x * star (B (x * h * x⁻¹) y) := by
              refine (Finset.sum_bij (fun h hh => x * h * x⁻¹) ?_ ?_ ?_ ?_).symm
              · intro h hh
                simp
              · intro h₁ hh₁ h₂ hh₂ hEq
                exact mul_left_cancel (mul_right_cancel hEq)
              · intro g hg
                refine ⟨x⁻¹ * g * x, by simp, ?_⟩
                group
              · intro h hh
                rfl
      _ = ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
              have hsummand : ∀ h : L,
                  A (x * h * x⁻¹) x * star (B (x * h * x⁻¹) y) =
                    (if hK : h ∈ K then
                      (if hz0 : z⁻¹ * h * z ∈ K then
                        δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0)
                     else 0) := by
                intro h
                have hA : A (x * h * x⁻¹) x = (if hK : h ∈ K then δ₁ ⟨h, hK⟩ else 0) := by
                  have hEq : x⁻¹ * (x * h * x⁻¹) * x = h := by group
                  change (if hx : x⁻¹ * (x * h * x⁻¹) * x ∈ K then δ₁ ⟨x⁻¹ * (x * h * x⁻¹) * x, hx⟩ else 0) =
                    (if hK : h ∈ K then δ₁ ⟨h, hK⟩ else 0)
                  rw [hEq]
                have hB : star (B (x * h * x⁻¹) y) =
                    (if hz0 : z⁻¹ * h * z ∈ K then star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0) := by
                  have hEq : y⁻¹ * (x * h * x⁻¹) * y = z⁻¹ * h * z := by
                    change y⁻¹ * (x * h * x⁻¹) * y = (x⁻¹ * y)⁻¹ * h * (x⁻¹ * y)
                    group
                  change star (if hy : y⁻¹ * (x * h * x⁻¹) * y ∈ K then δ₂ ⟨y⁻¹ * (x * h * x⁻¹) * y, hy⟩ else 0) =
                    (if hz0 : z⁻¹ * h * z ∈ K then star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0)
                  rw [hEq]
                  by_cases hz0 : z⁻¹ * h * z ∈ K <;> simp [hz0]
                rw [hA, hB]
                by_cases hK : h ∈ K
                · by_cases hz0 : z⁻¹ * h * z ∈ K <;> simp [hK, hz0]
                · simp [hK]
              calc
                (∑ h : L, A (x * h * x⁻¹) x * star (B (x * h * x⁻¹) y))
                    = ∑ h : L, (if hK : h ∈ K then
                        (if hz0 : z⁻¹ * h * z ∈ K then
                          δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0)
                       else 0) := by
                          refine Finset.sum_congr rfl ?_
                          intro h hh
                          exact hsummand h
                _ = ∑ h : ↥K, (if hz0 : z⁻¹ * (h : L) * z ∈ K then
                      δ₁ h * star (δ₂ ⟨z⁻¹ * (h : L) * z, hz0⟩) else 0) := by
                          calc
                            (∑ h : L, (if hK : h ∈ K then
                                (if hz0 : z⁻¹ * h * z ∈ K then
                                  δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0)
                               else 0))
                                = Finset.sum (Finset.univ.filter (fun h : L => h ∈ K))
                                    (fun h => (if hK : h ∈ K then
                                      (if hz0 : z⁻¹ * h * z ∈ K then
                                        δ₁ ⟨h, hK⟩ * star (δ₂ ⟨z⁻¹ * h * z, hz0⟩) else 0)
                                     else 0)) := by
                                      refine (Finset.sum_subset (by intro h hh; exact Finset.mem_univ h) ?_).symm
                                      intro h hh hnot
                                      have hhK : h ∉ K := by
                                        intro hK
                                        exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ h, hK⟩)
                                      simp [hhK]
                            _ = ∑ h : ↥K, (if hz0 : z⁻¹ * (h : L) * z ∈ K then
                                  δ₁ h * star (δ₂ ⟨z⁻¹ * (h : L) * z, hz0⟩) else 0) := by
                                  refine Finset.sum_bij (fun h hh =>
                                    (⟨(h : L), (Finset.mem_filter.mp hh).2⟩ : ↥K)) ?_ ?_ ?_ ?_
                                  · intro h hh
                                    simp
                                  · intro h₁ hh₁ h₂ hh₂ hEq
                                    exact congrArg Subtype.val hEq
                                  · intro h hh
                                    refine ⟨(h : L), Finset.mem_filter.mpr ⟨Finset.mem_univ _, h.2⟩, ?_⟩
                                    exact Subtype.ext rfl
                                  · intro a ha
                                    by_cases hK : a ∈ K
                                    · by_cases hz0 : z⁻¹ * a * z ∈ K
                                      · simp [hK, hz0]
                                      · simp [hK, hz0]
                                    · exfalso
                                      exact hK (Finset.mem_filter.mp ha).2
                _ = ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
                          refine Finset.sum_congr rfl ?_
                          intro h hh
                          by_cases hz0 : z⁻¹ * (h : L) * z ∈ K
                          · rw [pairingSummand]
                          · rw [pairingSummand]
  calc
    scalarProduct L (inducedClassFunction K δ₁) (inducedClassFunction K δ₂)
        = (Nat.card L : ℂ)⁻¹ *
            ∑ g : L, (c * ∑ x : L, A g x) * star (c * ∑ y : L, B g y) := by
            rw [scalarProduct]
            congr 1
    _ = (Nat.card L : ℂ)⁻¹ * (c * c) *
          ∑ g : L, ∑ x : L, ∑ y : L, A g x * star (B g y) := by
            calc
              (Nat.card L : ℂ)⁻¹ * (∑ g : L, (c * ∑ x : L, A g x) * star (c * ∑ y : L, B g y))
                  = (Nat.card L : ℂ)⁻¹ *
                      ((c * c) * ∑ g : L, (∑ x : L, A g x) * (∑ y : L, star (B g y))) := by
                      congr 1
                      calc
                        ∑ g : L, (c * ∑ x : L, A g x) * star (c * ∑ y : L, B g y)
                            = ∑ g : L, (c * ∑ x : L, A g x) * (c * (∑ y : L, star (B g y))) := by
                                refine Finset.sum_congr rfl ?_
                                intro g hg
                                simp [hcstar]
                        _ = ∑ g : L, c * c * ((∑ x : L, A g x) * (∑ y : L, star (B g y))) := by
                                refine Finset.sum_congr rfl ?_
                                intro g hg
                                ring
                        _ = (c * c) * ∑ g : L, (∑ x : L, A g x) * (∑ y : L, star (B g y)) := by
                                rw [← Finset.mul_sum]
              _ = (Nat.card L : ℂ)⁻¹ * (c * c) * ∑ g : L, (∑ x : L, A g x) * (∑ y : L, star (B g y)) := by
                      rw [← mul_assoc]
              _ = (Nat.card L : ℂ)⁻¹ * (c * c) * ∑ g : L, ∑ x : L, ∑ y : L,
                    A g x * star (B g y) := by
                      congr 1
                      refine Finset.sum_congr rfl ?_
                      intro g hg
                      rw [Fintype.sum_mul_sum]
    _ = (Nat.card L : ℂ)⁻¹ * (c * c) * ∑ x : L, ∑ y : L, ∑ g : L, A g x * star (B g y) := by
            congr 1
            rw [Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
              (f := fun g x : L => ∑ y : L, A g x * star (B g y))]
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
              (f := fun g y : L => A g x * star (B g y))
    _ = (Nat.card L : ℂ)⁻¹ * (c * c) *
          ∑ x : L, ∑ y : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ (x⁻¹ * y) h := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro x hx
            refine Finset.sum_congr rfl ?_
            intro y hy
            exact hsubst x y
    _ = (Nat.card L : ℂ)⁻¹ * (c * c) *
          ((Nat.card L : ℂ) * ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h) := by
            congr 1
            rw [conj_reindex (fun z : L => ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h)]
    _ = (c * c) * ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
            let S : ℂ := ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h
            calc
              (Nat.card L : ℂ)⁻¹ * (c * c) * ((Nat.card L : ℂ) * S)
                  = (Nat.card L : ℂ)⁻¹ * (Nat.card L : ℂ) * ((c * c) * S) := by
                      ring
              _ = (c * c) * S := by
                      rw [inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (ne_of_gt (Nat.card_pos (α := L)))),
                        one_mul]
    _ = ((Nat.card (↥K) : ℂ)⁻¹ * (Nat.card (↥K) : ℂ)⁻¹) *
          ∑ z : L, ∑ h : ↥K, pairingSummand K δ₁ δ₂ z h := by
            rfl

end CFSG.Theory.Character
