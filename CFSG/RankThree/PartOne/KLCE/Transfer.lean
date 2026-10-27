module

public import CFSG.RankThree.PartOne.KLC.LayerData

public section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup

section Powers

variable {G : Type} [Group G]

theorem pow_apply_mem {α : MulAut G} {Q : Subgroup G} (hQ : ∀ g ∈ Q, α g ∈ Q) (k : ℕ) :
    ∀ g ∈ Q, (α ^ k) g ∈ Q := by
  induction k with
  | zero => intro g hg; simpa using hg
  | succ k ih =>
    intro g hg
    rw [pow_succ, MulAut.mul_apply]
    exact ih _ (hQ g hg)

theorem pow_apply_of_fixed {α : MulAut G} {g : G} (hg : α g = g) (k : ℕ) : (α ^ k) g = g := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, MulAut.mul_apply, hg, ih]

theorem pow_apply_of_inner {α : MulAut G} {Q : Subgroup G} (hQ : ∀ g ∈ Q, α g ∈ Q) {e : G}
    (hall : ∀ g ∈ Q, α g = e * g * e⁻¹) (k : ℕ) :
    ∀ g ∈ Q, (α ^ k) g = e ^ k * g * (e ^ k)⁻¹ := by
  induction k with
  | zero => intro g _; simp
  | succ k ih =>
    intro g hg
    rw [pow_succ, MulAut.mul_apply, ih (α g) (hQ g hg), hall g hg]
    group

theorem lieLayerData_of_power {p : ℕ} {α₁ α : MulAut G} (hα : ∃ t : ℕ, α = α₁ ^ t)
    (hα' : ∃ t' : ℕ, α₁ = α ^ t') {X : Subgroup G} (h : KLC.LieLayerData p α₁ X) :
    KLC.LieLayerData p α X := by
  obtain ⟨t, ht⟩ := hα
  obtain ⟨t', ht'⟩ := hα'
  obtain ⟨ι, Q, hne, hcomp, hsolv, hnorm, hodd, hper⟩ := h
  refine ⟨ι, Q, hne, hcomp, hsolv, hnorm, hodd, fun i hstab => ?_⟩
  have hstab₁ : ∀ g ∈ Q i, α₁ g ∈ Q i := by
    intro g hg
    rw [ht']
    exact pow_apply_mem hstab t' g hg
  obtain ⟨hout, hmodel, hfix⟩ := hper i hstab₁
  refine ⟨?_, hmodel, ?_⟩
  · intro e he hall
    refine hout (e ^ t') (pow_mem he _) fun g hg => ?_
    rw [ht']
    exact pow_apply_of_inner hstab hall t' g hg
  · obtain ⟨t₁, ht₁, hf₁, t₂, ht₂, hf₂, o1, o2, hnc⟩ := hfix
    refine ⟨t₁, ht₁, ?_, t₂, ht₂, ?_, o1, o2, hnc⟩
    · rw [ht]
      exact pow_apply_of_fixed hf₁ t
    · rw [ht]
      exact pow_apply_of_fixed hf₂ t

end Powers

end CFSG.RankThree.PartOne.KLCE
