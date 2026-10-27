module

public import CFSG.LocalAnalysis.ComponentInitial.LinearUnitaryField
public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition

public section

namespace CFSG.RankThree.PartOne.KCUnitary

open Polynomial Module CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary

section PrimitiveCentral

@[expose] def IsPrimitiveCentralIdempotent (K : Type*) [CommSemiring K] {R : Type*} [Semiring R]
    [Algebra K R] (e : R) : Prop :=
  e ∈ Subalgebra.center K R ∧ IsIdempotentElem e ∧ e ≠ 0 ∧
    ∀ g ∈ Subalgebra.center K R, IsIdempotentElem g → g * e = g → g = 0 ∨ g = e

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {x : Module.End K V} (hsq : Squarefree (minpoly K x))
include hsq

theorem primaryProjection_mul_self {a : K[X]} (ha : a ∈ primaryFactors x) :
    primaryProjection x a * primaryProjection x a = primaryProjection x a := by
  ext v
  exact primaryProjection_of_mem hsq ha (primaryProjection_mem hsq ha v)

@[expose] noncomputable def primaryProjectionR (x : Module.End K V) (a : K[X]) : commutant x :=
  ⟨primaryProjection x a, primaryProjection_mem_commutant x a⟩

theorem primaryProjectionR_mem_center {a : K[X]} (ha : a ∈ primaryFactors x) :
    primaryProjectionR x a ∈ Subalgebra.center K (commutant x) := by
  classical
  rw [mem_center_commutant_iff hsq]
  intro b
  refine ⟨if (b : K[X]) = a then 1 else 0, fun v => ?_⟩
  split_ifs with hba
  · rw [one_smul]
    have hv : (v : V) ∈ primaryComponent x a := by rw [← hba]; exact v.2
    exact primaryProjection_of_mem hsq ha hv
  · rw [zero_smul]
    exact primaryProjection_of_mem_ne hsq ha b.2 hba v.2

theorem primaryProjectionR_ne_zero {a : K[X]} (ha : a ∈ primaryFactors x) :
    primaryProjectionR x a ≠ 0 := by
  intro h
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq ha)
  apply hv0
  have := primaryProjection_of_mem hsq ha hv
  rw [← this]
  exact congrArg (fun r : commutant x => (r : Module.End K V) v) h


theorem isPrimitiveCentralIdempotent_iff (r : commutant x) :
    IsPrimitiveCentralIdempotent K r ↔ ∃ a ∈ primaryFactors x, r = primaryProjectionR x a := by
  classical
  constructor
  · rintro ⟨hc, hidem, hne, hprim⟩
    obtain ⟨a, ha, hca⟩ : ∃ a ∈ primaryFactors x, ∃ v ∈ primaryComponent x a,
        (r : Module.End K V) v ≠ 0 := by
      by_contra! h
      apply hne
      refine Subtype.ext (ext_primaryComponent hsq fun a ha v hv => ?_)
      exact h a ha v hv
    obtain ⟨v, hv, hrv⟩ := hca
    have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
    have hcen := (mem_center_commutant_iff hsq r).mp hc
    obtain ⟨c₀, hcv⟩ := hcen ⟨a, ha⟩
    let c : AdjoinRoot a := c₀
    have hrc : ∀ u : primaryComponent x a,
        (r : Module.End K V) u = ((c • u : primaryComponent x a) : V) := hcv
    refine ⟨a, ha, ?_⟩
    let v' : primaryComponent x a := ⟨v, hv⟩
    have hv'0 : v' ≠ 0 := fun h => hrv (by
      have : v = 0 := congrArg Subtype.val h
      rw [this, map_zero])
    have hc0 : c ≠ 0 := by
      intro h0
      apply hrv
      have := hrc v'
      rw [h0, zero_smul] at this
      exact this
    have hc1 : c = 1 := by
      have h1 : (r : Module.End K V) ((r : Module.End K V) (v' : V)) =
          (r : Module.End K V) (v' : V) :=
        congrArg (fun s : commutant x => (s : Module.End K V) (v' : V)) hidem
      rw [hrc v', hrc (c • v')] at h1
      have h2 : ((c * c) • v' : primaryComponent x a) = c • v' := by
        apply Subtype.ext
        rw [mul_smul]
        exact h1
      have h3 : (c * (c - 1)) • v' = 0 := by
        rw [mul_sub, mul_one, sub_smul, h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hc0
        · exact sub_eq_zero.mp h'
      · exact absurd h hv'0
    have hgr : primaryProjectionR x a * r = primaryProjectionR x a := by
      refine Subtype.ext (ext_primaryComponent hsq fun b hb u hu => ?_)
      obtain ⟨cb, hcb⟩ := hcen ⟨b, hb⟩
      change primaryProjection x a ((r : Module.End K V) u) = primaryProjection x a u
      by_cases hba : b = a
      · have hu' : u ∈ primaryComponent x a := by rw [← hba]; exact hu
        have h1 := hrc ⟨u, hu'⟩
        rw [hc1, one_smul] at h1
        change (r : Module.End K V) u = u at h1
        rw [h1]
      · have hru : (r : Module.End K V) u = ((cb • (⟨u, hu⟩ : primaryComponent x b) :
            primaryComponent x b) : V) := hcb ⟨u, hu⟩
        rw [hru, primaryProjection_of_mem_ne hsq ha hb hba
          (cb • (⟨u, hu⟩ : primaryComponent x b) : primaryComponent x b).2,
          primaryProjection_of_mem_ne hsq ha hb hba hu]
    rcases hprim _ (primaryProjectionR_mem_center hsq ha)
      (Subtype.ext (primaryProjection_mul_self hsq ha)) hgr with h | h
    · exact absurd h (primaryProjectionR_ne_zero hsq ha)
    · exact h.symm
  · rintro ⟨a, ha, rfl⟩
    refine ⟨primaryProjectionR_mem_center hsq ha, Subtype.ext (primaryProjection_mul_self hsq ha),
      primaryProjectionR_ne_zero hsq ha, fun g hg hgi hga => ?_⟩
    have : Fact (Irreducible a) := ⟨irreducible_of_mem_primaryFactors ha⟩
    have hgcen := (mem_center_commutant_iff hsq g).mp hg
    obtain ⟨c₀, hcv⟩ := hgcen ⟨a, ha⟩
    let c : AdjoinRoot a := c₀
    have hgc : ∀ u : primaryComponent x a,
        (g : Module.End K V) u = ((c • u : primaryComponent x a) : V) := hcv
    have hgo : ∀ b ∈ primaryFactors x, b ≠ a → ∀ v ∈ primaryComponent x b,
        (g : Module.End K V) v = 0 := by
      intro b hb hba v hv
      have h1 := congrArg (fun s : commutant x => (s : Module.End K V) v) hga
      change (g : Module.End K V) (primaryProjection x a v) = (g : Module.End K V) v at h1
      rw [primaryProjection_of_mem_ne hsq ha hb hba hv, map_zero] at h1
      exact h1.symm
    obtain ⟨v₀, hv₀, hv₀0⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (primaryComponent_ne_bot hsq ha)
    let v' : primaryComponent x a := ⟨v₀, hv₀⟩
    have hv'0 : v' ≠ 0 := fun h => hv₀0 (congrArg Subtype.val h)
    have hcc : c * c = c := by
      have h1 : (g : Module.End K V) ((g : Module.End K V) (v' : V)) =
          (g : Module.End K V) (v' : V) :=
        congrArg (fun s : commutant x => (s : Module.End K V) (v' : V)) hgi
      rw [hgc v', hgc (c • v')] at h1
      have h2 : ((c * c) • v' : primaryComponent x a) = c • v' := by
        apply Subtype.ext
        rw [mul_smul]
        exact h1
      have h3 : ((c * c - c) • v' : primaryComponent x a) = 0 := by
        rw [sub_smul, h2, sub_self]
      rcases smul_eq_zero.mp h3 with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hv'0
    have hc01 : c = 0 ∨ c = 1 := by
      have : c * (c - 1) = 0 := by linear_combination hcc
      rcases mul_eq_zero.mp this with h | h
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h)
    rcases hc01 with h0 | h1
    · left
      refine Subtype.ext (ext_primaryComponent hsq fun b hb u hu => ?_)
      by_cases hba : b = a
      · have hu' : u ∈ primaryComponent x a := by rw [← hba]; exact hu
        have := hgc ⟨u, hu'⟩
        rw [h0, zero_smul] at this
        exact this
      · exact hgo b hb hba u hu
    · right
      refine Subtype.ext (ext_primaryComponent hsq fun b hb u hu => ?_)
      by_cases hba : b = a
      · have hu' : u ∈ primaryComponent x a := by rw [← hba]; exact hu
        have := hgc ⟨u, hu'⟩
        rw [h1, one_smul] at this
        change (g : Module.End K V) u = primaryProjection x a u
        rw [primaryProjection_of_mem hsq ha hu']
        exact this
      · change (g : Module.End K V) u = primaryProjection x a u
        rw [hgo b hb hba u hu, primaryProjection_of_mem_ne hsq ha hb hba hu]

end PrimitiveCentral

end CFSG.RankThree.PartOne.KCUnitary
