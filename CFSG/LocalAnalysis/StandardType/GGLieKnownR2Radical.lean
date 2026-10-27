module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Levels
public import CFSG.LieType.TitsSimplicity.Unipotent
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.LieType.HighestRoot CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.LieType.TitsSimplicity
open scoped commutatorElement

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem eq_or_linIndepPair_of_rootForm_pos (hD : D.divisible = ∅) {r γ δ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots) (hγr : 0 < rootForm D γ r)
    (hδr : 0 < rootForm D δ r) : γ = δ ∨ LinIndepPair γ δ := by
  by_cases hli : LinIndepPair γ δ
  · exact Or.inr hli
  refine Or.inl ?_
  rcases OfCartan.proportional D.isFiniteType hγ hδ hli with h | h | h | h | h | h
  · exact h
  · exfalso
    have e : rootForm D γ r = -rootForm D δ r := by
      rw [h]
      simp only [rootForm, map_neg, LinearMap.neg_apply]
    linarith
  · exact absurd (h ▸ hγ) (two_smul_notMem_roots hD hδ)
  · exfalso
    have h2 : 2 • δ ∈ D.roots := by
      have := OfCartan.neg_mem_roots D.isFiniteType hγ
      rwa [h, neg_neg] at this
    exact two_smul_notMem_roots hD hδ h2
  · exact absurd (h ▸ hδ) (two_smul_notMem_roots hD hγ)
  · exfalso
    have h2 : 2 • γ ∈ D.roots := by
      have := OfCartan.neg_mem_roots D.isFiniteType hδ
      rwa [h, neg_neg] at this
    exact two_smul_notMem_roots hD hγ h2

theorem commutator_mem_rootGroup_of_rootForm_pos (hext : SteinbergExtras D n H)
    (hE : RootGroupCommutators D) (hD : D.divisible = ∅) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) {γ δ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (hδ : δ ∈ D.roots)
    (hγr : 0 < rootForm D γ r) (hδr : 0 < rootForm D δ r) {x y : K} (hx : x ∈ D.rootGroup γ)
    (hy : y ∈ D.rootGroup δ) : ⁅x, y⁆ ∈ D.rootGroup r := by
  rcases eq_or_linIndepPair_of_rootForm_pos hD hγ hδ hγr hδr with rfl | hli
  · have h' := Subgroup.commutator_mem_commutator hx hy
    rw [hE.commutator_eq_bot γ hγ (two_smul_notMem_roots hD hγ), Subgroup.mem_bot] at h'
    rw [h']
    exact one_mem _
  · refine (iSup₂_le fun ε hε => ?_ : ⨆ ε ∈ openCone D.roots γ δ, D.rootGroup ε ≤ _)
      (hext.commutator_mem γ hγ δ hδ hli x hx y hy)
    obtain rfl : ε = r := Set.mem_singleton_iff.1 (openCone_subset_of_pos D hD hr hγ hδ hγr hδr hε)
    exact le_rfl

theorem commute_of_rootForm_pos (hext : SteinbergExtras D n H) (hE : RootGroupCommutators D)
    (hD : D.divisible = ∅) {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hγr : 0 < rootForm D γ r) {x y : K} (hx : x ∈ D.rootGroup γ)
    (hy : y ∈ D.rootGroup r) : Commute x y := by
  have hr0 : toRat r ≠ 0 := fun e =>
    ne_zero_of_mem_roots D.isFiniteType D.divisible hr.mem_roots
      (toRat_injective (by rw [e, map_zero]))
  have hrr : 0 < rootForm D r r := form_pos D.isFiniteType hr0
  rcases eq_or_linIndepPair_of_rootForm_pos hD hγ hr.mem_roots hγr hrr with rfl | hli
  · have h' := Subgroup.commutator_mem_commutator hx hy
    rw [hE.commutator_eq_bot γ hγ (two_smul_notMem_roots hD hγ), Subgroup.mem_bot] at h'
    exact commutatorElement_eq_one_iff_commute.1 h'
  · have hc := hext.commutator_mem γ hγ r hr.mem_roots hli x hx y hy
    rw [openCone_eq_empty_of_pos D hD hr hγ hγr] at hc
    simp only [Set.mem_empty_iff_false, iSup_false, iSup_bot, Subgroup.mem_bot] at hc
    exact commutatorElement_eq_one_iff_commute.1 hc

theorem highestRootRadical_le_centralizer_rootGroup (hext : SteinbergExtras D n H)
    (hE : RootGroupCommutators D) (hD : D.divisible = ∅) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) :
    highestRootRadical D r ≤ Subgroup.centralizer (D.rootGroup r : Set K) := by
  refine iSup₂_le fun γ hγ x hx => ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (commute_of_rootForm_pos hext hE hD hr hγ.1 hγ.2 hx hy).eq.symm

theorem commutator_highestRootRadical_le_rootGroup (hext : SteinbergExtras D n H)
    (hE : RootGroupCommutators D) (hD : D.divisible = ∅) {r : Fin D.rank → ℤ}
    (hr : IsHighestRoot D r) :
    ⁅highestRootRadical D r, highestRootRadical D r⁆ ≤ D.rootGroup r := by
  have hN : highestRootRadical D r ≤ Subgroup.normalizer (D.rootGroup r : Set K) :=
    (highestRootRadical_le_centralizer_rootGroup hext hE hD hr).trans
      (Subgroup.centralizer_le_normalizer _)
  have hQ : ∀ {γ : Fin D.rank → ℤ}, γ ∈ D.roots → 0 < rootForm D γ r →
      D.rootGroup γ ≤ highestRootRadical D r := fun hγ h => rootGroup_le_highestRootRadical hγ h
  rw [Subgroup.commutator_le]
  have hA : ∀ γ : Fin D.rank → ℤ, γ ∈ D.roots → 0 < rootForm D γ r →
      ∀ x ∈ D.rootGroup γ, ∀ y ∈ highestRootRadical D r, ⁅x, y⁆ ∈ D.rootGroup r := by
    intro γ hγ hγr x hx y hy
    have hy' : y ∈ ⨆ δ ∈ {δ | δ ∈ D.roots ∧ 0 < rootForm D δ r}, D.rootGroup δ := hy
    have h := iSup₂_induction
      (C := fun y => y ∈ highestRootRadical D r ∧ ⁅x, y⁆ ∈ D.rootGroup r) hy'
      (fun δ hδ y hy => ⟨hQ hδ.1 hδ.2 hy,
        commutator_mem_rootGroup_of_rootForm_pos hext hE hD hr hγ hδ.1 hγr hδ.2 hx hy⟩)
      ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
      (fun y z hy hz => ⟨mul_mem hy.1 hz.1, by
        have e : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem hy.2 ((Subgroup.mem_normalizer_iff.1 (hN hy.1) _).1 hz.2)⟩)
    exact h.2
  intro x hx y hy
  have hx' : x ∈ ⨆ δ ∈ {δ | δ ∈ D.roots ∧ 0 < rootForm D δ r}, D.rootGroup δ := hx
  have h := iSup₂_induction
    (C := fun x => x ∈ highestRootRadical D r ∧ ⁅x, y⁆ ∈ D.rootGroup r) hx'
    (fun δ hδ x hx => ⟨hQ hδ.1 hδ.2 hx, hA δ hδ.1 hδ.2 x hx y hy⟩)
    ⟨one_mem _, by rw [commutatorElement_one_left]; exact one_mem _⟩
    (fun x x' hx hx' => ⟨mul_mem hx.1 hx'.1, by
      have e : ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hN hx.1) _).1 hx'.2) hx.2⟩)
  exact h.2

end CFSG.StandardType.LieKnownR2
