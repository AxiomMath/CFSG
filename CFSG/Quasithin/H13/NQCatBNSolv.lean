module

public import CFSG.LieType.Steinberg.Bruhat

public section

namespace CFSG.Quasithin.H13.NQCat.BN

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg
open scoped Pointwise

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem exists_eq_mul_of_mem_borel
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H) {b : K} (hb : b ∈ borel D H) :
    ∃ u ∈ posUnipotent D, ∃ t ∈ ⨆ i, H i, b = u * t := by
  have hb' : b⁻¹ ∈ ((⨆ i, H i : Subgroup K) : Set K) * (posUnipotent D : Set K) := by
    rw [← coe_borel hct]
    exact inv_mem hb
  obtain ⟨t, ht, u, hu, he⟩ := hb'
  have he' : t * u = b⁻¹ := he
  refine ⟨u⁻¹, inv_mem hu, t⁻¹, inv_mem ht, ?_⟩
  rw [← mul_inv_rev, he', inv_inv]

theorem le_borel_of_isSolvable
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hL : ∀ i, ¬ Group.IsSolvable (rankOne D.rootGroup i))
    {A : Subgroup K} (hUA : posUnipotent D ≤ A) (hA : Group.IsSolvable A) : A ≤ borel D H := by
  intro g hg
  obtain ⟨w, hw⟩ := Set.mem_iUnion.1 ((iUnion_bruhatCell hct hext).symm ▸ Set.mem_univ g)
  by_cases hw1 : w = 1
  · subst hw1
    rw [bruhatCell_one] at hw
    exact hw
  exfalso
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := hw
  obtain ⟨u₁, hu₁, t₁, ht₁, rfl⟩ := exists_eq_mul_of_mem_borel hct hb₁
  have hb₂' : b₂ ∈ ((⨆ i, H i : Subgroup K) : Set K) * (posUnipotent D : Set K) := by
    rw [← coe_borel hct]
    exact hb₂
  obtain ⟨t₂, ht₂, u₂, hu₂, rfl⟩ := hb₂'
  set m := t₁ * nrep hct w * t₂ with hm
  have hmA : m ∈ A := by
    have h1 : m = u₁⁻¹ * (u₁ * t₁ * nrep hct w * (t₂ * u₂)) * u₂⁻¹ := by
      rw [hm]
      group
    rw [h1]
    exact mul_mem (mul_mem (inv_mem (hUA hu₁)) hg) (inv_mem (hUA hu₂))
  have hact : ActsAs D m w := by
    have h := ((actsAs_of_mem_iSup hct ht₁).mul (actsAs_nrep hct w)).mul
      (actsAs_of_mem_iSup hct ht₂)
    rwa [one_mul, mul_one] at h
  obtain ⟨i, hi⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_leftDescent_of_ne_one hw1
  have hαi : (Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots :=
    (RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i
  have hneg : -(Pi.single i 1 : Fin D.rank → ℤ) ∈ D.roots := OfCartan.neg_mem_roots _ hαi
  set γ := weylAction D.isFiniteType w⁻¹ (-Pi.single i 1) with hγdef
  have hγ : γ ∈ D.roots := weylAction_mem_roots _ w⁻¹ hneg
  have hγpos : 0 < ht γ := by
    have h1 := ht_weylAction_single_neg (D := D) (w := w⁻¹) (i := i)
      (by rwa [CoxeterSystem.isRightDescent_inv_iff])
    rw [hγdef, map_neg]
    simp only [ht, Pi.neg_apply, Finset.sum_neg_distrib] at h1 ⊢
    omega
  have hXneg : D.rootGroup (-Pi.single i 1) ≤ A := by
    have h1 := hact γ hγ
    rw [hγdef, weylAction_apply_inv_apply] at h1
    rw [← h1]
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hmA (hUA (rootGroup_le_posUnipotent hγ hγpos hx))) (inv_mem hmA)
  have hLA : rankOne D.rootGroup i ≤ A :=
    sup_le (fun x hx => hUA (rootGroup_le_posUnipotent hαi (ht_single_pos i) hx)) hXneg
  exact hL i (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLA)
    (Subgroup.inclusion_injective hLA))

end CFSG.Quasithin.H13.NQCat.BN
