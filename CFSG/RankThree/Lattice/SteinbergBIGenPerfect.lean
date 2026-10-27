module

public import CFSG.LieType.Chevalley.OrthogonalSemilinearFixedRootPerfectness
public import CFSG.RankThree.Lattice.SteinbergBIGenOrbitMaps

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.LieType.Chevalley
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg.Adjoint
open scoped commutatorElement

namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem orbitMapHom_HSL {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) (t : (D.orbitField O)ˣ) :
    D.orbitMapHom hO (HSL t) = D.orbitH O t :=
  rfl

theorem orbitX_mem_commutator_of_sq_ne_one {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {t : (D.orbitField O)ˣ} (ht : (t : D.orbitField O) ^ 2 ≠ 1) (c : D.orbitField O) :
    D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  have hne : (t : D.orbitField O) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 ht
  have h := map_commutatorElement (D.orbitMapHom hO) (HSL t) (uSL (c / ((t : _) ^ 2 - 1)))
  rw [commutatorElement_HSL_uSL, mul_div_cancel₀ _ hne] at h
  rw [orbitX, ← D.orbitMapHom_apply hO, h]
  exact Subgroup.commutator_mem_commutator (D.orbitMap_mem_orbitGroup hO _)
    (D.orbitMap_mem_orbitGroup hO _)

theorem orbitY_mem_commutator_of_sq_ne_one {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    {t : (D.orbitField O)ˣ} (ht : (t : D.orbitField O) ^ 2 ≠ 1) (c : D.orbitField O) :
    D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  have ht' : (((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 ≠ 1 := by
    intro h
    apply ht
    have h1 : ((t : D.orbitField O) * ((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 = 1 := by
      rw [Units.mul_inv, one_pow]
    rw [mul_pow, h, mul_one] at h1
    exact h1
  have hne : (((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 - 1 ≠ 0 := sub_ne_zero.2 ht'
  have h := map_commutatorElement (D.orbitMapHom hO) (HSL t)
    (vSL (c / ((((t⁻¹ : (D.orbitField O)ˣ) : D.orbitField O)) ^ 2 - 1)))
  rw [commutatorElement_HSL_vSL, mul_div_cancel₀ _ hne] at h
  rw [orbitY, ← D.orbitMapHom_apply hO, h]
  exact Subgroup.commutator_mem_commutator (D.orbitMap_mem_orbitGroup hO _)
    (D.orbitMap_mem_orbitGroup hO _)

theorem exists_sq_ne_one {O : Set (Fin τ.rank → ℤ)} (h3 : 3 < Nat.card (D.orbitField O)) :
    ∃ t : (D.orbitField O)ˣ, (t : D.orbitField O) ^ 2 ≠ 1 := by
  by_contra h
  push Not at h
  have hsub : (Set.univ : Set (D.orbitField O)) ⊆ {0, 1, -1} := by
    intro x _
    by_cases hx : x = 0
    · exact Or.inl hx
    · have h1 := h (Units.mk0 x hx)
      rw [Units.val_mk0] at h1
      have h2 : (x - 1) * (x + 1) = 0 := by linear_combination h1
      rcases mul_eq_zero.1 h2 with h3 | h3
      · exact Or.inr (Or.inl (sub_eq_zero.1 h3))
      · exact Or.inr (Or.inr (eq_neg_of_add_eq_zero_left h3))
  have hfin : ({0, 1, -1} : Set (D.orbitField O)).Finite := Set.toFinite _
  have hle := Set.ncard_le_ncard hsub hfin
  rw [Set.ncard_univ] at hle
  have h4 : ({0, 1, -1} : Set (D.orbitField O)).ncard ≤ 3 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    refine Nat.succ_le_succ ((Set.ncard_insert_le _ _).trans ?_)
    rw [Set.ncard_singleton]
  omega

end GenFixedRootDatum


namespace GenFixedRootDatum

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]
  {M : Type} [CommGroup M]
  (D : GenFixedRootDatum τ p₀ k M)

theorem isPerfect_orbitGroup_of_forall
    (h : ∀ O ∈ D.orbits, ∀ c, D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ ∧
      D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆) : Group.IsPerfect D.orbitGroup := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm (Subgroup.commutator_le_self _) ((Subgroup.closure_le _).2 ?_)
  rintro _ ⟨O, hO, c, rfl | rfl⟩
  exacts [(h O hO c).1, (h O hO c).2]

theorem gens_mem_commutator_of_three_lt {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (h3 : 3 < Nat.card (D.orbitField O)) (c : D.orbitField O) :
    D.orbitX O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ ∧ D.orbitY O c ∈ ⁅D.orbitGroup, D.orbitGroup⁆ := by
  obtain ⟨t, ht⟩ := D.exists_sq_ne_one h3
  exact ⟨D.orbitX_mem_commutator_of_sq_ne_one hO ht c, D.orbitY_mem_commutator_of_sq_ne_one hO ht c⟩

theorem range_orbitMap_eq_of_orbits_eq {O : Set (Fin τ.rank → ℤ)} (hA : D.orbits = {O}) :
    Set.range (D.orbitMap O) = D.orbitGroup := by
  have hO : O ∈ D.orbits := by rw [hA]; exact Set.mem_singleton O
  refine Set.Subset.antisymm (D.range_orbitMap_subset hO) ?_
  rw [D.range_orbitMap hO]
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨O', hO', c, rfl | rfl⟩
  · rw [hA, Set.mem_singleton_iff] at hO'
    subst hO'
    exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  · rw [hA, Set.mem_singleton_iff] at hO'
    subst hO'
    exact Subgroup.subset_closure (Or.inr ⟨c, rfl⟩)

@[expose] def orbitGroupHom {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits) :
    SL2 (D.orbitField O) →* D.orbitGroup :=
  (D.orbitMapHom hO).codRestrict D.orbitGroup fun A => D.orbitMap_mem_orbitGroup hO A

theorem orbitGroupHom_surjective {O : Set (Fin τ.rank → ℤ)} (hO : O ∈ D.orbits)
    (hA : D.orbits = {O}) : Function.Surjective (D.orbitGroupHom hO) := by
  rintro ⟨g, hg⟩
  have hg' : g ∈ Set.range (D.orbitMap O) := by
    rw [D.range_orbitMap_eq_of_orbits_eq hA]
    exact hg
  obtain ⟨A, rfl⟩ := hg'
  exact ⟨A, rfl⟩

theorem isPerfect_orbitGroup_of_card (h3 : ∀ O ∈ D.orbits, 3 < Nat.card (D.orbitField O)) :
    Group.IsPerfect D.orbitGroup :=
  D.isPerfect_orbitGroup_of_forall fun O hO c => D.gens_mem_commutator_of_three_lt hO (h3 O hO) c

end GenFixedRootDatum

end CFSG.RankThree.Lattice
