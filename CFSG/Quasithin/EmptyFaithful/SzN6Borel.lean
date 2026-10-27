module

public import CFSG.Quasithin.EmptyFaithful.SzN2Lin

public section

namespace CFSG.Quasithin.SzN6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin

variable {K : Type} [Field K]

theorem sl2_le_upperTriangular_of_ne_top {A : Subgroup (SpecialLinearGroup (Fin 2) K)}
    (hVA : unitriangular 2 K ≤ A) (hA : A ≠ ⊤) : A ≤ upperTriangular 2 K := by
  obtain ⟨hle, hiff⟩ :=
    (linear_unitriangular_overgroup_subflag_containment (n := 2) (K := K)).1 A hVA
  refine SzN2.le_upperTriangular_of_cuts hle fun i hi1 hin => ?_
  have hi : i = 1 := by omega
  subst hi
  by_contra h1
  have hempty : borelOvergroupCuts A = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun j hj => ?_
    obtain ⟨hj1, hjn, -⟩ := id hj
    have hj' : j = 1 := by omega
    subst hj'
    exact h1 hj
  exact hA (hiff.mp hempty)


section General

variable {M : Type} [Group M] [Finite M]

theorem proper_overgroup_le_normalizer_of_sylow {U₀ : Subgroup M} (hU₀ : IsSylowTwoOf U₀ ⊤)
    (h₀ : ∀ Y : Subgroup M, U₀ ≤ Y → Y ≠ ⊤ → Y ≤ Subgroup.normalizer (U₀ : Set M))
    {U Y : Subgroup M} (hU : IsSylowTwoOf U ⊤) (hUY : U ≤ Y) (hY : Y ≠ ⊤) :
    Y ≤ Subgroup.normalizer (U : Set M) := by
  obtain ⟨φ, hφ⟩ := SzN2.exists_mulEquiv_map_eq hU₀ hU
  have h1 : U₀ ≤ Y.map φ.toMonoidHom := hφ ▸ Subgroup.map_mono hUY
  have h2 : Y.map φ.toMonoidHom ≠ ⊤ := by
    intro h
    apply hY
    have := congrArg (Subgroup.comap φ.toMonoidHom) h
    rwa [Subgroup.comap_map_eq_self_of_injective φ.injective, Subgroup.comap_top] at this
  have h3 := h₀ _ h1 h2
  rw [← hφ, ← Subgroup.map_equiv_normalizer_eq] at h3
  exact (Subgroup.map_le_map_iff_of_injective φ.injective).mp h3

end General

theorem sl2_proper_overgroup_le_normalizer [Finite K] [CharP K 2] :
    ∀ Ū Y : Subgroup (SpecialLinearGroup (Fin 2) K), IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Y ≠ ⊤ →
      Y ≤ Subgroup.normalizer (Ū : Set (SpecialLinearGroup (Fin 2) K)) :=
  fun _ _ hŪ hUY hY =>
    proper_overgroup_le_normalizer_of_sylow
      (SzN2.isSylowTwoOf_unitriangular (K := K) (by norm_num : 1 ≤ 2))
      (fun _ hY' hne => by
        rw [normalizer_unitriangular]
        exact sl2_le_upperTriangular_of_ne_top hY' hne) hŪ hUY hY

section Transport

variable {Γ M : Type} [Group Γ] [Group M]

theorem normalizes_of_proper_overgroup [Finite Γ] (ρ : Γ →* M) (hρ : Function.Surjective ρ)
    (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū Y : Subgroup M, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Y ≠ ⊤ →
      Y ≤ Subgroup.normalizer (Ū : Set M))
    {S X : Subgroup Γ} (hS : IsSylowTwoOf S ⊤) (hSX : S ≤ X) (hX : X ≠ ⊤) :
    X ≤ Subgroup.normalizer (S : Set Γ) := by
  have hkS := SzN2.ker_le_of_isSylowTwoOf hk hS
  have hŪ := isSylowTwoOf_top_map_of_surjective hS ρ hρ
  have hXρ : X.map ρ ≠ ⊤ := by
    intro h
    apply hX
    have hkX : ρ.ker ≤ X := hkS.trans hSX
    rw [← Subgroup.comap_map_eq_self hkX, h, Subgroup.comap_top]
  have h1 := hM (S.map ρ) (X.map ρ) hŪ (Subgroup.map_mono hSX) hXρ
  intro x hx
  exact SzN2.mem_normalizer_of_ker_le ρ hkS (h1 ⟨x, hx, rfl⟩)

end Transport

section Subgroup

variable {G : Type} [Group G] {L : Subgroup G} {M : Type} [Group M]

theorem L_normalizes_of_proper_overgroup [Finite G] {S₀ X : Subgroup G} (ρ : ↥L →* M)
    (hρ : Function.Surjective ρ) (hk : IsPGroup 2 ρ.ker)
    (hM : ∀ Ū Y : Subgroup M, IsSylowTwoOf Ū ⊤ → Ū ≤ Y → Y ≠ ⊤ →
      Y ≤ Subgroup.normalizer (Ū : Set M))
    (hS : IsSylowTwoOf S₀ L) (hSX : S₀ ≤ X) (hXL : X ≤ L) (hX : X ≠ L) :
    X ≤ Subgroup.normalizer (S₀ : Set G) := by
  have hX' : X.subgroupOf L ≠ ⊤ := fun h =>
    hX (le_antisymm hXL (Subgroup.subgroupOf_eq_top.mp h))
  have h := normalizes_of_proper_overgroup ρ hρ hk hM (isSylowTwoOf_top_subgroupOf hS)
    (fun x hx => hSX hx : S₀.subgroupOf L ≤ X.subgroupOf L) hX'
  intro x hx
  have hxL : x ∈ L := hXL hx
  have h1 := (A312.mem_normalizer_map_subtype_iff L (S₀.subgroupOf L) ⟨x, hxL⟩).mp
    (h (show (⟨x, hxL⟩ : ↥L) ∈ X.subgroupOf L from hx))
  rwa [Subgroup.map_subgroupOf_eq_of_le hS.1] at h1

end Subgroup

end CFSG.Quasithin.SzN6
