module

public import CFSG.LocalAnalysis.StandardType.GGF4B3CoreDefs

public section

namespace CFSG.StandardType

theorem ggF4B3_exists_pair_of_core (hCore : GGF4B3Core) {X : Type} [Group X] {A : Subgroup X}
    (cs : CoxeterSystem CoxeterMatrix.F₄ ↥A) (a : Fin 3 → ↥A)
    (ha : ∀ i, cs.IsReflection (a i)) (o01 : orderOf (a 0 * a 1) = 3)
    (o12 : orderOf (a 1 * a 2) = 4) (o02 : orderOf (a 0 * a 2) = 2) {AL : Subgroup X}
    (haAL : ∀ i, ((a i : ↥A) : X) ∈ AL)
    (hAL : AL ≤ Subgroup.closure (Set.range fun i => ((a i : ↥A) : X)))
    {ι : Type} {𝒦 : Finset ι} {AK : ι → Subgroup X}
    (hAK : ∀ K ∈ 𝒦, AK K ≤ Subgroup.closure
      {x : X | ∃ t : ↥A, cs.IsReflection t ∧ (t : X) = x ∧ x ∈ AK K})
    (hA : A ≤ AL ⊔ ⨆ K ∈ 𝒦, AK K) :
    ∃ K ∈ 𝒦, A ≤ AL ⊔ AK K := by
  classical
  obtain ⟨H, hHne, haH, hH⟩ := hCore ↥A cs a ha o01 o12 o02
  by_contra hcon0
  have hcon : ∀ K ∈ 𝒦, ¬ A ≤ AL ⊔ AK K := fun K hK h => hcon0 ⟨K, hK, h⟩
  have hHX : ∀ K ∈ 𝒦, AK K ≤ H.map A.subtype := by
    intro K hK
    refine (hAK K hK).trans ?_
    rw [Subgroup.closure_le]
    rintro x ⟨t, ht, rfl, hxK⟩
    rcases hH t ht with htH | htop
    · exact Subgroup.mem_map.2 ⟨t, htH, rfl⟩
    · exfalso
      apply hcon K hK
      intro φ hφ
      have hmem : (⟨φ, hφ⟩ : ↥A) ∈ Subgroup.closure ({a 0, a 1, a 2, t} : Set ↥A) := by
        rw [htop]; exact Subgroup.mem_top _
      have hle : Subgroup.closure ({a 0, a 1, a 2, t} : Set ↥A) ≤
          (AL ⊔ AK K).comap A.subtype := by
        rw [Subgroup.closure_le]
        intro u hu
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
        rw [SetLike.mem_coe, Subgroup.mem_comap]
        rcases hu with hu | hu | hu | hu
        · rw [hu]; exact Subgroup.mem_sup_left (haAL 0)
        · rw [hu]; exact Subgroup.mem_sup_left (haAL 1)
        · rw [hu]; exact Subgroup.mem_sup_left (haAL 2)
        · rw [hu]; exact Subgroup.mem_sup_right hxK
      exact hle hmem
  have hAle : A ≤ H.map A.subtype := by
    refine hA.trans (sup_le ?_ (iSup₂_le fun K hK => hHX K hK))
    refine hAL.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ ⟨i, rfl⟩
    exact Subgroup.mem_map.2 ⟨a i, haH i, rfl⟩
  apply hHne
  rw [eq_top_iff]
  intro u _
  obtain ⟨h, hh, hhu⟩ := Subgroup.mem_map.1 (hAle u.2)
  have hhu' : h = u := Subtype.ext hhu
  rwa [hhu'] at hh

theorem closure_range_simple_of_equiv {X : Type} [Group X] {κ : Type} {M : CoxeterMatrix κ}
    {T : Subgroup X} (f : M.Group ≃* ↥T) :
    Subgroup.closure (Set.range fun i => ((f (M.simple i) : ↥T) : X)) = T := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact (f (M.simple i)).2
  · intro φ hφ
    obtain ⟨w, hw⟩ := f.surjective ⟨φ, hφ⟩
    have hw' : ((f w : ↥T) : X) = φ := congrArg Subtype.val hw
    rw [← hw']
    have hmem : w ∈ Subgroup.closure (Set.range M.simple) := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple M,
        M.toCoxeterSystem.subgroup_closure_range_simple]
      exact Subgroup.mem_top _
    refine Subgroup.closure_induction (k := Set.range M.simple)
      (p := fun w _ => ((f w : ↥T) : X) ∈
        Subgroup.closure (Set.range fun i => ((f (M.simple i) : ↥T) : X))) ?_ ?_ ?_ ?_ hmem
    · rintro _ ⟨i, rfl⟩
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · simp
    · intro x y _ _ hx hy
      simpa using Subgroup.mul_mem _ hx hy
    · intro x _ hx
      simpa using Subgroup.inv_mem _ hx

end CFSG.StandardType

end
