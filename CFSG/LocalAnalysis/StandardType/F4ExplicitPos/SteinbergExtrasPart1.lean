module

public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart25
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.UnipotentNo117Part1

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.SteinbergExtras

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.LieType.TitsSimplicity CFSG.StandardType.F4ExplicitPos.UnipotentNo117

open scoped commutatorElement

variable {τ : Tag} {K : Type} [Field K]

theorem rootGroup_of_isRootN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ}
    (h : IsRoot τ γ) : rootGroup F K γ = F.rootSubgroup K ⟨γ, h⟩ := by
  classical
  exact dite_eq_left h

theorem rootGroup_of_not_isRootN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ}
    (h : ¬IsRoot τ γ) : rootGroup F K γ = ⊥ := by
  classical
  exact dite_eq_right h

theorem xPar_memN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) (c : K) :
    xPar F γ c ∈ rootGroup F K γ := by
  rw [xPar_of_isRoot_without117 F h, rootGroup_of_isRootN F h]
  exact F.eltElement_mem_rootSubgroup _ c

theorem mem_rootGroup_iffN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ)
    (g : adjointGroup τ K) : g ∈ rootGroup F K γ ↔ ∃ c, xPar F γ c = g := by
  constructor
  · intro hg
    rw [rootGroup_of_isRootN F h] at hg
    obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hg
    exact ⟨c, xPar_of_isRoot_without117 F h c⟩
  · rintro ⟨c, rfl⟩
    exact xPar_memN F h c

theorem exists_of_mem_rootGroupN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ}
    (h : IsRoot τ γ) {g : adjointGroup τ K} (hg : g ∈ rootGroup F K γ) :
    ∃ c : K, g = F.eltElement ⟨γ, h⟩ c := by
  rw [rootGroup_of_isRootN F h] at hg
  obtain ⟨c, rfl⟩ := F.mem_rootSubgroup.1 hg
  exact ⟨c, rfl⟩

theorem endHom_eltElementN
    (F : RootOperatorFamily τ) (α : Root τ) (c : K) :
    endHom K (F.eltElement α c) = F.elt K α c := rfl

theorem endHom_eq_oneN {g : adjointGroup τ K} (h : endHom K g = 1) : g = 1 :=
  endHom_injective (h.trans (map_one _).symm)

theorem xPar_injectiveN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    Function.Injective (xPar F γ : K → adjointGroup τ K) := by
  intro c d hcd
  obtain ⟨a, b, hab⟩ := exists_D_one_apply_ne_zero_w F (R := K) ⟨γ, h⟩
  have hshift : labelWt τ a = labelWt τ b + γ := by
    have := F.mapsLabelWt_D (R := K) ⟨γ, h⟩ le_rfl a b hab
    rwa [one_nsmul] at this
  have h1 := congrArg (fun g => endHom K g (Finsupp.single b 1) a) hcd
  simp only [xPar_of_isRoot_without117 F h, endHom_eltElementN,
    elt_apply_of_shift_w F ⟨γ, h⟩ _ hshift] at h1
  exact mul_right_cancel₀ hab h1

theorem rootGroup_ne_botN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ} (h : IsRoot τ γ) :
    rootGroup F K γ ≠ ⊥ := by
  intro hbot
  have h1 := xPar_memN F h (1 : K)
  rw [hbot, Subgroup.mem_bot, ← xPar_zero_without117 F γ] at h1
  exact one_ne_zero (xPar_injectiveN F h h1)

theorem roots_eq_setOf_isRootN
    (F : RootOperatorFamily τ) :
    (adjDatum F K).roots = {γ | IsRoot τ γ} := by
  change CFSG.LieType.RootSystem.roots (isFiniteType_cartan τ) (∅ : Set (Fin τ.rank)) =
    {γ | IsRoot τ γ}
  ext γ
  constructor
  · rintro (⟨w, i, rfl⟩ | ⟨w, i, hi, -⟩)
    · obtain ⟨ω, rfl⟩ :=
        (coxeterMatrix (isFiniteType_cartan τ)).toCoxeterSystem.wordProd_surjective w
      induction ω with
      | nil => simpa using IsRoot.basis i
      | cons j ω ih =>
        rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple,
          reflection_apply]
        exact IsRoot.reflect j ih
    · exact absurd hi (Set.notMem_empty i)
  · intro h
    induction h with
    | basis j => exact Or.inl ⟨1, j, by simp⟩
    | @reflect i v _ ih =>
      rcases ih with ⟨w, j, hw⟩ | ⟨w, j, hj, -⟩
      · refine Or.inl ⟨(coxeterMatrix (isFiniteType_cartan τ)).toCoxeterSystem.simple i * w,
          j, ?_⟩
        rw [weylAction_mul_apply, ← hw, weylAction_simple, reflection_apply]
        rfl
      · exact absurd hj (Set.notMem_empty j)

theorem mem_adjDatum_rootsN
    (F : RootOperatorFamily τ) {γ : Fin τ.rank → ℤ} :
    γ ∈ (adjDatum F K).roots ↔ IsRoot τ γ := by
  rw [roots_eq_setOf_isRootN F]
  rfl

theorem prodInjectiveN
    (F : RootOperatorFamily τ) (φ : (Fin τ.rank → ℤ) →+ ℤ)
    (L : List (Fin τ.rank → ℤ)) (hnd : L.Nodup)
    (hL : ∀ γ ∈ L, IsRoot τ γ ∧ 0 < φ γ) (hsort : L.Pairwise fun γ δ => φ γ ≤ φ δ) :
    ProdInjectiveFor (rootGroup F K) L := by
  classical
  intro f g hf hg heq
  have hcf : ∀ γ ∈ L, ∃ c, xPar F γ c = f γ := fun γ hγ =>
    (mem_rootGroup_iffN F (hL γ hγ).1 _).1 (hf γ hγ)
  have hcg : ∀ γ ∈ L, ∃ c, xPar F γ c = g γ := fun γ hγ =>
    (mem_rootGroup_iffN F (hL γ hγ).1 _).1 (hg γ hγ)
  set c : (Fin τ.rank → ℤ) → K := fun γ => if h : γ ∈ L then (hcf γ h).choose else 0
  set c' : (Fin τ.rank → ℤ) → K := fun γ => if h : γ ∈ L then (hcg γ h).choose else 0
  have hfc : ∀ γ ∈ L, f γ = xPar F γ (c γ) := fun γ hγ => by
    simp only [c, dite_eq_left hγ]
    exact (hcf γ hγ).choose_spec.symm
  have hgc : ∀ γ ∈ L, g γ = xPar F γ (c' γ) := fun γ hγ => by
    simp only [c', dite_eq_left hγ]
    exact (hcg γ hγ).choose_spec.symm
  have hprod : (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c γ)).prod =
      (L.map fun γ => RootOperatorFamily'.eltOr F K γ (c' γ)).prod := by
    have h1 := congrArg (endHom K) heq
    rw [map_list_prod, map_list_prod, List.map_map, List.map_map] at h1
    have e1 : L.map (endHom K ∘ f) = L.map fun γ => RootOperatorFamily'.eltOr F K γ (c γ) :=
      List.map_congr_left fun γ hγ => by
        simp only [Function.comp_apply, hfc γ hγ, endHom_xPar_without117 F]
    have e2 : L.map (endHom K ∘ g) = L.map fun γ => RootOperatorFamily'.eltOr F K γ (c' γ) :=
      List.map_congr_left fun γ hγ => by
        simp only [Function.comp_apply, hgc γ hγ, endHom_xPar_without117 F]
    rwa [e1, e2] at h1
  intro γ hγ
  rw [hfc γ hγ, hgc γ hγ,
    prod_eltOr_injective_w F L hnd hL hsort c c' hprod γ hγ]

noncomputable def unipN (φ : (Fin τ.rank → ℤ) →+ ℤ) : Subgroup (adjointGroup τ K) where
  carrier := {g | Raises φ 1 (endHom K g - 1) ∧ Raises φ 1 (endHom K g⁻¹ - 1)}
  mul_mem' {_ _} hg hh := by
    refine ⟨?_, ?_⟩
    · rw [map_mul, RootOperatorFamily'.mul_sub_one]
      exact (Raises.add hg.1 hh.1).add ((raises_mul hg.1 hh.1).mono (by omega))
    · rw [mul_inv_rev, map_mul, RootOperatorFamily'.mul_sub_one]
      exact (Raises.add hh.2 hg.2).add ((raises_mul hh.2 hg.2).mono (by omega))
  one_mem' := ⟨by simpa using Raises.zero (R := K) (τ := τ) (φ := φ) 1,
    by simpa using Raises.zero (R := K) (τ := τ) (φ := φ) 1⟩
  inv_mem' {_} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

noncomputable def triN (φ : (Fin τ.rank → ℤ) →+ ℤ) : Subgroup (adjointGroup τ K) where
  carrier := {g | Raises φ 0 (endHom K g) ∧ Raises φ 0 (endHom K g⁻¹)}
  mul_mem' {_ _} hg hh :=
    ⟨by rw [map_mul]; exact (raises_mul hg.1 hh.1).mono (by omega),
      by rw [mul_inv_rev, map_mul]; exact (raises_mul hh.2 hg.2).mono (by omega)⟩
  one_mem' := ⟨by rw [map_one]; exact (IsDiag.raises φ fun b => ⟨1, by simp⟩),
    by rw [inv_one, map_one]; exact (IsDiag.raises φ fun b => ⟨1, by simp⟩)⟩
  inv_mem' {_} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem IsDiag_mulN {A B : Module.End K (RootModule τ K)} (hA : IsDiag A) (hB : IsDiag B) :
    IsDiag (A * B) := fun b => by
  obtain ⟨μ, hμ⟩ := hB b
  obtain ⟨ν, hν⟩ := hA b
  exact ⟨μ * ν, by rw [Module.End.mul_apply, hμ, map_smul, hν, smul_smul]⟩

noncomputable def diagN (K : Type) [Field K] : Subgroup (adjointGroup τ K) where
  carrier := {g | IsDiag (endHom K g) ∧ IsDiag (endHom K g⁻¹)}
  mul_mem' {_ _} hg hh :=
    ⟨by rw [map_mul]; exact IsDiag_mulN hg.1 hh.1,
      by rw [mul_inv_rev, map_mul]; exact IsDiag_mulN hh.2 hg.2⟩
  one_mem' := ⟨fun _ => ⟨1, by simp⟩, fun _ => ⟨1, by simp⟩⟩
  inv_mem' {_} hg := ⟨hg.2, by rw [inv_inv]; exact hg.1⟩

theorem one_raises_zeroN (φ : (Fin τ.rank → ℤ) →+ ℤ) :
    Raises φ 0 (1 : Module.End K (RootModule τ K)) :=
  IsDiag.raises φ fun b => ⟨1, by simp⟩

theorem unip_le_triN (φ : (Fin τ.rank → ℤ) →+ ℤ) :
    unipN (K := K) φ ≤ triN (K := K) φ := fun g hg => by
  have h1 : endHom K g = 1 + (endHom K g - 1) := by abel
  have h2 : endHom K g⁻¹ = 1 + (endHom K g⁻¹ - 1) := by abel
  exact ⟨by rw [h1]; exact (one_raises_zeroN φ).add (hg.1.mono (by omega)),
    by rw [h2]; exact (one_raises_zeroN φ).add (hg.2.mono (by omega))⟩

theorem diag_le_triN (φ : (Fin τ.rank → ℤ) →+ ℤ) : diagN (τ := τ) K ≤ triN (K := K) φ :=
  fun _ hg => ⟨hg.1.raises φ, hg.2.raises φ⟩

theorem torus_le_diagN
    (i : Fin τ.rank) : torus (τ := τ) K i ≤ diagN (τ := τ) K := by
  rintro _ ⟨t, rfl⟩
  refine ⟨fun b => ⟨_, torusElt_single i t b⟩, fun b => ?_⟩
  have : (torusHom K i t)⁻¹ = torusHom K i t⁻¹ := (map_inv _ t).symm
  rw [this]
  exact ⟨_, torusElt_single i t⁻¹ b⟩

theorem rootGroup_le_unipN
    (F : RootOperatorFamily τ) (φ : (Fin τ.rank → ℤ) →+ ℤ)
    {γ : Fin τ.rank → ℤ} (hγ : 0 < φ γ) : rootGroup F K γ ≤ unipN (K := K) φ := by
  by_cases h : IsRoot τ γ
  · intro g hg
    obtain ⟨c, rfl⟩ := exists_of_mem_rootGroupN F h hg
    have hinv : (F.eltElement ⟨γ, h⟩ c)⁻¹ = F.eltElement ⟨γ, h⟩ (-c) := by
      rw [eq_comm, eq_inv_iff_mul_eq_one, ← F.eltElement_add, neg_add_cancel, F.eltElement_zero]
    refine ⟨?_, ?_⟩
    · exact (elt_sub_one_raises_w F ⟨γ, h⟩ hγ.le c).mono
        (show (1 : ℤ) ≤ φ γ by omega)
    · rw [hinv]
      exact (elt_sub_one_raises_w F ⟨γ, h⟩ hγ.le (-c)).mono
        (show (1 : ℤ) ≤ φ γ by omega)
  · rw [rootGroup_of_not_isRootN F h]
    exact bot_le

theorem tri_inf_unip_negN (φ : (Fin τ.rank → ℤ) →+ ℤ) :
    triN (K := K) φ ⊓ unipN (K := K) (-φ) = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨h1, -⟩, h2, -⟩ := hg
  refine Subgroup.mem_bot.2 (endHom_eq_oneN ?_)
  refine sub_eq_zero.1 (Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_))
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, LinearMap.zero_apply,
    Finsupp.zero_apply]
  by_contra hne
  have h3 := h2 a b hne
  simp only [AddMonoidHom.neg_apply] at h3
  by_cases hab : a = b
  · subst hab
    omega
  · have hne' : endHom K g (Finsupp.single b 1) a ≠ 0 := by
      rwa [LinearMap.sub_apply, Module.End.one_apply, Finsupp.sub_apply,
        Finsupp.single_eq_of_ne hab, sub_zero] at hne
    have := h1 a b hne'
    omega

theorem unip_inf_unip_negN (φ : (Fin τ.rank → ℤ) →+ ℤ) :
    unipN (K := K) φ ⊓ unipN (K := K) (-φ) = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_right _ (unip_le_triN φ)).trans (tri_inf_unip_negN φ).le)

theorem diag_inf_unipN (φ : (Fin τ.rank → ℤ) →+ ℤ) :
    diagN (τ := τ) K ⊓ unipN (K := K) φ = ⊥ := by
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨⟨h1, -⟩, h2, -⟩ := hg
  refine Subgroup.mem_bot.2 (endHom_eq_oneN ?_)
  refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring ?_
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Module.End.one_apply]
  obtain ⟨μ, hμ⟩ := h1 b
  rw [hμ]
  by_cases hμ1 : μ = 1
  · rw [hμ1, one_smul]
  · exfalso
    have h3 := h2 b b (by
      rw [LinearMap.sub_apply, hμ, Module.End.one_apply, Finsupp.sub_apply, Finsupp.smul_apply,
        Finsupp.single_eq_same, smul_eq_mul, mul_one]
      exact sub_ne_zero.2 hμ1)
    omega

theorem iSup_torus_inf_unipN
    (φ : (Fin τ.rank → ℤ) →+ ℤ) :
    (⨆ i, torus (τ := τ) K i) ⊓ unipN (K := K) φ = ⊥ :=
  eq_bot_iff.2 ((inf_le_inf_right _ (iSup_le fun i => torus_le_diagN i)).trans
    (diag_inf_unipN φ).le)

section F4

variable [CharP K 2]

theorem f4_commutator_memN
    {γ δ : Fin Tag.F4.rank → ℤ}
    (hγ : γ ∈ (f4Datum K).roots) (hδ : δ ∈ (f4Datum K).roots) (hlin : LinIndepPair γ δ)
    {x y : adjointGroup Tag.F4 K} (hx : x ∈ (f4Datum K).rootGroup γ)
    (hy : y ∈ (f4Datum K).rootGroup δ) :
    ⁅x, y⁆ ∈ ⨆ ε ∈ openCone (f4Datum K).roots γ δ, (f4Datum K).rootGroup ε := by
  have hγ' : IsRoot Tag.F4 γ := (mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).1 hγ
  have hδ' : IsRoot Tag.F4 δ := (mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).1 hδ
  have hne : γ ≠ δ := fun h => by
    have := (hlin 1 (-1) (by rw [h, one_smul, neg_one_smul, add_neg_cancel])).1
    exact one_ne_zero this
  have hne' : γ ≠ -δ := fun h => by
    have := (hlin 1 1 (by rw [h, one_smul, one_smul, neg_add_cancel])).1
    exact one_ne_zero this
  obtain ⟨c, rfl⟩ := (mem_rootGroup_iffN (rootOperatorFamily Tag.F4) hγ' x).1 hx
  obtain ⟨d, rfl⟩ := (mem_rootGroup_iffN (rootOperatorFamily Tag.F4) hδ' y).1 hy
  have key : ∀ a b : ℕ, 0 < a → 0 < b → ∀ e : K,
      xPar (rootOperatorFamily Tag.F4) (a • γ + b • δ) e ∈
        ⨆ ε ∈ openCone (f4Datum K).roots γ δ, (f4Datum K).rootGroup ε := by
    intro a b ha hb e
    by_cases hr : IsRoot Tag.F4 (a • γ + b • δ)
    · refine Subgroup.mem_iSup_of_mem (a • γ + b • δ) (Subgroup.mem_iSup_of_mem ?_ ?_)
      · exact ⟨(mem_adjDatum_rootsN (rootOperatorFamily Tag.F4)).2 hr, a, b, ha, hb, rfl⟩
      · exact xPar_memN (rootOperatorFamily Tag.F4) hr e
    · rw [xPar_of_not_isRoot_without117 (rootOperatorFamily Tag.F4) hr]
      exact one_mem _
  rw [commutator_xPar_without117 (F := rootOperatorFamily Tag.F4) (K := K)
    CFSG.StandardType.F4ExplicitPos.DataValid.f4Data_valid_without117 noG2_F4 hγ' hδ' hne hne']
  refine mul_mem (mul_mem ?_ ?_) ?_
  · have := key 1 1 one_pos one_pos
      ((RootOperatorFamily'.coeff11_without117 (rootOperatorFamily Tag.F4)
        DataValid.f4Data_valid_without117 ⟨γ, hγ'⟩ ⟨δ, hδ'⟩ : K) * c * d)
    rwa [one_smul, one_smul] at this
  · have := key 1 2 one_pos two_pos
      ((RootOperatorFamily'.coeff12_without117 (rootOperatorFamily Tag.F4)
        DataValid.f4Data_valid_without117 ⟨γ, hγ'⟩ ⟨δ, hδ'⟩ : K) * c * d ^ 2)
    rwa [one_smul] at this
  · have := key 2 1 two_pos one_pos
      ((RootOperatorFamily'.coeff21_without117 (rootOperatorFamily Tag.F4)
        DataValid.f4Data_valid_without117 ⟨γ, hγ'⟩ ⟨δ, hδ'⟩ : K) * c ^ 2 * d)
    rwa [one_smul] at this

end F4

end CFSG.StandardType.F4ExplicitPos.SteinbergExtras
end

end
