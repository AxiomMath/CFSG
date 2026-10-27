module

public import CFSG.LieType.Ree.Endo

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.B3Exact

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Chevalley CFSG.LieType.Chevalley.RootOps
  CFSG.LieType.BorelTits CFSG.LieType.Ree

section Narrow

namespace Narrow

theorem eq_of_eqOn_narrow {t : ReeTag} {K : Type} [Field K] (hf : t.ShortFaithful K)
    {g g' : ModGL t.tag K} (hg : g ∈ adjointGroup t.tag K) (hg' : g' ∈ adjointGroup t.tag K)
    (h : ∀ v ∈ t.shortModule K,
      (g : Module.End K (RootModule t.tag K)) v = (g' : Module.End K (RootModule t.tag K)) v) :
    g = g' := by
  have h1 := hf (g'⁻¹ * g) (mul_mem (inv_mem hg') hg) fun v hv => by
    rw [Units.val_mul, Module.End.mul_apply, h v hv, ← Module.End.mul_apply, ← Units.val_mul,
      inv_mul_cancel, Units.val_one, Module.End.one_apply]
  rwa [inv_mul_eq_one, eq_comm] at h1

theorem twist_unique_narrow
    {t : ReeTag} {K : Type} [Field K] (hf : t.ShortFaithful K)
    {g₁ g₂ : ModGL t.tag K} (h₁ : g₁ ∈ adjointGroup t.tag K)
    (h₂ : g₂ ∈ adjointGroup t.tag K)
    (h : (g₁ : Module.End K (RootModule t.tag K)) * t.lengthMap K =
      (g₂ : Module.End K (RootModule t.tag K)) * t.lengthMap K) : g₁ = g₂ :=
  eq_of_eqOn_narrow hf h₁ h₂ fun v hv => by
    obtain ⟨u, rfl⟩ : v ∈ LinearMap.range (t.lengthMap K) := by rwa [ReeTag.range_lengthMap K]
    rw [← Module.End.mul_apply, h, Module.End.mul_apply]

theorem twist_spec_narrow
    {t : ReeTag} {K : Type} [Field K] (hp : (t.prime : K) = 0)
    (g : adjointGroup t.tag K) :
    glRep (adjointGroup t.tag K) (t.twist K hp g) * t.lengthMap K =
      t.lengthMap K * glRep (adjointGroup t.tag K) g :=
  (ReeTag.exists_twist hp g.2).choose_spec.2

theorem twist_eq_of_narrow
    {t : ReeTag} {K : Type} [Field K] (hp : (t.prime : K) = 0)
    (hf : t.ShortFaithful K) {g g' : adjointGroup t.tag K}
    (h : glRep (adjointGroup t.tag K) g' * t.lengthMap K =
      t.lengthMap K * glRep (adjointGroup t.tag K) g) :
    t.twist K hp g = g' :=
  Subtype.ext (twist_unique_narrow hf (t.twist K hp g).2 g'.2 ((twist_spec_narrow hp g).trans
      h.symm))

noncomputable def exceptionalEndoNarrow
    {t : ReeTag} (K : Type) [Field K]
    (hp : (t.prime : K) = 0) (hf : t.ShortFaithful K) :
    adjointGroup t.tag K →* adjointGroup t.tag K where
  toFun := t.twist K hp
  map_one' := twist_eq_of_narrow hp hf (by simp only [map_one, one_mul, mul_one])
  map_mul' g h := twist_eq_of_narrow hp hf (by
    rw [map_mul, map_mul, mul_assoc, twist_spec_narrow, ← mul_assoc, twist_spec_narrow, mul_assoc])

theorem exceptionalEndoNarrow_xElement
    {t : ReeTag} {K : Type} [Field K]
    (hp : (t.prime : K) = 0) (hf : t.ShortFaithful K) (i : Fin t.tag.rank) (c : K) :
    exceptionalEndoNarrow K hp hf (xElement i c) = xElement (t.perm i) (c ^ t.exponent i) :=
  twist_eq_of_narrow hp hf (ReeTag.lengthMap_mul_xOp K hp i c).symm

theorem exceptionalEndoNarrow_yElement
    {t : ReeTag} {K : Type} [Field K]
    (hp : (t.prime : K) = 0) (hf : t.ShortFaithful K) (i : Fin t.tag.rank) (c : K) :
    exceptionalEndoNarrow K hp hf (yElement i c) = yElement (t.perm i) (c ^ t.exponent i) :=
  twist_eq_of_narrow hp hf (ReeTag.lengthMap_mul_yOp K hp i c).symm

theorem closure_xElement_yElement_narrow
    {τ : Tag} {K : Type} [Field K] :
    Subgroup.closure {g : adjointGroup τ K | ∃ (i : Fin τ.rank) (c : K),
      g = xElement i c ∨ g = yElement i c} = ⊤ := by
  have hcl : Subgroup.closure (((↑) : adjointGroup τ K → ModGL τ K) ⁻¹'
      {g | ∃ (i : Fin τ.rank) (c : K), (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c}) = ⊤ :=
    Subgroup.closure_closure_coe_preimage
  rw [eq_top_iff, ← hcl]
  refine Subgroup.closure_mono fun g ⟨i, c, h⟩ => ⟨i, c, ?_⟩
  rcases h with h | h
  · exact .inl (Subtype.ext (Units.ext h))
  · exact .inr (Subtype.ext (Units.ext h))

theorem exponent_F4_eq_one_or_two (i : Fin ReeTag.F4.tag.rank) :
    ReeTag.F4.exponent i = 1 ∨ ReeTag.F4.exponent i = 2 := by
  by_cases h : i ∈ ReeTag.F4.longSet
  · exact Or.inl (by simp [ReeTag.exponent, h])
  · exact Or.inr (by simp [ReeTag.exponent, h, ReeTag.prime])

theorem exists_sq_eq_charTwo_narrow {K : Type} [Field K] [Finite K] [CharP K 2] (c : K) :
    ∃ d : K, d ^ 2 = c :=
  Finite.surjective_of_injective (f := fun x : K => x ^ 2)
    (fun _ _ h => CharTwo.sq_injective h) c

theorem F4_prime_cast_eq_zero (K : Type) [Field K] [CharP K 2] :
    (ReeTag.F4.prime : K) = 0 := by
  rw [show ReeTag.F4.prime = 2 from rfl]
  exact CharP.cast_eq_zero K 2

theorem exceptionalEndoNarrow_F4_surjective
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf : ReeTag.F4.ShortFaithful K) :
    Function.Surjective (exceptionalEndoNarrow (t :=
        ReeTag.F4) K (F4_prime_cast_eq_zero K) hf) := by
  rw [← MonoidHom.range_eq_top]
  apply le_antisymm le_top
  intro x hx
  have hcl := closure_xElement_yElement_narrow (τ := ReeTag.F4.tag) (K := K)
  have hx' : x ∈ Subgroup.closure {g : adjointGroup ReeTag.F4.tag K |
      ∃ (i : Fin ReeTag.F4.tag.rank) (c : K), g = xElement i c ∨ g = yElement i c} := by
    rw [hcl]; exact hx
  have hle : Subgroup.closure {g : adjointGroup ReeTag.F4.tag K |
      ∃ (i : Fin ReeTag.F4.tag.rank) (c : K), g = xElement i c ∨ g = yElement i c} ≤
      (exceptionalEndoNarrow (t := ReeTag.F4) K (F4_prime_cast_eq_zero K) hf).range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, c, rfl | rfl⟩
    · rcases exponent_F4_eq_one_or_two (ReeTag.F4.perm i) with he | he
      · refine ⟨xElement (ReeTag.F4.perm i) c, ?_⟩
        rw [exceptionalEndoNarrow_xElement, ReeTag.perm_perm ReeTag.F4 i, he, pow_one]
      · obtain ⟨d, hd⟩ := exists_sq_eq_charTwo_narrow c
        refine ⟨xElement (ReeTag.F4.perm i) d, ?_⟩
        rw [exceptionalEndoNarrow_xElement, ReeTag.perm_perm ReeTag.F4 i, he, hd]
    · rcases exponent_F4_eq_one_or_two (ReeTag.F4.perm i) with he | he
      · refine ⟨yElement (ReeTag.F4.perm i) c, ?_⟩
        rw [exceptionalEndoNarrow_yElement, ReeTag.perm_perm ReeTag.F4 i, he, pow_one]
      · obtain ⟨d, hd⟩ := exists_sq_eq_charTwo_narrow c
        refine ⟨yElement (ReeTag.F4.perm i) d, ?_⟩
        rw [exceptionalEndoNarrow_yElement, ReeTag.perm_perm ReeTag.F4 i, he, hd]
  exact hle hx'

theorem exceptionalEndoNarrow_F4_injective
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf : ReeTag.F4.ShortFaithful K) :
    Function.Injective (exceptionalEndoNarrow (t := ReeTag.F4) K (F4_prime_cast_eq_zero K) hf) :=
  Finite.injective_iff_surjective.2 (exceptionalEndoNarrow_F4_surjective hf)

theorem exceptionalEndoNarrow_F4_bijective
    {K : Type} [Field K] [Finite K] [CharP K 2]
    (hf : ReeTag.F4.ShortFaithful K) :
    Function.Bijective (exceptionalEndoNarrow (t := ReeTag.F4) K (F4_prime_cast_eq_zero K) hf) :=
  ⟨exceptionalEndoNarrow_F4_injective hf, exceptionalEndoNarrow_F4_surjective hf⟩

end Narrow

end Narrow

theorem f4_repsCheck_without68 : repsCheck .F4 f4Reps = true := by
  decide +kernel

theorem f4_coverCheck_without68 : coverCheck .F4 f4Reps f4Cover = true := by
  decide +kernel

theorem f4_simple_commContained_without68
    (K : Type) [Field K] (i : Fin (Tag.rank .F4))
    (β : Root .F4) (hβ : 0 < height β.1) (hne : β ≠ simpleRoot .F4 i) :
    (rootOperatorFamily .F4).CommContained K (simpleRoot .F4 i) β :=
  commContained_of_checks K dataChecks_F4.valid dataChecks_F4.tab
    f4_repsCheck_without68 f4_coverCheck_without68 i β hβ hne

noncomputable def f4RootSubgroups
    (K : Type) [Field K] : RootSubgroups .F4 K :=
  (rootOperatorFamily .F4).toRootSubgroups K
    fun i β hβ hne => f4_simple_commContained_without68 K i β hβ hne

@[simp] theorem f4RootSubgroups_X
    (K : Type) [Field K] :
    (f4RootSubgroups K).X = (rootOperatorFamily .F4).rootSubgroup K :=
  (rootOperatorFamily .F4).toRootSubgroups_X K _

noncomputable def f4RootGroupData
    (K : Type) [Field K] [Finite K] :
    RootGroupData (rootCombinatorics .F4) ↥(adjointGroup .F4 K) :=
  (f4RootSubgroups K).toRootGroupData

end CFSG.StandardType.F4ExplicitPos.B3Exact

end

end
