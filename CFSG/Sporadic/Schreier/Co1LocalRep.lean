module

public import CFSG.Sporadic.Schreier.Co1LocalModuleBound
public import CFSG.Sporadic.Schreier.Co1WeightInternal
public import CFSG.RepresentationTheory.PerfectWeightStabilizerModule

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix WeightProj CFSG.RepresentationTheory
open scoped Pointwise

instance EA_normal :
    (E.subgroupOf A).Normal := E_normal_A

@[expose] def ofEA : E.subgroupOf A →* E where
  toFun e := ⟨e.1.1, Subgroup.mem_subgroupOf.mp e.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[expose] def toEA : E →* E.subgroupOf A where
  toFun e := ⟨⟨e, E_le_A e.2⟩, Subgroup.mem_subgroupOf.mpr e.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem EA_comm :

    ∀ x ∈ E.subgroupOf A, ∀ y ∈ E.subgroupOf A, x * y = y * x := fun x hx y hy =>
  Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (E_comm _ (Subgroup.mem_subgroupOf.mp hx) _ (Subgroup.mem_subgroupOf.mp hy)).eq)

theorem EA_inf_CA :
    E.subgroupOf A ⊓ C.subgroupOf A = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h : (x : GL24) ∈ E ⊓ C := Subgroup.mem_inf.mpr
    ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).1,
      Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hx).2⟩
  rw [E_inf_C, Subgroup.mem_bot] at h
  exact Subtype.ext h

theorem EA_sup_CA :
    E.subgroupOf A ⊔ C.subgroupOf A = ⊤ := by
  rw [eq_top_iff]
  rintro x -
  have hx : (x : GL24) ∈ (E : Set GL24) * (C : Set GL24) := by
    rw [← A_eq_mul]
    exact x.2
  obtain ⟨e, he, c, hc, hec⟩ := hx
  have : x = ⟨e, E_le_A he⟩ * ⟨c, C_le_A hc⟩ :=
    Subtype.ext (by rw [Subgroup.coe_mul]; exact hec.symm)
  rw [this]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr he) (Subgroup.mem_subgroupOf.mpr hc)

@[expose] noncomputable def chiA
    (f : Fin 6 → ZMod 3) : E.subgroupOf A →* Kbarˣ :=
  (charK f).comp ofEA

theorem chiA_apply
    (f : Fin 6 → ZMod 3) (e : E.subgroupOf A) :
    chiA f e = Units.map ι4.toMonoidHom (charV f ((e : A) : GL24)) := by
  rw [charV_of_mem f (x := ((e : A) : GL24)) (Subgroup.mem_subgroupOf.mp e.2)]
  rfl

theorem chiA_injective :
    Function.Injective chiA := by
  intro f f' h
  apply charK_injective
  ext e
  exact congrArg Units.val (DFunLike.congr_fun h (toEA e))

noncomputable abbrev orbA :
    Set (E.subgroupOf A →* Kbarˣ) :=
  RepresentationTheory.charOrbit (E.subgroupOf A) (C.subgroupOf A) (chiA (γ 0))

theorem charConj_chiA
    {f f' : Fin 6 → ZMod 3} (x : A)
    (h : ∀ e ∈ E, charV f' e = charV f ((x : GL24)⁻¹ * e * x)) :
    charConj (E.subgroupOf A) (chiA f) x = chiA f' := by
  ext e
  rw [charConj_apply, chiA_apply, chiA_apply, h _ (Subgroup.mem_subgroupOf.mp e.2),
    Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

theorem orbRep_one : orbRep 1 = γ 0 := rfl

theorem charConj_chiA_mem
    (c : A) :
    ∃ f ∈ orbSet 1, charConj (E.subgroupOf A) (chiA (γ 0)) c = chiA f := by
  obtain ⟨f, hf⟩ := exists_charE_eq (charConjE (γ 0) c.2)
  have hrel : ∀ e ∈ E, charV f e = charV (γ 0) ((c : GL24)⁻¹ * e * c) := fun e he => by
    rw [charV_of_mem _ he, ← hf, charConjE_apply]
  refine ⟨f, ?_, charConj_chiA c hrel⟩
  have hmem : f ∈ charOrbit (orbRep 1) := ⟨c, c.2, by rw [orbRep_one]; exact hrel⟩
  rw [charOrbit_orbRep] at hmem
  exact hmem

theorem chiA_mem_charOrbit
    {f : Fin 6 → ZMod 3} (hf : f ∈ orbSet 1) :
    chiA f ∈ orbA := by
  have hmem : f ∈ CFSG.Sporadic.Co1Schreier.charOrbit (orbRep 1) := by
    rw [charOrbit_orbRep]
    exact hf
  obtain ⟨x, hx, hxf⟩ := hmem
  have hxEC : x ∈ (E : Set GL24) * (C : Set GL24) := by
    rw [← A_eq_mul]
    exact hx
  obtain ⟨e₀, he₀, c, hc, rfl⟩ := hxEC
  refine ⟨⟨c, C_le_A hc⟩, Subgroup.mem_subgroupOf.mpr hc, charConj_chiA _ fun e he => ?_⟩
  have hcomm : e₀⁻¹ * e * e₀ = e := by
    rw [mul_assoc, (E_comm e he e₀ he₀).eq, inv_mul_cancel_left]
  rw [hxf e he, orbRep_one, show (e₀ * c)⁻¹ * e * (e₀ * c) = c⁻¹ * (e₀⁻¹ * e * e₀) * c by group,
    hcomm]

theorem mem_charOrbit_chiA
    {μ : E.subgroupOf A →* Kbarˣ} :
    μ ∈ orbA ↔ ∃ f ∈ orbSet 1, μ = chiA f := by
  constructor
  · rintro ⟨c, -, rfl⟩
    exact charConj_chiA_mem c
  · rintro ⟨f, hf, rfl⟩
    exact chiA_mem_charOrbit hf

theorem mem_charStab_iff
    (c : A) :
    c ∈ charStab (E.subgroupOf A) (C.subgroupOf A) (chiA (γ 0)) ↔ (c : GL24) ∈ wStab := by
  constructor
  · rintro ⟨hc, hconj⟩
    refine ⟨Subgroup.mem_subgroupOf.mp hc, fun e he => ?_⟩
    have h1 := congrArg (fun χ : E.subgroupOf A →* Kbarˣ => ((χ (toEA ⟨e, he⟩) : Kbarˣ) : Kbar))
      hconj
    simp only [charConj_apply, chiA_apply] at h1
    rw [Subgroup.coe_mk, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact Units.ext (ι4.injective h1)
  · rintro ⟨hc, h⟩
    exact ⟨Subgroup.mem_subgroupOf.mpr hc, charConj_chiA c fun e he => (h e he).symm⟩

@[expose] noncomputable def wStabToCharStab :
    wStab →* charStab (E.subgroupOf A) (C.subgroupOf A) (chiA (γ 0)) where
  toFun w := ⟨⟨w, C_le_A (wStab_le_C w.2)⟩, (mem_charStab_iff _).mpr w.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem isPerfect_charStab :
    Group.IsPerfect (charStab (E.subgroupOf A) (C.subgroupOf A) (chiA (γ 0))) := by
  have : Group.IsPerfect wStab := Group.isPerfect_def.mpr commutator_wStab
  exact Group.IsPerfect.ofSurjective (f := wStabToCharStab) fun c =>
    ⟨⟨c.1, (mem_charStab_iff c.1).mp c.2⟩, rfl⟩

variable (ρ : A →* GL (Fin 24) (ZMod 2))

@[expose] noncomputable def repK : Representation Kbar A (Fin 24 → Kbar) where
  toFun x := Matrix.mulVecLin (rhoK ρ x)
  map_one' := by
    show Matrix.mulVecLin (rhoK ρ 1) = 1
    rw [rhoK_one, Matrix.mulVecLin_one]
    rfl
  map_mul' x y := by
    show Matrix.mulVecLin (rhoK ρ (x * y)) =
      Matrix.mulVecLin (rhoK ρ x) * Matrix.mulVecLin (rhoK ρ y)
    rw [rhoK_mul, Matrix.mulVecLin_mul]
    rfl

theorem repK_apply (x : A) (v : Fin 24 → Kbar) : repK ρ x v = rhoK ρ x *ᵥ v := rfl

theorem weightSpace_chiA
    (f : Fin 6 → ZMod 3) :
    weightSpace (E.subgroupOf A) (repK ρ) (chiA f) = wt ρ f := by
  rw [← wtChar_charK]
  ext v
  constructor
  · intro hv e
    exact hv (toEA e)
  · intro hv e
    exact hv (ofEA e)

@[expose] noncomputable def orbExp
    (μ : orbA) : Fin 6 → ZMod 3 :=
  Classical.choose (mem_charOrbit_chiA.mp μ.2)

theorem orbExp_spec
    (μ : orbA) :
    orbExp μ ∈ orbSet 1 ∧ (μ : E.subgroupOf A →* Kbarˣ) = chiA (orbExp μ) :=
  Classical.choose_spec (mem_charOrbit_chiA.mp μ.2)

theorem orbExp_injective :
    Function.Injective orbExp := by
  intro μ ν h
  apply Subtype.ext
  rw [(orbExp_spec μ).2, (orbExp_spec ν).2, h]

theorem weightSpace_orbExp
    (μ : orbA) :
    weightSpace (E.subgroupOf A) (repK ρ) μ = wt ρ (orbExp μ) := by
  rw [(orbExp_spec μ).2]
  exact weightSpace_chiA ρ _

variable {ρ}

theorem finrank_weightSpace
    (hE : ∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) (μ : orbA) :
    Module.finrank Kbar (weightSpace (E.subgroupOf A) (repK ρ) μ) = 1 := by
  have h := ((degree_bound ρ hE).2 rfl).1 (orbExp μ)
  simp only [(orbExp_spec μ).1, ↓reduceIte] at h
  rw [weightSpace_orbExp]
  exact h

theorem isInternal_weightSpace
    {dec : DecidableEq orbA} (hE : ∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) :
    DirectSum.IsInternal fun μ : orbA => weightSpace (E.subgroupOf A) (repK ρ) μ := by
  have hwt := ((degree_bound ρ hE).2 rfl).1
  have hbot : ∀ f, (∀ μ, orbExp μ ≠ f) → wtSpace (w := wK) (rhoE ρ) f = ⊥ := by
    intro f hf
    have hf1 : f ∉ orbSet 1 := fun hf1 => by
      apply hf ⟨chiA f, chiA_mem_charOrbit hf1⟩
      apply chiA_injective
      exact (orbExp_spec ⟨chiA f, chiA_mem_charOrbit hf1⟩).2.symm
    have h0 := hwt f
    simp only [hf1, ↓reduceIte] at h0
    exact Submodule.finrank_eq_zero.mp h0
  have h := isInternal_wtSpace_comp wK_cube wK_ne_one (rhoE_add ρ) (rhoE_zero ρ)
    orbExp_injective hbot
  have hfun : (fun μ : orbA => weightSpace (E.subgroupOf A) (repK ρ) μ) =
      fun μ => wt ρ (orbExp μ) :=
    funext fun μ => weightSpace_orbExp ρ μ
  rw [hfun]
  exact h

theorem exists_equiv_natural
    (hE : ∃ e : E, ρ ⟨e, E_le_A e.2⟩ ≠ 1) :
    ∃ f : (Fin 24 → Kbar) ≃ₗ[Kbar] (Fin 24 → Kbar),
      ∀ (x : A) (v : Fin 24 → Kbar), f (repK A.subtype x v) = repK ρ x (f v) := by
  classical
  have hE0 : ∃ e : E, A.subtype ⟨e, E_le_A e.2⟩ ≠ 1 :=
    ⟨⟨a 0, a_mem_E 0⟩, fun h => z_ne_one (by rw [← a_zero]; exact h)⟩
  obtain ⟨-, -, f, hf⟩ := perfect_weight_stabilizer_monomial_module_uniqueness
    (E.subgroupOf A) (C.subgroupOf A) EA_comm EA_inf_CA EA_sup_CA (chiA (γ 0))
    isPerfect_charStab (repK A.subtype) (repK ρ) (isInternal_weightSpace hE0)
    (finrank_weightSpace hE0) (isInternal_weightSpace hE) (finrank_weightSpace hE)
  exact ⟨f, hf⟩

end CFSG.Sporadic.Co1Schreier
