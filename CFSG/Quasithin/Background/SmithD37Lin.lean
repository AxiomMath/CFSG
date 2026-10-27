module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderTensorDecomp
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
public import CFSG.Quasithin.Background.SmithD37Fix
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.QuasithinUnique.Setup
open TensorProduct

variable {U : Type} [CommGroup U]

@[expose, instance_reducible] noncomputable def zmodModule (hU : ∀ u : U, u ^ 2 = 1) :
    Module (ZMod 2) (Additive U) :=
  AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    apply Additive.toMul.injective
    rw [toMul_add, ← pow_two]
    exact hU _

@[expose] def theta : U ≃* Multiplicative (Additive U) := MulEquiv.refl U

section Lin

variable (hU : ∀ u : U, u ^ 2 = 1)

@[expose] noncomputable def autLin :
    letI := zmodModule hU
    MulAut U ≃* (Additive U ≃ₗ[ZMod 2] Additive U) :=
  letI := zmodModule hU
  Layer.binPsi theta

theorem autLin_apply (g : MulAut U) (u : U) :
    letI := zmodModule hU
    autLin hU g (Additive.ofMul u) = Additive.ofMul (g u) := rfl

end Lin

@[expose] def subOf (S : AddSubgroup (Additive U)) : Subgroup U where
  carrier := {u | Additive.ofMul u ∈ S}
  one_mem' := S.zero_mem
  mul_mem' ha hb := S.add_mem ha hb
  inv_mem' ha := S.neg_mem ha

theorem subOf_eq_bot {S : AddSubgroup (Additive U)} (h : subOf S = ⊥) : S = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : Additive.toMul x ∈ subOf S := hx
  rw [h, Subgroup.mem_bot] at this
  rw [AddSubgroup.mem_bot]
  exact Additive.toMul.injective this

theorem subOf_eq_top {S : AddSubgroup (Additive U)} (h : subOf S = ⊤) : S = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have : Additive.toMul x ∈ subOf S := h ▸ Subgroup.mem_top _
  exact this

section Lin2

variable (hU : ∀ u : U, u ^ 2 = 1)

theorem isIrrAct_map {X : Subgroup (MulAut U)}
    (hirr : ∀ J : Subgroup U, (∀ g ∈ X, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤) :
    letI := zmodModule hU
    Offender.IsIrrAct (X.map (autLin hU).toMonoidHom) := by
  let _ : Module (ZMod 2) (Additive U) := zmodModule hU
  intro S hS
  have hJ : ∀ g ∈ X, ∀ u ∈ subOf S.toAddSubgroup, g u ∈ subOf S.toAddSubgroup := by
    intro g hg u hu
    have := hS (autLin hU g) ⟨g, hg, rfl⟩ (Additive.ofMul u) hu
    rwa [autLin_apply] at this
  rcases hirr _ hJ with h | h
  · left
    exact Submodule.toAddSubgroup_injective (subOf_eq_bot h)
  · right
    exact Submodule.toAddSubgroup_injective (subOf_eq_top h)

end Lin2

@[expose] def toFLin {k F W : Type*} [Field k] [Field F] [AddCommGroup W] [Module k W]
    [Module F W] (g : W ≃ₗ[k] W) (hg : ∀ (c : F) (w : W), g (c • w) = c • g w) :
    W ≃ₗ[F] W :=
  { g.toAddEquiv with map_smul' := hg }

@[expose] def pair (L₁ L₂ : Subgroup (MulAut U)) : Fin 2 → Subgroup (MulAut U) := ![L₁, L₂]

theorem pair_le_sup (L₁ L₂ : Subgroup (MulAut U)) (i : Fin 2) : pair L₁ L₂ i ≤ L₁ ⊔ L₂ := by
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem pair_comm {L₁ L₂ : Subgroup (MulAut U)}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x) {i j : Fin 2} (hij : i ≠ j) {x y : MulAut U}
    (hx : x ∈ pair L₁ L₂ i) (hy : y ∈ pair L₁ L₂ j) : x * y = y * x := by
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact hcomm x hx y hy
  · exact (hcomm y hy x hx).symm
  · exact absurd rfl hij

section Decomp

variable [Finite U] (hU : ∀ u : U, u ^ 2 = 1)

omit [Finite U] in
@[expose] def commutantAut (f : letI := zmodModule hU; Module.End (ZMod 2) (Additive U)) :
    Subgroup (MulAut U) :=
  letI := zmodModule hU
  { carrier := {g | ∀ w, f (autLin hU g w) = autLin hU g (f w)}
    one_mem' := fun w => by simp
    mul_mem' := fun {a b} ha hb w => by
      show f (autLin hU (a * b) w) = autLin hU (a * b) (f w)
      rw [map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, hb]
    inv_mem' := fun {a} ha w => by
      show f (autLin hU a⁻¹ w) = autLin hU a⁻¹ (f w)
      have h1 := ha (autLin hU a⁻¹ w)
      have h2 : autLin hU a (autLin hU a⁻¹ w) = w := by
        rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      rw [h2] at h1
      rw [h1, ← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl }

include hU in
theorem exists_tensor_decomp [Nontrivial U] {L₁ L₂ : Subgroup (MulAut U)}
    (hcomm : ∀ x ∈ L₁, ∀ y ∈ L₂, x * y = y * x)
    (hirr : ∀ J : Subgroup U, (∀ g ∈ L₁ ⊔ L₂, ∀ u ∈ J, g u ∈ J) → J = ⊥ ∨ J = ⊤) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : Algebra (ZMod 2) F)
      (V : Fin 2 → Type) (_ : ∀ i, AddCommGroup (V i)) (_ : ∀ i, Module F (V i))
      (ρ : ∀ i, ↥(pair L₁ L₂ i) →* (V i ≃ₗ[F] V i)) (e : Additive U ≃+ ⨂[F] i, V i),
      (∀ i, Nontrivial (V i)) ∧ (∀ i, Finite (V i)) ∧
      (∀ i (g : ↥(pair L₁ L₂ i)) (u : U), e (Additive.ofMul ((g : MulAut U) u)) =
        Offender.factorEnd i ((ρ i g : V i ≃ₗ[F] V i) : Module.End F (V i))
          (e (Additive.ofMul u))) ∧
      (∀ i, Submodule.span F
        (Set.range fun g => ((ρ i g : V i ≃ₗ[F] V i) : Module.End F (V i))) = ⊤) ∧
      (∀ g : MulAut U, (L₁ ⊔ L₂).map (MulAut.conj g).toMonoidHom = L₁ ⊔ L₂ →
        ∃ τ : F ≃+* F, ∀ (c : F) (x : ⨂[F] i, V i),
          e (Additive.ofMul (g (Additive.toMul (e.symm (c • x))))) =
            τ c • e (Additive.ofMul (g (Additive.toMul (e.symm x))))) := by
  let _ : Module (ZMod 2) (Additive U) := zmodModule hU
  set H := (L₁ ⊔ L₂).map (autLin hU).toMonoidHom with hHdef
  have hH : Offender.IsIrrAct H := isIrrAct_map hU hirr
  obtain ⟨F, _, _, _, _, _, hcommF, _, -, -, hnorm⟩ :=
    Offender.finite_irreducible_endomorphism_field_density.{0, 0, 0} H hH
  have hFlin : ∀ h ∈ H, ∀ (c : F) (w : Additive U), h (c • w) = c • h w := by
    intro h hh c w
    let f : Module.End (ZMod 2) (Additive U) :=
      { toFun := fun w => c • w
        map_add' := smul_add c
        map_smul' := fun r w =>
          ZMod.map_smul (DistribSMul.toAddMonoidHom (Additive U) c) r w }
    exact ((hcommF f).mpr ⟨c, fun _ => rfl⟩ h hh w).symm
  have hmemH : ∀ i (g : ↥(pair L₁ L₂ i)), autLin hU (g : MulAut U) ∈ H := fun i g =>
    ⟨g, pair_le_sup L₁ L₂ i g.2, rfl⟩
  let φ : ∀ i, ↥(pair L₁ L₂ i) →* (Additive U ≃ₗ[F] Additive U) := fun i =>
    { toFun := fun g => toFLin (autLin hU (g : MulAut U)) (hFlin _ (hmemH i g))
      map_one' := by ext w; rfl
      map_mul' := fun a b => by ext w; rfl }
  have hc : ∀ i j, i ≠ j → ∀ (x : ↥(pair L₁ L₂ i)) (y : ↥(pair L₁ L₂ j)),
      φ i x * φ j y = φ j y * φ i x := by
    intro i j hij x y
    have hxy := pair_comm hcomm hij x.2 y.2
    ext w
    exact congrArg (fun g : MulAut U => Additive.ofMul (g (Additive.toMul w))) hxy
  have hirrF : ∀ S : Submodule F (Additive U),
      (∀ i (g : ↥(pair L₁ L₂ i)), ∀ u ∈ S, φ i g u ∈ S) → S = ⊥ ∨ S = ⊤ := by
    intro S hS
    have hJ : ∀ i, IsInvBy (pair L₁ L₂ i) (subOf S.toAddSubgroup) :=
      fun i g hg u hu => hS i ⟨g, hg⟩ _ hu
    rcases hirr _ (isInvBy_sup (hJ 0) (hJ 1)) with h | h
    · exact Or.inl (Submodule.toAddSubgroup_injective (subOf_eq_bot h))
    · exact Or.inr (Submodule.toAddSubgroup_injective (subOf_eq_top h))
  have hendF : ∀ f : Module.End F (Additive U),
      (∀ i (g : ↥(pair L₁ L₂ i)), ∀ w, f (φ i g w) = φ i g (f w)) →
        ∃ c : F, ∀ w, f w = c • w := by
    intro f hf
    have hle : L₁ ⊔ L₂ ≤ commutantAut hU (f.restrictScalars (ZMod 2)) :=
      sup_le (fun g hg w => hf 0 ⟨g, hg⟩ w) (fun g hg w => hf 1 ⟨g, hg⟩ w)
    exact (hcommF (f.restrictScalars (ZMod 2))).mp (by
      rintro _ ⟨g, hg, rfl⟩ w
      exact hle hg w)
  obtain ⟨V, _, _, ρ, e, hnt, hfin, hact, hspan⟩ :=
    Offender.tensor_decomposition_core 2 (fun i => ↥(pair L₁ L₂ i)) φ hc hirrF hendF
  refine ⟨F, inferInstance, inferInstance, inferInstance, V, inferInstance, inferInstance, ρ,
    e.toAddEquiv, hnt, hfin, fun i g u => hact i g (Additive.ofMul u), hspan, ?_⟩
  intro g hg
  have hconj : H.map (MulAut.conj (autLin hU g)).toMonoidHom = H := by
    rw [hHdef, Subgroup.map_map]
    conv_rhs => rw [← hg, Subgroup.map_map]
    congr 1
  obtain ⟨σ, hσ⟩ := hnorm (autLin hU g)
    (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hconj)
  refine ⟨σ.toRingEquiv, fun c x => ?_⟩
  show e (autLin hU g (e.symm (c • x))) = σ c • e (autLin hU g (e.symm x))
  rw [map_smul, hσ, map_smul]

end Decomp

end CFSG.Quasithin.SmithD37
