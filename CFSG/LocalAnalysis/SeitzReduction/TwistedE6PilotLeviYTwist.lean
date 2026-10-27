module

public import CFSG.LieType.Chevalley.C2E6D4Twist
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticDescent
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotLeviYFaithful

public section

namespace CFSG.SeitzReduction.TwistedE6Pilot

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.UnbalancedCatalog (semilinCentralizer mem_semilinCentralizer)

section Tau

variable {K : Type} [Field K]

@[expose] noncomputable def d4Tau (σ : K ≃+* K) :
    (Fin 4 ⊕ Fin 4 → K) →ₛₗ[(σ : K →+* K)] (Fin 4 ⊕ Fin 4 → K) where
  toFun v s := σ (v (Equiv.swap (.inl 3) (.inr 3) s))
  map_add' v w := by
    funext s
    simp
  map_smul' c v := by
    funext s
    simp

theorem d4Tau_apply (σ : K ≃+* K) (v : Fin 4 ⊕ Fin 4 → K) (s : Fin 4 ⊕ Fin 4) :
    d4Tau σ v s = σ (v (Equiv.swap (.inl 3) (.inr 3) s)) :=
  rfl

theorem d4Tau_d4Tau {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) (v : Fin 4 ⊕ Fin 4 → K) :
    d4Tau σ (d4Tau σ v) = v := by
  funext s
  rw [d4Tau_apply, d4Tau_apply, Equiv.swap_apply_self, hσσ]

theorem quadPlus_d4Tau (σ : K ≃+* K) (v : Fin 4 ⊕ Fin 4 → K) :
    quadPlus 4 K (d4Tau σ v) = σ (quadPlus 4 K v) := by
  rw [quadPlus_apply, quadPlus_apply, Fin.sum_univ_four, Fin.sum_univ_four]
  simp only [d4Tau_apply, map_add, map_mul]
  have h0 : Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inl 0) = Sum.inl 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have h1 : Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inl 1) = Sum.inl 1 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have h2 : Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inl 2) = Sum.inl 2 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have h0' : Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inr 0) = Sum.inr 0 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have h1' : Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inr 1) = Sum.inr 1 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  have h2' : Equiv.swap (Sum.inl 3 : Fin 4 ⊕ Fin 4) (Sum.inr 3) (Sum.inr 2) = Sum.inr 2 :=
    Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  rw [h0, h1, h2, h0', h1', h2', Equiv.swap_apply_left, Equiv.swap_apply_right,
    mul_comm (σ (v (Sum.inr 3)))]

end Tau

section Frobenius


variable {K : Type} [Field K]

theorem d4Levi_le_adjointGroup : d4Levi K ≤ adjointGroup Tag.E6 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨i, -, c, rfl | rfl⟩
  · exact Subgroup.subset_closure ⟨i, c, Or.inl rfl⟩
  · exact Subgroup.subset_closure ⟨i, c, Or.inr rfl⟩

noncomputable abbrev d4F (σ : K →+* K) : ModGL Tag.E6 K →* ModGL Tag.E6 K :=
  twistHom TwistTag.E6 K σ

theorem d4F_xUnit (σ : K →+* K) (k : Fin 4) (c : K) :
    d4F σ (xUnit Tag.E6 K (jD k) c) = xUnit Tag.E6 K (jD (Equiv.swap 2 3 k)) (σ c) := by
  have h := twistHom_xUnit TwistTag.E6 K σ (jD k) c
  rw [perm_jD] at h
  exact h

theorem d4F_yUnit (σ : K →+* K) (k : Fin 4) (c : K) :
    d4F σ (yUnit Tag.E6 K (jD k) c) = yUnit Tag.E6 K (jD (Equiv.swap 2 3 k)) (σ c) := by
  have h := twistHom_yUnit TwistTag.E6 K σ (jD k) c
  rw [perm_jD] at h
  exact h

theorem d4F_mem_d4Levi (σ : K →+* K) {g : ModGL Tag.E6 K} (hg : g ∈ d4Levi K) :
    d4F σ g ∈ d4Levi K := by
  have hle : d4Levi K ≤ (d4Levi K).comap (d4F σ) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
      rw [SetLike.mem_coe, Subgroup.mem_comap, d4F_xUnit]
      exact xUnit_mem_d4Levi _ _
    · obtain ⟨k, rfl⟩ := exists_jD_of_mem_setD hi
      rw [SetLike.mem_coe, Subgroup.mem_comap, d4F_yUnit]
      exact yUnit_mem_d4Levi _ _
  exact hle hg

@[expose] noncomputable def d4Frob (σ : K →+* K) : d4Levi K →* d4Levi K :=
  ((d4F σ).comp (d4Levi K).subtype).codRestrict (d4Levi K) fun g => d4F_mem_d4Levi σ g.2

theorem coe_d4Frob (σ : K →+* K) (g : d4Levi K) :
    ((d4Frob σ g : d4Levi K) : ModGL Tag.E6 K) = d4F σ g :=
  rfl

end Frobenius

section VectorFrobenius

variable {K : Type} [Field K]

@[expose] noncomputable def d4VecFrob (σ : K →+* K) (v : RootModule Tag.E6 K) :
    RootModule Tag.E6 K :=
  Finsupp.mapRange σ σ.map_zero v

theorem d4VecFrob_apply (σ : K →+* K) (v : RootModule Tag.E6 K) (l : Label Tag.E6) :
    d4VecFrob σ v l = σ (v l) :=
  rfl

theorem d4VecFrob_add (σ : K →+* K) (v w : RootModule Tag.E6 K) :
    d4VecFrob σ (v + w) = d4VecFrob σ v + d4VecFrob σ w :=
  Finsupp.mapRange_add (map_add σ) v w

theorem d4VecFrob_smul (σ : K →+* K) (c : K) (v : RootModule Tag.E6 K) :
    d4VecFrob σ (c • v) = σ c • d4VecFrob σ v := by
  ext l
  simp [d4VecFrob_apply]

theorem d4VecFrob_rootVec (σ : K →+* K) (β : Fin Tag.E6.rank → ℤ) :
    d4VecFrob σ (rootVec Tag.E6 K β) = rootVec Tag.E6 K β := by
  ext l
  rw [d4VecFrob_apply]
  by_cases hβ : IsRoot Tag.E6 β
  · rw [C2E6Std.rootVec_eq_single hβ, Finsupp.single_apply]
    split_ifs <;> simp
  · rw [C2E6Std.rootVec_eq_zero_of_not hβ]
    simp

theorem d4VecFrob_mem (σ : K →+* K) {v : RootModule Tag.E6 K} (hv : v ∈ d4Module K) :
    d4VecFrob σ v ∈ d4Module K := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j, rfl⟩ := hx
    rw [d4VecFrob_rootVec]
    exact d4Vec_mem j
  | zero =>
    rw [show d4VecFrob σ 0 = 0 from Finsupp.mapRange_zero]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    rw [d4VecFrob_add]
    exact add_mem hx hy
  | smul c x _ hx =>
    rw [d4VecFrob_smul]
    exact Submodule.smul_mem _ _ hx

theorem labD_injective' : Function.Injective labD := fun _ _ e =>
  rootD_injective (congrArg Subtype.val (Sum.inr_injective e))

theorem d4Phi_apply_natD {w : RootModule Tag.E6 K} (hw : w ∈ d4Module K) (j : Fin 8) :
    d4Phi K ⟨w, hw⟩ (natD j) = w (labD j) := by
  have key : (LinearMap.proj (natD j) : (Fin 4 ⊕ Fin 4 → K) →ₗ[K] K).comp (d4Phi K).toLinearMap =
      (Finsupp.lapply (labD j)).comp (d4Module K).subtype := by
    refine (d4Basis K).ext fun j' => ?_
    rw [LinearMap.comp_apply, LinearMap.comp_apply, d4Basis_apply, LinearEquiv.coe_coe, d4Phi_vec,
      LinearMap.proj_apply, Submodule.subtype_apply, Finsupp.lapply_apply]
    change (Pi.single (natD j') 1 : Fin 4 ⊕ Fin 4 → K) (natD j) =
      rootVec Tag.E6 K (rootD j') (labD j)
    rw [C2E6Std.rootVec_eq_single (isRoot_rootD j'), Pi.single_apply, Finsupp.single_apply]
    by_cases h : j' = j
    · subst h
      simp
    · rw [ite_eq_right (natD_injective.ne (Ne.symm h)), ite_eq_right (labD_injective'.ne h)]
  exact LinearMap.congr_fun key ⟨w, hw⟩

theorem d4Phi_vecFrob (σ : K →+* K) {v : RootModule Tag.E6 K} (hv : v ∈ d4Module K) :
    d4Phi K ⟨d4VecFrob σ v, d4VecFrob_mem σ hv⟩ = fun s => σ (d4Phi K ⟨v, hv⟩ s) := by
  funext s
  obtain ⟨j, rfl⟩ := exists_natD_eq s
  rw [d4Phi_apply_natD, d4Phi_apply_natD, d4VecFrob_apply]

end VectorFrobenius

section Compat


variable {K : Type} [Field K]

theorem d4Tau_d4Phi (σ : K ≃+* K) {w : RootModule Tag.E6 K} (hw : w ∈ d4Module K) :
    d4Tau σ (d4Phi K ⟨w, hw⟩) =
      d4Phi K ⟨d4Diag K (d4VecFrob (σ : K →+* K) w),
        diagramMap_mem_d4Module _ (d4VecFrob_mem (σ : K →+* K) hw)⟩ := by
  rw [d4Phi_diagramMap (d4VecFrob_mem _ hw), d4Phi_vecFrob _ hw]
  rfl

theorem twistHom_apply_diagramMap_mapRange (σ : K →+* K) (g : ModGL TwistTag.E6.tag K)
    (v : RootModule TwistTag.E6.tag K) :
    ((twistHom TwistTag.E6 K σ g : ModGL TwistTag.E6.tag K) :
        Module.End K (RootModule TwistTag.E6.tag K))
      ((diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))
        (Finsupp.mapRange σ σ.map_zero v)) =
      (diagramMap TwistTag.E6 K : Module.End K (RootModule TwistTag.E6.tag K))
        (Finsupp.mapRange σ σ.map_zero ((g : Module.End K (RootModule TwistTag.E6.tag K)) v)) := by
  rw [coe_twistHom, Module.End.mul_apply, Module.End.mul_apply, ← Module.End.mul_apply
    (((diagramMap TwistTag.E6 K)⁻¹ : ModGL TwistTag.E6.tag K) :
      Module.End K (RootModule TwistTag.E6.tag K)), ← Units.val_mul, inv_mul_cancel,
    Units.val_one, Module.End.one_apply, entrywise_apply_mapRange]

theorem d4Psi_d4Frob_d4Tau (σ : K ≃+* K) (g : d4Levi K) (x : Fin 4 ⊕ Fin 4 → K) :
    d4Psi K (d4Frob (σ : K →+* K) g) (d4Tau σ x) = d4Tau σ (d4Psi K g x) := by
  obtain ⟨⟨v, hv⟩, rfl⟩ := (d4Phi K).surjective x
  rw [d4Tau_d4Phi σ hv, d4Psi_phi, d4Psi_phi, d4Tau_d4Phi σ]
  congr 1
  apply Subtype.ext
  exact twistHom_apply_diagramMap_mapRange (σ : K →+* K) (g : ModGL Tag.E6 K) v

variable [Finite K] [CharP K 2]

theorem d4Frob_eq_self_iff {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) (g : d4Levi K) :
    d4Frob (σ : K →+* K) g = g ↔ d4Psi K g ∈ semilinCentralizer (d4Tau σ) := by
  rw [mem_semilinCentralizer]
  constructor
  · intro h x
    rw [← d4Psi_d4Frob_d4Tau, h]
  · intro h
    apply d4Psi_injective
    refine LinearEquiv.ext fun y => ?_
    have := d4Psi_d4Frob_d4Tau σ g (d4Tau σ y)
    rw [d4Tau_d4Tau hσσ, ← h, d4Tau_d4Tau hσσ] at this
    exact this

omit [Finite K] [CharP K 2] in
theorem mem_twistedFixedGroup_iff_d4Frob (σ : K →+* K) (g : d4Levi K) :
    (g : ModGL Tag.E6 K) ∈ twistedFixedGroup TwistTag.E6 K σ ↔ d4Frob σ g = g := by
  rw [show ((g : ModGL Tag.E6 K) ∈ twistedFixedGroup TwistTag.E6 K σ) ↔
    ((g : ModGL Tag.E6 K) ∈ adjointGroup Tag.E6 K ∧ d4F σ g = g) from Iff.rfl]
  constructor
  · rintro ⟨-, h⟩
    exact Subtype.ext h
  · intro h
    exact ⟨d4Levi_le_adjointGroup g.2, congrArg Subtype.val h⟩

theorem mem_twistedFixedGroup_iff_d4Psi {σ : K ≃+* K} (hσσ : ∀ c, σ (σ c) = c) (g : d4Levi K) :
    (g : ModGL Tag.E6 K) ∈ twistedFixedGroup TwistTag.E6 K (σ : K →+* K) ↔
      d4Psi K g ∈ semilinCentralizer (d4Tau σ) := by
  rw [mem_twistedFixedGroup_iff_d4Frob, d4Frob_eq_self_iff hσσ]

end Compat

end CFSG.SeitzReduction.TwistedE6Pilot
