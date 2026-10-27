module

public import CFSG.Monster.B.E6.StdF4DegreeBound
public import CFSG.LieType.Chevalley.GraphFixedF4Canonical
public import CFSG.Monster.B.E6.StandardSimple

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4Radical

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.Monster.B.E6.StdF4

theorem groupJ_eq_canonical :
    (groupJ : Subgroup (ModGL TwistTag.E6.tag K)) =
      (twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))).map
        (baseChangeGL (algebraMap (ZMod 2) K)) := by
  obtain ⟨⟨η, hη, -, hJC, hfix, -⟩, -⟩ := (even_E6_twisted_E6_canonical_graph_fixed_subgroup 1
    le_rfl (ZMod 2) K (by simp) CFSG.Monster.B.E6.card_K barHom CFSG.Monster.B.E6.barHom_eq_pow).2
  have hF : ∀ g ∈ stdGroup, diagE6GL * betaGL g * diagE6GL⁻¹ = g := fun g hg =>
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K barHom).1
      (graphFixedRootGroup_le _ _ _ hg)).2
  ext g
  constructor
  · intro hg
    have hgC : g ∈ graphFixedRootGroup TwistTag.E6 K barHom := hg.1
    refine (hfix ⟨g, hgC⟩).1 (Subtype.ext ?_)
    rw [hη]
    have := hF g hg.1
    rw [hg.2] at this
    exact this
  · intro hg
    have hgC := hJC hg
    have h1 := congrArg Subtype.val ((hfix ⟨g, hgC⟩).2 hg)
    rw [hη] at h1
    refine ⟨hgC, ?_⟩
    have h2 := hF g hgC
    have h3 : diagE6GL * betaGL g * diagE6GL⁻¹ = diagE6GL * g * diagE6GL⁻¹ := h2.trans h1.symm
    simpa using h3

theorem isSimpleGroup_groupJ :
    IsSimpleGroup groupJ := by
  obtain ⟨⟨η, -, -, -, -, hsimple, -⟩, -⟩ := (even_E6_twisted_E6_canonical_graph_fixed_subgroup 1
    le_rfl (ZMod 2) K (by simp) CFSG.Monster.B.E6.card_K barHom CFSG.Monster.B.E6.barHom_eq_pow).2
  have e : groupJ ≃* (twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))).map
      (baseChangeGL (algebraMap (ZMod 2) K)) := MulEquiv.subgroupCongr groupJ_eq_canonical
  exact @MulEquiv.isSimpleGroup _ _ _ _ hsimple e

theorem nonempty_groupJ_mulEquiv_F4 :
    Nonempty (groupJ ≃* adjointGroup Tag.F4 (ZMod 2)) := by
  obtain ⟨-, e, -⟩ := (even_E6_twisted_E6_canonical_graph_fixed_subgroup 1
    le_rfl (ZMod 2) K (by simp) CFSG.Monster.B.E6.card_K barHom CFSG.Monster.B.E6.barHom_eq_pow).2
  have e₁ : groupJ ≃* (twistedFixedGroup TwistTag.E6 (ZMod 2) (RingHom.id (ZMod 2))).map
      (baseChangeGL (algebraMap (ZMod 2) K)) := MulEquiv.subgroupCongr groupJ_eq_canonical
  exact ⟨e₁.trans e⟩

theorem tJ_ne_one :
    tJ ≠ 1 := by
  intro h
  apply rootInvM_ne_one
  have := congrArg (fun x : groupJ => (x : ModGL Tag.E6 K)) h
  rwa [OneMemClass.coe_one] at this

theorem rho_tJ_ne_one
    {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ groupJ V}
    (hρ : ρ ≠ Representation.trivial ℂ groupJ V) : ρ tJ ≠ 1 := by
  have := isSimpleGroup_groupJ
  intro ht
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ρ.ker with h | h
  · exact tJ_ne_one ((MonoidHom.ker_eq_bot_iff ρ).1 h (ht.trans (map_one ρ).symm))
  · refine hρ (MonoidHom.ext fun g => ?_)
    have hg : g ∈ ρ.ker := h ▸ Subgroup.mem_top g
    rw [MonoidHom.mem_ker] at hg
    rw [hg]
    rfl

theorem le_finrank_of_ne_trivial
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {ρ : Representation ℂ groupJ V} (hρ : ρ ≠ Representation.trivial ℂ groupJ V) :
    448 ≤ Module.finrank ℂ V :=
  le_finrank_of_rho_tJ_ne_one ρ (rho_tJ_ne_one hρ)

section Index

variable {X : Type*} [MulAction groupJ X]

@[expose] def permRep : Representation ℂ groupJ (X → ℂ) where
  toFun g :=
    { toFun f := fun x => f (g⁻¹ • x)
      map_add' f f' := rfl
      map_smul' c f := rfl }
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [mul_smul]

theorem permRep_apply (g : groupJ) (f : X → ℂ) (x : X) : permRep g f x = f (g⁻¹ • x) := rfl

variable [Fintype X]

@[expose] def aug : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ x, f x
  map_add' f f' := Finset.sum_add_distrib
  map_smul' c f := by simp [Finset.mul_sum]

theorem aug_permRep (g : groupJ) (f : X → ℂ) : aug (permRep g f) = aug f := by
  simp only [aug, LinearMap.coe_mk, AddHom.coe_mk, permRep_apply]
  exact Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun x => rfl

abbrev augSpace : Submodule ℂ (X → ℂ) := LinearMap.ker (aug (X := X))

theorem permRep_mem_augSpace (g : groupJ) {f : X → ℂ} (hf : f ∈ augSpace (X := X)) :
    permRep g f ∈ augSpace (X := X) := by
  rw [LinearMap.mem_ker] at hf ⊢
  rw [aug_permRep, hf]

@[expose] def augRep : Representation ℂ groupJ (augSpace (X := X)) where
  toFun g := (permRep g).restrict fun f hf => permRep_mem_augSpace g hf
  map_one' := by
    ext f x
    simp
  map_mul' g h := by
    ext f x
    simp [permRep_apply]

omit [MulAction groupJ X] in
theorem finrank_augSpace [Nonempty X] :
    Module.finrank ℂ (augSpace (X := X)) = Fintype.card X - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (aug (X := X))
  have hr : LinearMap.range (aug (X := X)) = ⊤ := by
    refine LinearMap.range_eq_top.2 fun c => ?_
    obtain ⟨x⟩ := ‹Nonempty X›
    classical
    refine ⟨Pi.single x c, ?_⟩
    simp [aug, Finset.sum_pi_single']
  rw [hr, finrank_top, Module.finrank_self, Module.finrank_fintype_fun_eq_card] at h
  change Module.finrank ℂ (LinearMap.ker (aug (X := X))) = _
  omega

theorem augRep_ne_trivial {g : groupJ} {x₀ : X} (hg : g • x₀ ≠ x₀) :
    augRep (X := X) ≠ Representation.trivial ℂ groupJ (augSpace (X := X)) := by
  classical
  intro h
  let f : X → ℂ := Pi.single x₀ 1 - Pi.single (g • x₀) 1
  have hf : f ∈ augSpace (X := X) := by
    rw [LinearMap.mem_ker]
    simp [f, aug, Finset.sum_sub_distrib, Finset.sum_pi_single']
  have e := congrArg (fun φ => ((φ g ⟨f, hf⟩ : augSpace (X := X)) : X → ℂ) (g • x₀)) h
  simp only [Representation.trivial_apply] at e
  change permRep g f (g • x₀) = f (g • x₀) at e
  rw [permRep_apply, inv_smul_smul] at e
  simp only [f, Pi.sub_apply, Pi.single_eq_same, Pi.single_apply, hg, hg.symm, ite_false] at e
  norm_num at e

end Index

theorem finite_groupJ :
    Finite groupJ := by
  have hfin : Finite stdGroup := CFSG.Monster.B.E6.standard_twisted_e6_group_simple.1
  exact Finite.of_injective (Subgroup.inclusion groupJ_le_stdGroup)
    (Subgroup.inclusion_injective _)

theorem le_index_of_ne_top
    {H : Subgroup groupJ} (hH : H ≠ ⊤) : 449 ≤ H.index := by
  classical
  have := finite_groupJ
  have : Fintype (groupJ ⧸ H) := Fintype.ofFinite _
  obtain ⟨g, hg⟩ : ∃ g : groupJ, g ∉ H := by
    by_contra h
    exact hH (eq_top_iff.2 fun g _ => not_not.1 fun hg => h ⟨g, hg⟩)
  have hmove : g • (QuotientGroup.mk 1 : groupJ ⧸ H) ≠ QuotientGroup.mk 1 := by
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, Ne, QuotientGroup.eq, mul_one]
    exact fun h => hg (by simpa using inv_mem h)
  have hbound := le_finrank_of_ne_trivial (augRep_ne_trivial (X := groupJ ⧸ H) hmove)
  rw [finrank_augSpace] at hbound
  rw [Subgroup.index_eq_card, Nat.card_eq_fintype_card]
  omega

theorem standard_F4_complex_degree_and_small_index_bound :
    (∀ (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
        (ρ : Representation ℂ groupJ V), ρ ≠ Representation.trivial ℂ groupJ V →
          448 ≤ Module.finrank ℂ V) ∧
      ∀ H : Subgroup groupJ, H ≠ ⊤ → 449 ≤ H.index :=
  ⟨fun _ _ _ _ _ hρ => le_finrank_of_ne_trivial hρ, fun _ hH => le_index_of_ne_top hH⟩

end CFSG.Monster.B.E6.StdF4Radical
