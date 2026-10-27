module

public import CFSG.LocalAnalysis.StandardType.GGMaxRankWeyl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem tne_coxeter_reindex_refl {ι : Type} (N : CoxeterMatrix ι) :
    N.reindex (Equiv.refl ι) = N := by
  apply CoxeterMatrix.ext
  funext i j
  simp only [CoxeterMatrix.reindex_apply, Equiv.refl_symm, Equiv.refl_apply]

private theorem tne_ggIsWeylMatrix_E8 : CFSG.StandardType.GGIsWeylMatrix CoxeterMatrix.E₈ :=
  Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 8), (tne_coxeter_reindex_refl _).symm⟩)))

private theorem tne_finite_E8 : Finite CoxeterMatrix.E₈.Group :=
  Finite.of_equiv _ CFSG.StandardType.ggE8Equiv.toEquiv.symm

private theorem tne_sigma_sq {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (σ : Fin 8 → V ≃ₗ[ZMod p] V) (c : Fin 8 → V)
    (β : Fin 8 → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (hβc : ∀ i, β i (c i) = 2) (i : Fin 8) :
    σ i * σ i = 1 := by
  ext v
  change σ i (σ i v) = v
  have hβσ : β i (σ i v) = β i v - β i v * β i (c i) := by
    rw [hσ i v, map_sub, map_smul, smul_eq_mul]
  rw [hσ i (σ i v), hβσ, hβc i, hσ i v]
  have hs : (β i v - β i v * 2 : ZMod p) = -(β i v) := by ring
  rw [hs, neg_smul, sub_neg_eq_add]
  exact sub_add_cancel _ _

private theorem tne_sigma_sub_range {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (σ : Fin 8 → V ≃ₗ[ZMod p] V) (c : Fin 8 → V)
    (β : Fin 8 → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (i : Fin 8) :
    LinearMap.range ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) ≤
      Submodule.span (ZMod p) ({c i} : Set V) := by
  rintro x ⟨v, rfl⟩
  rw [LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, hσ i v]
  have h : v - β i v • c i - v = -(β i v) • c i := by module
  rw [h]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton (c i)))

private theorem tne_isRefl {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (σ : Fin 8 → V ≃ₗ[ZMod p] V) (c : Fin 8 → V)
    (β : Fin 8 → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (hσ2 : ∀ i, σ i * σ i = 1)
    (hσne : ∀ i, σ i ≠ 1) (i : Fin 8) :
    CFSG.StandardType.ZS.IsRefl p (σ i) := by
  refine ⟨hσ2 i, ?_⟩
  have hci : c i ≠ 0 := by
    intro hc
    apply hσne i
    ext v
    simp [hσ i v, hc]
  have hsub := tne_sigma_sub_range σ c β hσ i
  have hrange_ne : LinearMap.range ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) ≠ ⊥ := by
    intro hbot
    apply hσne i
    ext v
    have hmem := LinearMap.mem_range_self ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) v
    rw [hbot] at hmem
    have hv : σ i v - v = 0 := by simpa using hmem
    exact sub_eq_zero.mp hv
  have hrange : LinearMap.range ((σ i : V →ₗ[ZMod p] V) - LinearMap.id) =
      Submodule.span (ZMod p) ({c i} : Set V) := by
    apply le_antisymm hsub
    rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨w, hwS, hw0⟩ := (Submodule.ne_bot_iff _).mp hrange_ne
    have hwspan : w ∈ Submodule.span (ZMod p) ({c i} : Set V) := hsub hwS
    rw [Submodule.mem_span_singleton] at hwspan
    obtain ⟨a, ha⟩ := hwspan
    have ha0 : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_smul] at ha
      exact hw0 ha.symm
    have hcw : c i = a⁻¹ • w := by
      rw [← ha, smul_smul, inv_mul_cancel₀ ha0, one_smul]
    rw [hcw]
    exact Submodule.smul_mem _ _ hwS
  rw [hrange]
  exact finrank_span_singleton hci

theorem linWeyl_E8_of_simple_system {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (R : Subgroup (V ≃ₗ[ZMod p] V)) (σ : Fin 8 → V ≃ₗ[ZMod p] V)
    (hσR : ∀ i, σ i ∈ R) (c : Fin 8 → V) (β : Fin 8 → Module.Dual (ZMod p) V)
    (hσ : ∀ i v, σ i v = v - β i v • c i) (hβc : ∀ i, β i (c i) = 2)
    (hrel : ∀ i j, i ≠ j → (σ i * σ j) ^ (CoxeterMatrix.E₈.M i j) = 1)
    (hgen : R ≤ Subgroup.closure (Set.range σ)) (hcard : Nat.card CoxeterMatrix.E₈.Group ≤ Nat.card R) :
    CFSG.StandardType.ZS.LinWeyl p R := by
  have hσ2 : ∀ i, σ i * σ i = 1 := fun i => tne_sigma_sq σ c β hσ hβc i
  have hfam : CoxeterMatrix.IsLiftable CoxeterMatrix.E₈ σ := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [CoxeterMatrix.diagonal CoxeterMatrix.E₈ i, pow_one]
      exact hσ2 i
    · exact hrel i j hij
  let f₀ : CoxeterMatrix.E₈.Group →* (V ≃ₗ[ZMod p] V) :=
    CoxeterMatrix.E₈.toCoxeterSystem.lift ⟨σ, hfam⟩
  have hf₀ : ∀ i, f₀ (CoxeterMatrix.E₈.toCoxeterSystem.simple i) = σ i := by
    intro i
    exact CoxeterMatrix.E₈.toCoxeterSystem.lift_apply_simple hfam i
  have hclosure_le : Subgroup.closure (Set.range σ) ≤ R := by
    refine (Subgroup.closure_le R).mpr ?_
    rintro _ ⟨i, rfl⟩
    exact hσR i
  have hR_eq : R = Subgroup.closure (Set.range σ) := le_antisymm hgen hclosure_le
  have hgen_top : Subgroup.closure (Set.range CoxeterMatrix.E₈.toCoxeterSystem.simple) = ⊤ :=
    CoxeterMatrix.E₈.toCoxeterSystem.subgroup_closure_range_simple
  have hrange : f₀.range = Subgroup.closure (Set.range σ) := by
    calc f₀.range = (⊤ : Subgroup CoxeterMatrix.E₈.Group).map f₀ :=
          (Subgroup.map_top f₀).symm
      _ = (Subgroup.closure (Set.range CoxeterMatrix.E₈.toCoxeterSystem.simple)).map f₀ := by
          rw [← hgen_top]
      _ = Subgroup.closure (f₀ '' Set.range CoxeterMatrix.E₈.toCoxeterSystem.simple) :=
          MonoidHom.map_closure f₀ _
      _ = Subgroup.closure (Set.range (f₀ ∘ CoxeterMatrix.E₈.toCoxeterSystem.simple)) := by
          rw [← Set.range_comp]
      _ = Subgroup.closure (Set.range σ) := by
          apply congrArg Subgroup.closure
          apply congrArg Set.range
          funext i
          exact hf₀ i
  have hmem : ∀ g : CoxeterMatrix.E₈.Group, f₀ g ∈ R := by
    intro g
    rw [hR_eq, ← hrange]
    exact ⟨g, rfl⟩
  let f₁ : CoxeterMatrix.E₈.Group →* R := MonoidHom.codRestrict f₀ R hmem
  have hf₁ : ∀ i, f₁ (CoxeterMatrix.E₈.toCoxeterSystem.simple i) = ⟨σ i, hσR i⟩ := by
    intro i
    apply Subtype.ext
    change f₀ (CoxeterMatrix.E₈.toCoxeterSystem.simple i) = σ i
    exact hf₀ i
  have hsurj : Function.Surjective f₁ := by
    intro r
    have hr : (r : V ≃ₗ[ZMod p] V) ∈ Subgroup.closure (Set.range σ) := by
      rw [← hR_eq]
      exact r.2
    rw [← hrange] at hr
    obtain ⟨g, hg⟩ := hr
    refine ⟨g, ?_⟩
    apply Subtype.ext
    change f₀ g = (r : V ≃ₗ[ZMod p] V)
    exact hg
  haveI : Finite CoxeterMatrix.E₈.Group := tne_finite_E8
  haveI : Finite R := Finite.of_surjective f₁ hsurj
  haveI : Fintype CoxeterMatrix.E₈.Group := Fintype.ofFinite _
  haveI : Fintype R := Fintype.ofFinite _
  have hcard_eq : Fintype.card CoxeterMatrix.E₈.Group = Fintype.card R := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact le_antisymm hcard (Nat.card_le_card_of_surjective f₁ hsurj)
  have hbij : Function.Bijective f₁ :=
    (Fintype.bijective_iff_surjective_and_card f₁).mpr ⟨hsurj, hcard_eq⟩
  let f : CoxeterMatrix.E₈.Group ≃* R := MulEquiv.ofBijective f₁ hbij
  have hσne : ∀ i, σ i ≠ 1 := by
    intro i hσi
    have hsimple_ne : CoxeterMatrix.E₈.toCoxeterSystem.simple i ≠ 1 := by
      intro h
      have h1 := CoxeterMatrix.E₈.toCoxeterSystem.length_simple i
      rw [h] at h1
      simp at h1
    have hf₁i : f₁ (CoxeterMatrix.E₈.toCoxeterSystem.simple i) = 1 := by
      apply Subtype.ext
      change f₀ (CoxeterMatrix.E₈.toCoxeterSystem.simple i) = 1
      rw [hf₀ i, hσi]
    have heq : f₁ (CoxeterMatrix.E₈.toCoxeterSystem.simple i) = f₁ 1 := by
      rw [hf₁i, map_one]
    exact hsimple_ne (hbij.1 heq)
  refine ⟨Fin 8, CoxeterMatrix.E₈, tne_ggIsWeylMatrix_E8, f, ?_⟩
  intro i
  have hmi : f (CoxeterMatrix.E₈.simple i) = ⟨σ i, hσR i⟩ := by
    apply Subtype.ext
    change f₀ (CoxeterMatrix.E₈.simple i) = σ i
    rw [show CoxeterMatrix.E₈.simple i = CoxeterMatrix.E₈.toCoxeterSystem.simple i from by
      rw [CoxeterMatrix.toCoxeterSystem_simple]]
    exact hf₀ i
  have hfi : (f (CoxeterMatrix.E₈.simple i) : V ≃ₗ[ZMod p] V) = σ i :=
    congrArg Subtype.val hmi
  rw [hfi]
  exact tne_isRefl σ c β hσ hσ2 hσne i

end CFSG.TwoNodeSmall
