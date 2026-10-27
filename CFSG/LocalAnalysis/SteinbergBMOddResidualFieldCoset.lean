module

public import CFSG.LieType.Chevalley.LangQuadraticFieldCosetConjugacy
public import CFSG.LocalAnalysis.SteinbergBMOddResidualTools
public import CFSG.LieType.Chevalley.LangRootRankOne
import CFSG.LieType.Chevalley.CoordinateFieldFixedOddComponents
import CFSG.LieType.Chevalley.GraphFixedOddComponents
import CFSG.LocalAnalysis.SteinbergBMEvenG2FixedNoNormalSL2

public noncomputable section

namespace CFSG.LocalAnalysis.SteinbergBM

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

theorem simpleRootSL2_comp_map_injective
    {τ : Tag} {F : Type} [Field F] (hF : ringChar F ≠ 2)
    (δ : F ≃+* F) (i : Fin τ.rank) : Function.Injective ((simpleRootSL2 τ F i).comp
      (Matrix.SpecialLinearGroup.map (fixSubfield δ).subtype)) :=
  (simpleRootSL2_injective hF i).comp (SL2_map_injective _)

theorem simpleRootSL2_comp_map_mem
    {τ : Tag} {F : Type} [Field F] (δ : F ≃+* F)
    (i : Fin τ.rank) {N : Subgroup (ModGL τ F)}
    (hx : ∀ c : fixSubfield δ, xUnit τ F i c ∈ N) (hy : ∀ c : fixSubfield δ, yUnit τ F i c ∈ N)
    (A : SL2 (fixSubfield δ)) :
    (simpleRootSL2 τ F i).comp (Matrix.SpecialLinearGroup.map (fixSubfield δ).subtype) A ∈ N := by
  have hle : closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper (fixSubfield δ)) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower (fixSubfield δ))) ≤
      N.comap ((simpleRootSL2 τ F i).comp
        (Matrix.SpecialLinearGroup.map (fixSubfield δ).subtype)) := by
    rw [closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    · change (simpleRootSL2 τ F i).comp
        (Matrix.SpecialLinearGroup.map (fixSubfield δ).subtype) (uSL c) ∈ N
      rw [MonoidHom.comp_apply, map_uSL, simpleRootSL2_uSL]
      exact hx c
    · change (simpleRootSL2 τ F i).comp
        (Matrix.SpecialLinearGroup.map (fixSubfield δ).subtype) (vSL c) ∈ N
      rw [MonoidHom.comp_apply, map_vSL, simpleRootSL2_vSL]
      exact hy c
  rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower] at hle
  exact hle (mem_top A)

theorem exists_injective_SL2_of_normal_simple_entrywiseFixedGroup
    {τ : Tag} {F : Type}
    [Field F] [Finite F] (hF : ringChar F ≠ 2) (δ : F ≃+* F)
    (S : Subgroup (entrywiseFixedGroup τ δ)) (hSn : S.Normal) (hSs : IsSimpleGroup S)
    (hSnab : ∃ x y : S, x * y ≠ y * x) :
    ∃ φ : SL2 (fixSubfield δ) →* S, Function.Injective φ := by
  obtain ⟨-, hinj, -, hJΓ, -, -, -, hder⟩ := Chevalley_coordinate_field_fixed_structure τ F hF δ
  have hk : ringChar (fixSubfield δ) ≠ 2 := ringChar_fixSubfield_ne_two hF δ
  have : IsSimpleGroup (adjointGroup τ (fixSubfield δ)) :=
    (odd_pinned_Chevalley_p_components τ (fixSubfield δ) hk).1
  have hJs : IsSimpleGroup (fixedFieldImage τ δ) :=
    ((adjointGroup τ (fixSubfield δ)).equivMapOfInjective _ hinj).symm.isSimpleGroup
  set i : Fin τ.rank := ⟨0, τ.rank_pos⟩
  exact exists_injective_of_normal_simple_of_commutator_le hder.le hJΓ hJs _
    (simpleRootSL2_comp_map_injective hF δ i)
    (simpleRootSL2_comp_map_mem δ i (fun c => xUnit_mem_fixedFieldImage i c.2)
      (fun c => yUnit_mem_fixedFieldImage i c.2)) S hSn hSs hSnab

theorem exists_injective_SL2_of_normal_simple_twistedFixedGroup
    {F : Type} [Field F] [Finite F]
    (hF : ringChar F ≠ 2) (δ : F ≃+* F) (S : Subgroup (twistedFixedGroup TwistTag.E6 F δ.toRingHom))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x) :
    ∃ φ : SL2 (fixSubfield δ) →* S, Function.Injective φ := by
  obtain ⟨-, -, hcomm, -⟩ := fixed_root_generated_normal_subgroup TwistTag.E6 F δ
  obtain ⟨hC0s, -, -⟩ := odd_diagram_field_fixed_p_components TwistTag.E6 F hF δ
  set i₃ : Fin TwistTag.E6.tag.rank := ⟨3, by decide⟩
  have hi₃ : TwistTag.E6.perm i₃ = i₃ := by decide
  have hx : ∀ c : fixSubfield δ, xUnit TwistTag.E6.tag F i₃ c ∈
      graphFixedRootGroup TwistTag.E6 F δ.toRingHom := fun c =>
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
      ⟨xUnit_mem_posUnipotent i₃ (c : F), xUnit_mem_adjointGroup i₃ (c : F), by
        change twistHom TwistTag.E6 F δ.toRingHom (xUnit TwistTag.E6.tag F i₃ c) = _
        rw [twistHom_xUnit, hi₃]
        exact congrArg _ c.2⟩
  have hy : ∀ c : fixSubfield δ, yUnit TwistTag.E6.tag F i₃ c ∈
      graphFixedRootGroup TwistTag.E6 F δ.toRingHom := fun c =>
    graphFixedNegUnipotent_le_graphFixedRootGroup _ _ _
      ⟨yUnit_mem_negUnipotent i₃ (c : F), yUnit_mem_adjointGroup i₃ (c : F), by
        change twistHom TwistTag.E6 F δ.toRingHom (yUnit TwistTag.E6.tag F i₃ c) = _
        rw [twistHom_yUnit, hi₃]
        exact congrArg _ c.2⟩
  exact exists_injective_of_normal_simple_of_commutator_le hcomm
    (graphFixedRootGroup_le _ _ _) hC0s _ (simpleRootSL2_comp_map_injective hF δ i₃)
    (simpleRootSL2_comp_map_mem δ i₃ hx hy) S hSn hSs hSnab

theorem odd_quadratic_field_coset_fixed_no_normal_even_SL2
    {τ : Tag}
    (_hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {F : Type} [Field F] [Finite F] {p e : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = (p ^ e) ^ 2) (δ : F ≃+* F)
    (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup τ F)} {g : adjointGroup τ F}
    {a : Fin τ.rank → Fˣ}
    (hαg : ∀ h : adjointGroup τ F, (α h : ModGL τ F) = (g : ModGL τ F) * rootDiagUnit τ a *
      Units.map (entrywiseHom δ.toRingHom) (h : ModGL τ F) * (rootDiagUnit τ a)⁻¹ *
        (g : ModGL τ F)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F)))) (hSn : S.Normal)
    (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (K : Type) [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2 * e) hp (by omega) (by rw [hF, ← pow_mul, mul_comm])
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨hQ1, -⟩ := exceptional_Lang_quadratic_field_coset_conjugacy hp he F hF δ.toRingHom hδ
  obtain ⟨β, hβ, hβα⟩ := hQ1 τ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))).map
      (adjointGroup τ F).subtype = entrywiseFixedGroup τ δ := by
    ext y
    simp only [Subgroup.mem_map, entrywiseFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change Units.map (entrywiseHom δ.toRingHom) (u : ModGL τ F) = u
      rw [← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyδ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL τ F) = y
      rw [hβ]
      exact hyδ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup τ F))) ≃*
      ↥(entrywiseFixedGroup τ δ) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
    exists_normal_simple_of_mulEquiv (e₁.trans e₂) S hSn hSs hSnab
  obtain ⟨φ, hφ⟩ :=
    exists_injective_SL2_of_normal_simple_entrywiseFixedGroup hF2 δ S' hS'n hS's hS'nab
  exact false_of_injective_SL2_of_mulEquiv (ringChar_fixSubfield_ne_two hF2 δ)
    (eS'.symm.toMonoidHom.comp φ) (eS'.symm.injective.comp hφ) eS

theorem odd_E6_graph_field_coset_fixed_no_normal_even_SL2
    {F : Type} [Field F] [Finite F]
    {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 1 ≤ e) (hF : Nat.card F = (p ^ e) ^ 2)
    (δ : F ≃+* F) (hδ : ∀ c, δ c = c ^ (p ^ e)) {α : MulAut (adjointGroup TwistTag.E6.tag F)}
    {g : adjointGroup TwistTag.E6.tag F} {a : Fin TwistTag.E6.tag.rank → Fˣ}
    (hαg : ∀ h : adjointGroup TwistTag.E6.tag F, (α h : ModGL TwistTag.E6.tag F) =
      (g : ModGL TwistTag.E6.tag F) * rootDiagUnit TwistTag.E6.tag a * diagramMap TwistTag.E6 F *
        Units.map (entrywiseHom δ.toRingHom) (h : ModGL TwistTag.E6.tag F) *
          (diagramMap TwistTag.E6 F)⁻¹ * (rootDiagUnit TwistTag.E6.tag a)⁻¹ *
            (g : ModGL TwistTag.E6.tag F)⁻¹)
    (hα : α ^ 2 = 1)
    (S : Subgroup (α.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))))
    (hSn : S.Normal) (hSs : IsSimpleGroup S) (hSnab : ∃ x y : S, x * y ≠ y * x)
    (K : Type) [Field K] [CharP K 2] (eS : S ≃* Matrix.SpecialLinearGroup (Fin 2) K) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : CharP F p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    (k := 2 * e) hp (by omega) (by rw [hF, ← pow_mul, mul_comm])
  have hF2 : ringChar F ≠ 2 := by rw [ringChar.eq F p]; exact hp2
  obtain ⟨-, β, hβ, hβα⟩ :=
    exceptional_Lang_quadratic_field_coset_conjugacy hp he F hF δ.toRingHom hδ
  obtain ⟨-, hconj⟩ := hβα g a
  obtain ⟨ψ, -, -, ⟨e₁, -⟩, -⟩ := hconj α hαg (by rw [← sq]; exact hα)
  have hβfix : (β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))).map
      (adjointGroup TwistTag.E6.tag F).subtype = twistedFixedGroup TwistTag.E6 F δ.toRingHom := by
    ext y
    simp only [Subgroup.mem_map, twistedFixedGroup, Subgroup.mem_inf]
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u.2, ?_⟩
      change twistHom TwistTag.E6 F δ.toRingHom (u : ModGL TwistTag.E6.tag F) = u
      rw [twistHom_apply, ← hβ u]
      exact congrArg Subtype.val hu
    · rintro ⟨hyG, hyσ⟩
      refine ⟨⟨y, hyG⟩, Subtype.ext ?_, rfl⟩
      change (β ⟨y, hyG⟩ : ModGL TwistTag.E6.tag F) = y
      rw [hβ]
      change twistHom TwistTag.E6 F δ.toRingHom y = y at hyσ
      rw [twistHom_apply] at hyσ
      exact hyσ
  let e₂ : ↥(β.toMonoidHom.eqLocus (MonoidHom.id (adjointGroup TwistTag.E6.tag F))) ≃*
      ↥(twistedFixedGroup TwistTag.E6 F δ.toRingHom) :=
    (Subgroup.equivMapOfInjective _ _ Subtype.val_injective).trans (MulEquiv.subgroupCongr hβfix)
  obtain ⟨S', hS'n, hS's, hS'nab, ⟨eS'⟩⟩ :=
    exists_normal_simple_of_mulEquiv (e₁.trans e₂) S hSn hSs hSnab
  obtain ⟨φ, hφ⟩ :=
    exists_injective_SL2_of_normal_simple_twistedFixedGroup hF2 δ S' hS'n hS's hS'nab
  exact false_of_injective_SL2_of_mulEquiv (ringChar_fixSubfield_ne_two hF2 δ)
    (eS'.symm.toMonoidHom.comp φ) (eS'.symm.injective.comp hφ) eS

end CFSG.LocalAnalysis.SteinbergBM
