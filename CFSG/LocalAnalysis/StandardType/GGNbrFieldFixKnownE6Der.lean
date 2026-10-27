module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Kernel
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixKnownE6Restrict
public import CFSG.LieType.Simplicity.Exceptional
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFieldVacOther

public section

namespace CFSG.StandardType.E6FieldFix

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.RecipeExcLang
  CFSG.LieType.SeitzGeneration.ExcWideThree

open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [Finite K]

theorem ggFixSub_entrywiseAdjointAut_E6 (σ : K ≃+* K) :
    ggFixSub (entrywiseAdjointAut Tag.E6 σ) =
      (entrywiseFixedGroup Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) := by
  ext x
  rw [mem_ggFixSub, Subgroup.mem_subgroupOf, mem_entrywiseFixedGroup]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    have := congrArg Subtype.val h
    rwa [coe_entrywiseAdjointAut] at this
  · rintro ⟨-, h⟩
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact h

theorem fixedFieldImage_le_adjointGroup_E6 (σ : K ≃+* K) :
    fixedFieldImage Tag.E6 σ ≤ adjointGroup Tag.E6 K := fun _ hj =>
  (mem_entrywiseFixedGroup.1
    ((Chevalley_coordinate_field_fixed_normal_subgroup Tag.E6 K σ).2.2.2.1 hj)).1

theorem ggFixDer_entrywiseAdjointAut_E6 (σ : K ≃+* K) :
    ggFixDer (entrywiseAdjointAut Tag.E6 σ) =
      (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) := by
  obtain ⟨-, -, -, -, -, -, hab⟩ :=
    Chevalley_coordinate_field_fixed_normal_subgroup Tag.E6 K σ
  have hJC := fixedFieldImage_le_adjointGroup_E6 σ
  have hJs : (fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K) ≤
      ggFixSub (entrywiseAdjointAut Tag.E6 σ) := fun x hx =>
    mem_ggFixSub_of_mem_map x (Subgroup.mem_subgroupOf.1 hx)
  refine le_antisymm ?_ ?_
  ·
    refine (Subgroup.commutator_le).2 fun g₁ h₁ g₂ h₂ => ?_
    rw [ggFixSub_entrywiseAdjointAut_E6, Subgroup.mem_subgroupOf] at h₁ h₂
    set a : ↥(entrywiseFixedGroup Tag.E6 σ) := ⟨(g₁ : ModGL Tag.E6 K), h₁⟩
    set b : ↥(entrywiseFixedGroup Tag.E6 σ) := ⟨(g₂ : ModGL Tag.E6 K), h₂⟩
    have hq : (QuotientGroup.mk' ((fixedFieldImage Tag.E6 σ).subgroupOf
        (entrywiseFixedGroup Tag.E6 σ))) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab _ _
    have hmem := Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff ⁅a, b⁆).1 hq)
    rw [Subgroup.mem_subgroupOf]
    simpa [a, b, commutatorElement_def] using hmem
  ·
    haveI : Group.IsPerfect ↥(adjointGroup Tag.E6 ↥(fixSubfield σ)) :=
      (CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e6 ↥(fixSubfield σ)).1
    let e : adjointGroup Tag.E6 ↥(fixSubfield σ) ≃*
        ↥((fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K)) :=
      (fixedFieldImageEquiv (τ := Tag.E6) σ).trans (Subgroup.subgroupOfEquivOfLe hJC).symm
    haveI : Group.IsPerfect ↥((fixedFieldImage Tag.E6 σ).subgroupOf (adjointGroup Tag.E6 K)) :=
      Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    rw [← Subgroup.commutator_eq_self (H := (fixedFieldImage Tag.E6 σ).subgroupOf
      (adjointGroup Tag.E6 K))]
    exact Subgroup.commutator_mono hJs hJs

theorem mem_ggFixDer_entrywiseAdjointAut_E6 (σ : K ≃+* K) (x : adjointGroup Tag.E6 K) :
    x ∈ ggFixDer (entrywiseAdjointAut Tag.E6 σ) ↔
      (x : ModGL Tag.E6 K) ∈ fixedFieldImage Tag.E6 σ := by
  rw [ggFixDer_entrywiseAdjointAut_E6, Subgroup.mem_subgroupOf]

@[expose] noncomputable def fixE6DerEquiv (σ : K ≃+* K) :
    adjointGroup Tag.E6 (fixSubfield σ) ≃* ↥(ggFixDer (entrywiseAdjointAut Tag.E6 σ)) :=
  ((fixedFieldImageEquiv (τ := Tag.E6) σ).trans
      (Subgroup.subgroupOfEquivOfLe (fixedFieldImage_le_adjointGroup_E6 σ)).symm).trans
    (MulEquiv.subgroupCongr (ggFixDer_entrywiseAdjointAut_E6 σ).symm)

theorem coe_fixE6DerEquiv (σ : K ≃+* K) (y : adjointGroup Tag.E6 (fixSubfield σ)) :
    ((((fixE6DerEquiv σ y : ↥(ggFixDer (entrywiseAdjointAut Tag.E6 σ))) :
      adjointGroup Tag.E6 K) : ModGL Tag.E6 K)) =
        baseChangeGL (fixSubfield σ).subtype (y : ModGL Tag.E6 (fixSubfield σ)) :=
  rfl

theorem exists_inndiagConj_restrict_der {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {σ : K ≃+* K} (hσ1 : σ ≠ 1) (w : inndiagGroup Tag.E6 K)
    (hc : inndiagConj Tag.E6 K w * entrywiseAdjointAut Tag.E6 σ =
      entrywiseAdjointAut Tag.E6 σ * inndiagConj Tag.E6 K w) :
    ∃ w₀ : inndiagGroup Tag.E6 (fixSubfield σ), ∀ y : adjointGroup Tag.E6 (fixSubfield σ),
      inndiagConj Tag.E6 K w
          ((fixE6DerEquiv σ y : ↥(ggFixDer (entrywiseAdjointAut Tag.E6 σ))) :
            adjointGroup Tag.E6 K) =
        ((fixE6DerEquiv σ (inndiagConj Tag.E6 (fixSubfield σ) w₀ y) :
          ↥(ggFixDer (entrywiseAdjointAut Tag.E6 σ))) : adjointGroup Tag.E6 K) := by
  have hK4 : 4 ≤ Nat.card K :=
    four_le_card_of_ne_one (ℓ := 2) (f := n) (by norm_num) hn hK hσ1
  have hfix : Units.map (entrywiseHom σ.toRingHom) (w : ModGL Tag.E6 K) =
      (w : ModGL Tag.E6 K) :=
    entrywise_inndiag_eq_of_commute (τ := Tag.E6) hK4 σ w hc
  have hk : Nat.card (fixSubfield σ) = 2 ^ (n / orderOf σ) :=
    (CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield (p := 2) (f := n)
      (by norm_num) hn hK σ).2
  obtain ⟨w₀m, hw₀m, hbase⟩ :=
    exists_inndiagGroup_of_fixed (τ := Tag.E6) (n := n) (e := n / orderOf σ) hK σ hk
      (w := (w : ModGL Tag.E6 K)) w.2 hfix
  refine ⟨⟨w₀m, hw₀m⟩, fun y => ?_⟩
  apply Subtype.ext
  simp only [coe_inndiagConj, coe_fixE6DerEquiv, map_mul, map_inv, hbase]

theorem eq_one_of_inndiagConj_fixes_der {σ : K ≃+* K} (hk : 2 < Nat.card (fixSubfield σ))
    (w : inndiagGroup Tag.E6 K)
    (hfix : ∀ x : ↥(ggFixDer (entrywiseAdjointAut Tag.E6 σ)),
      inndiagConj Tag.E6 K w (x : adjointGroup Tag.E6 K) = x) :
    inndiagConj Tag.E6 K w = 1 := by
  refine eq_one_of_mem_e6Inndiag_of_fix_subfield (fixSubfield σ) hk
    (inndiagConj_mem_e6Inndiag w) fun x hx => ?_
  exact hfix ⟨x, (mem_ggFixDer_entrywiseAdjointAut_E6 σ x).2 hx⟩

end CFSG.StandardType.E6FieldFix

end
