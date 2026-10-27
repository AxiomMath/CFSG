module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Assembly
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.Unipotent
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.AdjointRep
public import CFSG.LieType.Chevalley.CoordinateFieldFixedSubgroup
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge
open scoped Pointwise

variable {τ : Tag} {K : Type} [Field K]

theorem isSimpleGroup_adjointGroup_of_quasisimple
    {k : Type} [Field k] [Finite k]
    (hq : IsQuasisimple ↥(adjointGroup τ k)) : IsSimpleGroup ↥(adjointGroup τ k) := by
  have hZ : Subgroup.center ↥(adjointGroup τ k) = ⊥ := center_adjointGroup_eq_bot
  exact CFSG.LieType.Simplicity.isSimpleGroup_of_mulEquiv hq
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm

theorem fixedFieldImage_le_adjointGroup
    (σ : K ≃+* K) :
    fixedFieldImage τ σ ≤ adjointGroup τ K :=
  fixedFieldImage_le.trans (inf_le_left : entrywiseFixedGroup τ σ ≤ adjointGroup τ K)

@[expose] noncomputable def subfieldEquiv
    (σ : K ≃+* K) :
    ↥(adjointGroup τ (fixSubfield σ)) ≃*
      ↥((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) :=
  ((adjointGroup τ (fixSubfield σ)).equivMapOfInjective (baseChangeGL (fixSubfield σ).subtype)
      (baseChangeGL_injective _)).trans
    (Subgroup.subgroupOfEquivOfLe (fixedFieldImage_le_adjointGroup σ)).symm

@[expose] noncomputable def subfieldUnipotent
    (τ : Tag) (σ : K ≃+* K) :
    Subgroup ↥(adjointGroup τ K) :=
  ((posUnipotent τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype)).subgroupOf
    (adjointGroup τ K)

theorem posUnipotent_le_adjointGroup
    (k : Type) [Field k] : posUnipotent τ k ≤ adjointGroup τ k :=
  le_sup_right.trans ((triangular_borel_structure.{0, 0} τ k).2.2.2.2.2.2.2.2.2.2.2 k).1

theorem map_posUnipotent_le_fixedFieldImage
    (σ : K ≃+* K) :
    (posUnipotent τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype) ≤
      fixedFieldImage τ σ :=
  Subgroup.map_mono (posUnipotent_le_adjointGroup _)

theorem card_subfieldUnipotent
    [Finite K] (σ : K ≃+* K) :
    Nat.card (subfieldUnipotent τ σ) =
      Nat.card (fixSubfield σ) ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard := by
  have hle : (posUnipotent τ (fixSubfield σ)).map (baseChangeGL (fixSubfield σ).subtype) ≤
      adjointGroup τ K :=
    (map_posUnipotent_le_fixedFieldImage σ).trans (fixedFieldImage_le_adjointGroup σ)
  rw [subfieldUnipotent, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Subgroup.card_map_of_injective (baseChangeGL_injective _), card_posUnipotent]

theorem eq_bot_of_isPGroup_of_normalized_subfield
    [Finite K] (σ : K ≃+* K) (r : ℕ) [Fact r.Prime]
    [CharP K r] (E : Subgroup ↥(adjointGroup τ K)) (hEr : IsPGroup r E)
    (hEn : ∀ j ∈ (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K), ∀ e ∈ E,
      j * e * j⁻¹ ∈ E) : E = ⊥ := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  have hJx : ∀ i : Fin τ.rank, xUnit τ K i 1 ∈ fixedFieldImage τ σ := fun i =>
    xUnit_mem_fixedFieldImage i (map_one σ)
  have hJn : canonicalRep (coxeterSystem τ) K w₀ ∈ fixedFieldImage τ σ :=
    canonicalRep_mem_fixedFieldImage w₀
  have hWr : IsPGroup r (E.map (adjointGroup τ K).subtype) := hEr.map _
  have hWC : E.map (adjointGroup τ K).subtype ≤ adjointGroup τ K := by
    rintro _ ⟨e, -, rfl⟩
    exact e.2
  have hbot := eq_bot_of_isPGroup_of_normalized r (fixedFieldImage_le_adjointGroup σ) hWC hWr
    hJx hw₀ hJn (J := fixedFieldImage τ σ) (fun j hj w hw => by
      obtain ⟨e, he, rfl⟩ := hw
      have hjX := fixedFieldImage_le_adjointGroup σ hj
      have := hEn ⟨j, hjX⟩ (Subgroup.mem_subgroupOf.2 hj) e he
      exact ⟨_, this, rfl⟩)
  exact (Subgroup.map_eq_bot_iff_of_injective _ (adjointGroup τ K).subtype_injective).1 hbot

theorem nonLocalized_fixedFieldImage_of_closing
    [Finite K] (σ : K ≃+* K) (r : ℕ) [Fact r.Prime]
    [CharP K r] (hsimple : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hclose : ∀ s : ℕ, s.Prime → s ≠ r → ∀ V : Subgroup ↥(adjointGroup τ K), V ≠ ⊥ →
      (∀ x ∈ V, ∀ y ∈ V, x * y = y * x) → (∀ v ∈ V, v ^ s = 1) →
      (∀ j ∈ (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K), ∀ v ∈ V, j * v * j⁻¹ ∈ V) →
      (∀ j ∈ (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K),
        (∀ v ∈ V, j * v * j⁻¹ = v) → j = 1) → False) :
    NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  set J : Subgroup ↥(adjointGroup τ K) :=
    (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) with hJ
  obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element τ
  have hJmem : ∀ x : ModGL τ K, x ∈ fixedFieldImage τ σ → ∀ hx : x ∈ adjointGroup τ K,
      (⟨x, hx⟩ : ↥(adjointGroup τ K)) ∈ J := fun x hx _ => Subgroup.mem_subgroupOf.2 hx
  have hJx : ∀ i : Fin τ.rank, xUnit τ K i 1 ∈ fixedFieldImage τ σ := fun i =>
    xUnit_mem_fixedFieldImage i (map_one σ)
  have hJn : canonicalRep (coxeterSystem τ) K w₀ ∈ fixedFieldImage τ σ :=
    canonicalRep_mem_fixedFieldImage w₀
  have hJsimple : IsSimpleGroup ↥J := by
    have := hsimple
    exact (subfieldEquiv (τ := τ) σ).symm.isSimpleGroup
  have hcent : ∀ x : ↥(adjointGroup τ K), (∀ j ∈ J, x * j = j * x) → x = 1 := by
    intro x hx
    refine Subtype.ext (eq_one_of_commute_simple_longest x.2 hw₀ (fun i => ?_) ?_)
    · have := hx ⟨xUnit τ K i 1, xUnit_mem_adjointGroup i 1⟩
        (hJmem _ (hJx i) _)
      exact congrArg Subtype.val this
    · have := hx ⟨canonicalRep (coxeterSystem τ) K w₀, canonicalRep_mem_adjointGroup _ K w₀⟩
        (hJmem _ hJn _)
      exact congrArg Subtype.val this
  exact nonLocalized_of_closing hJsimple hcent
    (fun E hEr hEn => eq_bot_of_isPGroup_of_normalized_subfield σ r E hEr hEn) hclose

theorem nonLocalized_fixedFieldImage_of_rep
    [Finite K] (σ : K ≃+* K) (r : ℕ) [Fact r.Prime]
    [CharP K r] (hsimple : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    {F W : Type*} [Field F] [IsAlgClosed F] [CharP F r] [AddCommGroup W] [Module F W]
    [FiniteDimensional F W] (ρ : ↥(adjointGroup τ K) →* Module.End F W)
    (hρ : Function.Injective ρ)
    (hnum : ¬ Nat.card (fixSubfield σ) ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ∣
      (Module.finrank F W).factorial) :
    NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) := by
  have : Finite (ModGL τ K) := finite_modGL
  have : Finite (adjointGroup τ K) := Subtype.finite
  refine nonLocalized_fixedFieldImage_of_closing σ r hsimple
    (closing_of_perm (Fact.out : r.Prime) ρ hρ (subfieldUnipotent τ σ) ?_ ?_)
  · exact fun x hx => Subgroup.mem_subgroupOf.2
      (map_posUnipotent_le_fixedFieldImage σ (Subgroup.mem_subgroupOf.1 hx))
  · rw [card_subfieldUnipotent]
    exact hnum

theorem nonLocalized_fixedFieldImage_of_perm
    [Finite K] (σ : K ≃+* K) (r : ℕ) [Fact r.Prime]
    [CharP K r] (hsimple : IsSimpleGroup ↥(adjointGroup τ (fixSubfield σ)))
    (hnum : ¬ Nat.card (fixSubfield σ) ^ {α : Fin τ.rank → ℤ | IsRoot τ α ∧ 0 < height α}.ncard ∣
      (τ.rank + τ.rootCount).factorial) :
    NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) := by
  classical
  let F := AlgebraicClosure K
  have hFr : CharP F r := charP_of_injective_algebraMap (algebraMap K F).injective r
  let ρ : ↥(adjointGroup τ K) →* Module.End F (Label τ → F) :=
    (adjRep τ K F).comp (adjointGroup τ K).subtype
  have hρ : Function.Injective ρ := (adjRep_injective τ K F).comp Subtype.val_injective
  refine nonLocalized_fixedFieldImage_of_rep σ r hsimple ρ hρ ?_
  rw [finrank_label_pi τ F, card_label_eq τ]
  exact hnum

end CFSG.SignalizerFunctorTheorem.NonLocalExc
