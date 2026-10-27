module

public import CFSG.Monster.CodeAut.BridgeData
public import CFSG.Monster.CodeAut.OrderBound

public section

namespace CFSG.Monster.Code

open CFSG.Sporadic.Mathieu (m24gA m24gB m24_eq card_M24 fam_m24_simplicity)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem bridgePA_basis : ∀ i, B i ∘ ⇑bridgePA ∈ C := by decide +kernel

private theorem bridgePA_basis' : ∀ i, B i ∘ ⇑bridgePA⁻¹ ∈ C := by decide +kernel

private theorem bridgePB_basis : ∀ i, B i ∘ ⇑bridgePB ∈ C := by decide +kernel

private theorem bridgePB_basis' : ∀ i, B i ∘ ⇑bridgePB⁻¹ ∈ C := by decide +kernel

theorem bridgePA_mem : bridgePA ∈ AutPerm := mem_AutPerm_of_basis bridgePA_basis bridgePA_basis'

theorem bridgePB_mem : bridgePB ∈ AutPerm := mem_AutPerm_of_basis bridgePB_basis bridgePB_basis'

theorem permWord_bridgePA_B : ∀ j : Fin 12,
    permWord bridgePA (B j) = coeffWord (bridgePACoeff.getD j 0) := by decide +kernel

theorem permWord_bridgePB_B : ∀ j : Fin 12,
    permWord bridgePB (B j) = coeffWord (bridgePBCoeff.getD j 0) := by decide +kernel

theorem bridgeDiffWord_eq : ∀ t : Fin 11,
    bridgeDiffWord t = coeffWord (bridgeDiffCoeff.getD t 0) := by decide +kernel

private def spanMask : List ℕ :=
  [1131, 1058, 2234, 1387, 3669, 3021, 2534, 2822, 3334, 1763, 1294, 3526]

private theorem B_eq_sum_diff : ∀ k : Fin 12, B k =
    ∑ t : Fin 11, (if (spanMask.getD k 0).testBit t then bridgeDiffWord t else 0) +
      (if (spanMask.getD k 0).testBit 11 then Ω else 0) := by decide +kernel

private theorem bridgeGen_mem (s : Fin 2) : bridgeGen s ∈ AutPerm := by
  fin_cases s
  · exact bridgePA_mem
  · exact bridgePB_mem

private theorem bridgeGen_mem_pair (s : Fin 2) :
    bridgeGen s ∈ ({bridgePA, bridgePB} : Set (Equiv.Perm (Fin 24))) := by
  fin_cases s
  · exact Set.mem_insert _ _
  · exact Set.mem_insert_of_mem _ rfl

@[expose] def bridgeDiffSet : Set (Fin 24 → ZMod 2) :=
  {x | ∃ p ∈ ({bridgePA, bridgePB} : Set (Equiv.Perm (Fin 24))), ∃ j : Fin 12,
    x = B j + permWord p (B j)}

theorem bridgeDiffSet_subset_C : bridgeDiffSet ⊆ C := by
  rintro _ ⟨p, hp, j, rfl⟩
  have hp' : p ∈ AutPerm := by
    rcases hp with rfl | rfl
    · exact bridgePA_mem
    · exact bridgePB_mem
  exact C.add_mem (B_mem_C j) (permWord_mem_of_mem_AutPerm hp' (B_mem_C j))

theorem span_bridgeDiffSet_sup :
    Submodule.span (ZMod 2) bridgeDiffSet ⊔ Submodule.span (ZMod 2) {Ω} = C := by
  apply le_antisymm
  · exact sup_le (Submodule.span_le.2 bridgeDiffSet_subset_C)
      (Submodule.span_le.2 (Set.singleton_subset_iff.2 Ω_mem_C))
  · rw [← span_B, Submodule.span_le, Set.range_subset_iff]
    intro k
    rw [B_eq_sum_diff k]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun t _ => ?_) ?_
    · split_ifs
      · exact Submodule.mem_sup_left (Submodule.subset_span
          ⟨_, bridgeGen_mem_pair (bridgeDiffGen t), bridgeDiffIdx t, rfl⟩)
      · exact Submodule.zero_mem _
    · split_ifs
      · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
      · exact Submodule.zero_mem _

@[expose] def ΩSpanC : Submodule (ZMod 2) C := Submodule.span (ZMod 2) {⟨Ω, Ω_mem_C⟩}

theorem span_mkQ_bridgeDiff :
    Submodule.span (ZMod 2) (ΩSpanC.mkQ '' {y : C | ∃ p ∈ ({bridgePA, bridgePB} :
      Set (Equiv.Perm (Fin 24))), ∃ j : Fin 12, (y : Fin 24 → ZMod 2) = B j + permWord p (B j)}) =
      ⊤ := by
  rw [← Submodule.map_span, Submodule.map_mkQ_eq_top]
  apply Submodule.map_injective_of_injective C.injective_subtype
  rw [Submodule.map_sup, ΩSpanC, Submodule.map_span, Submodule.map_span,
    Submodule.map_subtype_top, Set.image_singleton, sup_comm]
  have h1 : (⇑C.subtype '' {y : C | ∃ p ∈ ({bridgePA, bridgePB} : Set (Equiv.Perm (Fin 24))),
      ∃ j : Fin 12, (y : Fin 24 → ZMod 2) = B j + permWord p (B j)}) = bridgeDiffSet := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, bridgeDiffSet_subset_C hx⟩, hx, rfl⟩
  have h2 : ({C.subtype ⟨Ω, Ω_mem_C⟩} : Set (Fin 24 → ZMod 2)) = {Ω} := rfl
  rw [h1, h2]
  exact span_bridgeDiffSet_sup


theorem bridge_closure_eq_map :
    Subgroup.closure {bridgePA, bridgePB} =
      CFSG.Blueprint.NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom := by
  rw [m24_eq, MonoidHom.map_closure, Set.image_pair]
  have hA : (MulAut.conj bridgeQ⁻¹).toMonoidHom m24gA = bridgePA := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, bridgePA]
  have hB : (MulAut.conj bridgeQ⁻¹).toMonoidHom m24gB = bridgePB := by
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, bridgePB]
  rw [hA, hB]

theorem card_bridge_closure :
    Nat.card (Subgroup.closure {bridgePA, bridgePB}) = 244823040 := by
  rw [bridge_closure_eq_map, Subgroup.card_map_of_injective (MulAut.conj bridgeQ⁻¹).injective,
    card_M24]

theorem AutPerm_eq_closure :
    AutPerm = Subgroup.closure {bridgePA, bridgePB} := by
  have hle : Subgroup.closure {bridgePA, bridgePB} ≤ AutPerm := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact bridgePA_mem
    · exact bridgePB_mem
  exact (Subgroup.eq_of_le_of_card_ge hle
    (by rw [card_bridge_closure]; exact card_AutPerm_le)).symm

theorem card_AutPerm : Nat.card AutPerm = 244823040 := by
  rw [AutPerm_eq_closure, card_bridge_closure]

theorem mem_AutPerm_iff_conj (p : Equiv.Perm (Fin 24)) :
    p ∈ AutPerm ↔
      ∃ g ∈ CFSG.Blueprint.NativeSporadic.M24, ∀ i, p i = bridgeQ⁻¹ (g (bridgeQ i)) := by
  rw [AutPerm_eq_closure, bridge_closure_eq_map, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g, hg, fun i => ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply]
  · rintro ⟨g, hg, h⟩
    refine ⟨g, hg, Equiv.ext fun i => ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv, Equiv.Perm.mul_apply,
      Equiv.Perm.mul_apply, h i]

theorem AutPerm_isSimpleGroup : IsSimpleGroup AutPerm := by
  have hM : IsSimpleGroup CFSG.Blueprint.NativeSporadic.M24 := fam_m24_simplicity.2.2
  let e1 : CFSG.Blueprint.NativeSporadic.M24 ≃*
      CFSG.Blueprint.NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom :=
    CFSG.Blueprint.NativeSporadic.M24.equivMapOfInjective _ (MulAut.conj bridgeQ⁻¹).injective
  let e2 : AutPerm ≃* CFSG.Blueprint.NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom :=
    MulEquiv.subgroupCongr (AutPerm_eq_closure.trans bridge_closure_eq_map)
  exact (e2.trans e1.symm).isSimpleGroup

theorem mog_catalog_M24_bridge :
    AutPerm = Subgroup.closure {bridgePA, bridgePB} ∧
    Subgroup.closure {bridgePA, bridgePB} =
      CFSG.Blueprint.NativeSporadic.M24.map (MulAut.conj bridgeQ⁻¹).toMonoidHom ∧
    (∀ p : Equiv.Perm (Fin 24), p ∈ AutPerm ↔
      ∃ g ∈ CFSG.Blueprint.NativeSporadic.M24, ∀ i, p i = bridgeQ⁻¹ (g (bridgeQ i))) ∧
    (Nontrivial AutPerm ∧ IsSimpleGroup AutPerm ∧ Nat.card AutPerm = 244823040) ∧
    Submodule.span (ZMod 2) (ΩSpanC.mkQ '' {y : C | ∃ p ∈ ({bridgePA, bridgePB} :
      Set (Equiv.Perm (Fin 24))), ∃ j : Fin 12, (y : Fin 24 → ZMod 2) = B j + permWord p (B j)}) =
      ⊤ :=
  ⟨AutPerm_eq_closure, bridge_closure_eq_map, mem_AutPerm_iff_conj,
    ⟨AutPerm_isSimpleGroup.toNontrivial, AutPerm_isSimpleGroup, card_AutPerm⟩,
    span_mkQ_bridgeDiff⟩

end CFSG.Monster.Code
