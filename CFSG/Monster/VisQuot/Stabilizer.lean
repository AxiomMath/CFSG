module

public import CFSG.Monster.VisQuot.Monomial
public import CFSG.Monster.CodeAut.Bridge

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.VisQuot

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Lifts CFSG.Monster.Visible CFSG.Monster.VisCert

private theorem pA_eq : pA = bridgePA :=
  Equiv.ext fun i => Fin.ext ((pA_image i).trans (bridgePA_image i).symm)

private theorem pB_eq : pB = bridgePB :=
  Equiv.ext fun i => Fin.ext ((pB_image i).trans (bridgePB_image i).symm)

theorem closure_pAAut_pBAut :
    Subgroup.closure {pAAut, pBAut} = (⊤ : Subgroup AutPerm) := by
  apply Subgroup.map_injective AutPerm.subtype_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  show Subgroup.closure {pA, pB} = AutPerm
  rw [pA_eq, pB_eq]
  exact AutPerm_eq_closure.symm

theorem kGen_one_mem_Nvis : kGen 1 ∈ Nvis :=
  Subgroup.subset_closure ⟨1, (by decide : 1 ≤ ((1 : Fin 15) : ℕ)), rfl⟩

theorem kGen_two_mem_Nvis : kGen 2 ∈ Nvis :=
  Subgroup.subset_closure ⟨2, (by decide : 1 ≤ ((2 : Fin 15) : ℕ)), rfl⟩

theorem permHom_mem_Nvis (p : AutPerm) : permHom p ∈ Nvis := by
  have h : permHom.range ≤ Nvis := by
    rw [MonoidHom.range_eq_map, ← closure_pAAut_pBAut, MonoidHom.map_closure, Set.image_pair,
      Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · rw [← kGen_one]
      exact kGen_one_mem_Nvis
    · rw [← kGen_two]
      exact kGen_two_mem_Nvis
  exact h ⟨p, rfl⟩

theorem Nvis_eq_range_monoHom : Nvis = monoHom.range := by
  refine le_antisymm ((Subgroup.closure_le _).2 ?_) ?_
  · rintro _ ⟨j, hj, rfl⟩
    have hj' : 1 ≤ (j : ℕ) := hj
    rcases (show (j : ℕ) = 1 ∨ (j : ℕ) = 2 ∨ 3 ≤ (j : ℕ) by omega) with h | h | h
    · rw [show j = 1 from Fin.ext h, kGen_one]
      exact permHom_mem_range_monoHom _
    · rw [show j = 2 from Fin.ext h, kGen_two]
      exact permHom_mem_range_monoHom _
    · rw [kGen_of_three_le h]
      exact Esign_le_range_monoHom (mem_Esign.2 ⟨_, rfl⟩)
  · rintro _ ⟨x, rfl⟩
    rw [monoHom_apply]
    refine Nvis.mul_mem (Evis_le_Nvis ?_) (permHom_mem_Nvis _)
    rw [Evis_eq_Esign, ← range_signQ]
    exact ⟨x.left, rfl⟩

theorem Hvis_stab_iff :
    ∀ u ∈ Hvis, u • twoΩCls = twoΩCls ↔ u ∈ Nvis := by
  intro u hu
  obtain ⟨g, -, rfl⟩ := mem_Hvis.1 hu
  rw [Nvis_eq_range_monoHom, ← modTwoEnd_twoΩCls_eq_iff]
  rfl

theorem Nvis_le_stabilizer :
    Nvis ≤ MulAction.stabilizer GLV twoΩCls := fun u hu =>
  (Hvis_stab_iff u (Nvis_le_Hvis hu)).2 hu

theorem Hvis_inf_stabilizer :
    Hvis ⊓ MulAction.stabilizer GLV twoΩCls = Nvis :=
  le_antisymm (fun u hu => (Hvis_stab_iff u hu.1).1 hu.2) fun _ hu =>
    ⟨Nvis_le_Hvis hu, Nvis_le_stabilizer hu⟩

def NvisEquiv : MonoSD ≃* Nvis :=
  (MonoidHom.ofInjective monoHom_injective).trans
    (MulEquiv.subgroupCongr Nvis_eq_range_monoHom.symm)

instance normal_Evis_subgroupOf_Nvis :
    (Evis.subgroupOf Nvis).Normal := by
  rw [Nvis_eq_range_monoHom, Evis_eq_Esign]
  infer_instance

def NvisToAutPerm : Nvis →* AutPerm :=
  rangeMonoToAutPerm.comp (MulEquiv.subgroupCongr Nvis_eq_range_monoHom).toMonoidHom

theorem NvisToAutPerm_surjective :
    Function.Surjective NvisToAutPerm :=
  rangeMonoToAutPerm_surjective.comp (MulEquiv.surjective _)

theorem ker_NvisToAutPerm :
    NvisToAutPerm.ker = Evis.subgroupOf Nvis := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Evis_eq_Esign]
  show rangeMonoToAutPerm (MulEquiv.subgroupCongr Nvis_eq_range_monoHom x) = 1 ↔ _
  rw [← MonoidHom.mem_ker, ker_rangeMonoToAutPerm, Subgroup.mem_subgroupOf]
  rfl

def NvisQuotEquiv : Nvis ⧸ Evis.subgroupOf Nvis ≃* AutPerm :=
  (QuotientGroup.quotientMulEquivOfEq ker_NvisToAutPerm.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ NvisToAutPerm_surjective)

theorem natCard_Evis : Nat.card Evis = 2 ^ 11 := by
  rw [Evis_eq_Esign, natCard_Esign]

theorem natCard_Nvis : Nat.card Nvis = 2 ^ 11 * 244823040 := by
  rw [Nvis_eq_range_monoHom, natCard_range_monoHom, card_AutPerm]

theorem Evis_comm {x y : GLV} (hx : x ∈ Evis) (hy : y ∈ Evis) : x * y = y * x := by
  rw [Evis_eq_Esign] at hx hy
  exact mul_comm_of_mem_Esign hx hy

theorem coordinate_frame_stabilizer :
    (∀ u ∈ Hvis, u • twoΩCls = twoΩCls ↔ u ∈ Nvis) ∧ Nvis ≤ Hvis ∧
    Hvis ⊓ MulAction.stabilizer GLV twoΩCls = Nvis ∧
    (∀ g : latticeO, modTwoEnd g twoΩCls = twoΩCls ↔ ∃ (a : C) (p : AutPerm), g = gO a * PO p) ∧
    (∀ x : OLq, x ∈ stabQ ↔ ∃ (a : C) (p : AutPerm), x = QuotientGroup.mk (gO a * PO p)) ∧
    (∀ (a b : C) (p q : AutPerm),
      (QuotientGroup.mk (gO a * PO p) : OLq) = QuotientGroup.mk (gO b * PO q) ↔
        p = q ∧ (a = b ∨ a = ΩC + b)) ∧
    gO ΩC = negOneO ∧
    Nonempty (stabQ ≃* MonoSD) ∧ Nonempty (Nvis ≃* MonoSD) ∧
    Nvis = monoHom.range ∧ Function.Injective monoHom ∧
    (∀ (a : C) (p : AutPerm),
      monoHom ⟨Multiplicative.ofAdd (Submodule.Quotient.mk a), p⟩ = modTwoUnit (PO p * gO a)) ∧
    pA = bridgePA ∧ pB = bridgePB ∧ Subgroup.closure {pAAut, pBAut} = (⊤ : Subgroup AutPerm) ∧
    Evis = Esign ∧
    (∀ x ∈ Evis, ∀ y ∈ Evis, x * y = y * x) ∧ Evis ≤ Nvis ∧ (Evis.subgroupOf Nvis).Normal ∧
    Nat.card Evis = 2 ^ 11 ∧
    Nonempty (Nvis ⧸ Evis.subgroupOf Nvis ≃* AutPerm) ∧
    Nat.card Nvis = 2 ^ 11 * 244823040 :=
  ⟨Hvis_stab_iff, Nvis_le_Hvis, Hvis_inf_stabilizer,
    fun g => by rw [twoΩCls_eq_frameClass]; exact modTwoEnd_frameClass_eq_iff g,
    fun _ => mem_stabQ_iff, mk_gO_mul_PO_eq_iff, gO_ΩC, ⟨stabQEquiv.symm⟩, ⟨NvisEquiv.symm⟩,
    Nvis_eq_range_monoHom, monoHom_injective, monoHom_mk, pA_eq, pB_eq, closure_pAAut_pBAut,
    Evis_eq_Esign, fun _ hx _ hy => Evis_comm hx hy, Evis_le_Nvis, inferInstance, natCard_Evis,
    ⟨NvisQuotEquiv⟩, natCard_Nvis⟩

end CFSG.Monster.VisQuot
