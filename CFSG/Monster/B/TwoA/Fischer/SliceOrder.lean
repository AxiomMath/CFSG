module

public import CFSG.Monster.B.TwoA.Fischer.CliqueKernel
public import CFSG.Monster.B.TwoA.Fischer.SliceOrderPSU

public noncomputable section

namespace CFSG.Monster.B.TwoA.Fischer

open CFSG.Monster.B.Classical.UnitarySix

variable {S V : Type*} [Group S] {act : S →* Equiv.Perm V} {lab : V → S} {Y : Set V}

theorem sliceStab_le_sliceGroup (u : V) : sliceStab act lab Y u ≤ sliceGroup lab Y :=
  inf_le_left

namespace IsFischerSlice

abbrev mulAction (hS : IsFischerSlice act lab Y) : MulAction (sliceGroup lab Y) Y :=
  MulAction.compHom Y (slicePerm act lab Y hS.mapsTo)

variable (hS : IsFischerSlice act lab Y)
include hS

theorem coe_smul (a : sliceGroup lab Y) (y : Y) :
    letI := hS.mulAction; ((a • y : Y) : V) = act (a : S) y := rfl

theorem slicePerm_injective : Function.Injective (slicePerm act lab Y hS.mapsTo) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  refine Subtype.ext (hS.faithful a a.2 fun y hy => ?_)
  have := congrArg (fun σ : Equiv.Perm Y => (σ ⟨y, hy⟩ : V)) ha
  simpa [slicePerm_apply] using this

theorem act_lab_self {u : V} (hu : u ∈ Y) : act (lab u) u = u :=
  (hS.act_lab_eq_iff hu hu).2 (Commute.refl _)

theorem act_eq_self_iff_commute {u : V} (hu : u ∈ Y) {a : S} (ha : a ∈ sliceGroup lab Y) :
    act a u = u ↔ Commute a (lab u) := by
  constructor
  · intro h
    have h1 := hS.lab_act a u
    rw [h] at h1
    rw [Commute, SemiconjBy]
    calc a * lab u = a * lab u * a⁻¹ * a := by group
      _ = lab u * a := by rw [← h1]
  · intro h
    refine hS.injOn (hS.mapsTo a ha u hu) hu ?_
    rw [hS.lab_act, h.eq, mul_inv_cancel_right]

theorem sliceStab_eq_inf_centralizer {u : V} (hu : u ∈ Y) :
    sliceStab act lab Y u = sliceGroup lab Y ⊓ Subgroup.centralizer {lab u} := by
  ext a
  rw [mem_sliceStab, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨ha, h⟩
    exact ⟨ha, ((hS.act_eq_self_iff_commute hu ha).1 h).eq⟩
  · rintro ⟨ha, h⟩
    exact ⟨ha, (hS.act_eq_self_iff_commute hu ha).2 h⟩

theorem zpowers_lab_le_sliceStab {u : V} (hu : u ∈ Y) :
    Subgroup.zpowers (lab u) ≤ sliceStab act lab Y u :=
  Subgroup.zpowers_le.2 (hS.lab_mem_sliceStab_self hu)

theorem card_zpowers_lab {u : V} (hu : u ∈ Y) : Nat.card (Subgroup.zpowers (lab u)) = 2 := by
  rw [Nat.card_zpowers, hS.orderOf_lab u hu]

theorem fix_neighborSet_iff {u : V} (hu : u ∈ Y) {a : S} (ha : a ∈ sliceStab act lab Y u) :
    (∀ z ∈ (sliceGraph lab Y).neighborSet u, act a z = z) ↔ a ∈ Subgroup.zpowers (lab u) := by
  obtain ⟨L⟩ := hS.nonempty_localChart hu
  constructor
  · intro h
    rw [← L.ker ⟨a, ha⟩]
    apply projAct_injective
    rw [map_one]
    ext p
    obtain ⟨z, rfl⟩ := L.τ.surjective p
    rw [Equiv.Perm.one_apply, ← L.equivariant ⟨a, ha⟩ z z (h z z.2).symm]
  · intro h z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 h
    have h1 : act (lab u) z = z :=
      (hS.act_lab_eq_iff hu (mem_of_mem_neighborSet hz)).2 hz.2.2.2
    rw [map_zpow]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self h1 k

theorem card_sliceStab_eq_two_mul {u : V} (hu : u ∈ Y) :
    Nat.card (sliceStab act lab Y u) = 2 * Nat.card ProjSU := by
  obtain ⟨L⟩ := hS.nonempty_localChart hu
  have hker : L.φ.ker = (Subgroup.zpowers (lab u)).subgroupOf (sliceStab act lab Y u) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, L.ker]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup L.φ.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective L.φ L.surj).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hS.zpowers_lab_le_sliceStab hu)).toEquiv,
    hS.card_zpowers_lab hu] at h1
  rw [h1, mul_comm]

theorem card_sliceStab {u : V} (hu : u ∈ Y) :
    Nat.card (sliceStab act lab Y u) = 18393661440 := by
  rw [hS.card_sliceStab_eq_two_mul hu, card_projSU]

theorem stabilizer_eq_subgroupOf {u : V} (hu : u ∈ Y) :
    letI := hS.mulAction
    MulAction.stabilizer (sliceGroup lab Y) (⟨u, hu⟩ : Y) =
      (sliceStab act lab Y u).subgroupOf (sliceGroup lab Y) := by
  let _ := hS.mulAction
  ext a
  rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, mem_sliceStab]
  constructor
  · intro h
    exact ⟨a.2, congrArg Subtype.val h⟩
  · intro h
    exact Subtype.ext h.2

theorem isPretransitive :
    letI := hS.mulAction
    MulAction.IsPretransitive (sliceGroup lab Y) Y := by
  let _ := hS.mulAction
  refine ⟨fun y z => ?_⟩
  obtain ⟨a, ha, hay⟩ := hS.transitive y y.2 z z.2
  exact ⟨⟨a, ha⟩, Subtype.ext hay⟩

theorem card_sliceGroup_eq_mul {u : V} (hu : u ∈ Y) :
    Nat.card (sliceGroup lab Y) = Y.ncard * Nat.card (sliceStab act lab Y u) := by
  let _ := hS.mulAction
  have := hS.isPretransitive
  rw [← Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (sliceGroup lab Y)
    (⟨u, hu⟩ : Y)), Nat.card_prod, MulAction.orbit_eq_univ, Nat.card_congr (Equiv.Set.univ Y),
    Nat.card_coe_set_eq, hS.stabilizer_eq_subgroupOf hu,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (sliceStab_le_sliceGroup (act := act) (lab := lab) (Y := Y) u)).toEquiv]

theorem card_sliceGroup : Nat.card (sliceGroup lab Y) = 64561751654400 := by
  obtain ⟨u, hu⟩ : Y.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hS.ncard]; norm_num)
  rw [hS.card_sliceGroup_eq_mul hu, hS.ncard, hS.card_sliceStab hu]

theorem exact_order {u : V} (hu : u ∈ Y) :
    sliceStab act lab Y u = sliceGroup lab Y ⊓ Subgroup.centralizer {lab u} ∧
    Subgroup.zpowers (lab u) ≤ sliceStab act lab Y u ∧
    (∀ a ∈ sliceStab act lab Y u,
      (∀ z ∈ (sliceGraph lab Y).neighborSet u, act a z = z) ↔ a ∈ Subgroup.zpowers (lab u)) ∧
    Nat.card ProjSU = 9196830720 ∧
    Nat.card (sliceStab act lab Y u) = 2 * Nat.card ProjSU ∧
    Nat.card (sliceStab act lab Y u) = 18393661440 ∧
    Nat.card (sliceGroup lab Y) = Y.ncard * Nat.card (sliceStab act lab Y u) ∧
    Nat.card (sliceGroup lab Y) = 64561751654400 ∧
    64561751654400 = 2 ^ 17 * 3 ^ 9 * 5 ^ 2 * 7 * 11 * 13 :=
  ⟨hS.sliceStab_eq_inf_centralizer hu, hS.zpowers_lab_le_sliceStab hu,
    fun _ ha => hS.fix_neighborSet_iff hu ha, card_projSU, hS.card_sliceStab_eq_two_mul hu,
    hS.card_sliceStab hu, hS.card_sliceGroup_eq_mul hu, hS.card_sliceGroup, by norm_num⟩

end IsFischerSlice

end CFSG.Monster.B.TwoA.Fischer
