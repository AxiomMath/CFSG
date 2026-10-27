module

public import CFSG.Sporadic.ONOddCore.LocalAutData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierTwoCentralizersStabilizer

public noncomputable section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.ComponentClassification.CatalogueSchreierTwoCentralizers

theorem RM_eq_map :
    RM = rhoM.range.map conjU := by
  rw [RM, piM, MonoidHom.range_comp]

theorem card_RM :
    Nat.card RM = 40320 := by
  rw [RM_eq_map, Subgroup.card_map_of_injective (MulAut.conj onu).injective, card_rhoM_range]

theorem rhoL_range_le :
    rhoL.range ≤ rhoM.range := by
  rintro _ ⟨y, rfl⟩
  exact ⟨_, rfl⟩

theorem onX_le_RM :
    onX ≤ RM := by
  rw [← rhoL_conj, RM_eq_map]
  exact Subgroup.map_mono rhoL_range_le

theorem map_commutator_top_M :
    (⁅(⊤ : Subgroup onM), ⊤⁆ : Subgroup onM).map onM.subtype = ⁅onM, onM⁆ := by
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

theorem map_L_subtype :
    (onL.subgroupOf onM).map onM.subtype = onL := by
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 onL_le_M]

theorem commutator_M_eq_L :
    ⁅onM, onM⁆ = onL := at_on_perfect_derived_subgroup.1.symm

theorem commutator_top_M :
    (⁅(⊤ : Subgroup onM), ⊤⁆ : Subgroup onM) = onL.subgroupOf onM := by
  apply Subgroup.map_injective onM.subtype_injective
  rw [map_commutator_top_M, map_L_subtype, commutator_M_eq_L]

theorem rhoL_apply
    (l : onL) : rhoL l = rhoM ⟨l, onL_le_M l.2⟩ := by
  rw [rhoL, MonoidHom.comp_apply]
  rfl

theorem mem_LM
    (l : onL) : (⟨l, onL_le_M l.2⟩ : onM) ∈ onL.subgroupOf onM :=
  Subgroup.mem_subgroupOf.2 l.2

theorem map_L_rhoM_le :
    (onL.subgroupOf onM).map rhoM ≤ rhoL.range := by
  rintro _ ⟨m, hm, rfl⟩
  have e : rhoM m = rhoL ⟨m, Subgroup.mem_subgroupOf.1 hm⟩ := by rw [rhoL_apply]
  rw [e]
  exact ⟨_, rfl⟩

theorem rhoL_range_le_map :
    rhoL.range ≤ (onL.subgroupOf onM).map rhoM := by
  rintro _ ⟨l, rfl⟩
  rw [rhoL_apply]
  exact Subgroup.mem_map_of_mem rhoM (mem_LM l)

theorem map_L_rhoM :
    (onL.subgroupOf onM).map rhoM = rhoL.range :=
  le_antisymm map_L_rhoM_le rhoL_range_le_map

theorem map_L_piM :
    (onL.subgroupOf onM).map piM = onX := by
  rw [show piM = conjU.comp rhoM from rfl, ← Subgroup.map_map, map_L_rhoM, rhoL_conj]

theorem commutator_RM :
    ⁅RM, RM⁆ = onX := by
  rw [RM, MonoidHom.range_eq_map, ← Subgroup.map_commutator, commutator_top_M, map_L_piM]

theorem RM_inf_centralizer :

    RM ⊓ Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) = ⊥ := by
  rw [onX_centralizer, inf_bot_eq]

theorem conj_mem_X
    {r x : Equiv.Perm (Fin 120)} (hr : r ∈ RM) (hx : x ∈ onX) :
    r * x * r⁻¹ ∈ onX := by
  have h1 : r * x * r⁻¹ * x⁻¹ ∈ onX := by
    rw [← commutator_RM]
    exact Subgroup.commutator_mem_commutator hr (onX_le_RM hx)
  have := mul_mem h1 hx
  rwa [inv_mul_cancel_right] at this

abbrev XR :
    Subgroup RM := onX.subgroupOf RM

instance XR_normal :
    XR.Normal :=
  ⟨fun x hx r => by
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact conj_mem_X r.2 hx⟩

@[expose] def XREquiv :
    XR ≃* onX := Subgroup.subgroupOfEquivOfLe onX_le_RM

@[expose] def iotaR :
    RM →* MulAut onX :=
  (MulAut.congr XREquiv).toMonoidHom.comp MulAut.conjNormal

theorem iotaR_apply
    (r : RM) (x : onX) :
    ((iotaR r x : onX) : Equiv.Perm (Fin 120)) = r * x * (r : Equiv.Perm (Fin 120))⁻¹ := rfl

theorem mem_centralizer_of_iotaR
    {r : RM} (hr : iotaR r = 1) :
    (r : Equiv.Perm (Fin 120)) ∈ Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h := congrArg (fun α : MulAut onX => ((α ⟨x, hx⟩ : onX) : Equiv.Perm (Fin 120))) hr
  simp only [iotaR_apply, MulAut.one_apply] at h
  calc x * r = r * x * (r : Equiv.Perm (Fin 120))⁻¹ * r := by rw [h]
    _ = r * x := by group

theorem iotaR_injective :
    Function.Injective iotaR := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  have h : (r : Equiv.Perm (Fin 120)) ∈ RM ⊓ Subgroup.centralizer (onX : Set _) :=
    ⟨r.2, mem_centralizer_of_iotaR hr⟩
  rw [RM_inf_centralizer, Subgroup.mem_bot] at h
  exact Subgroup.mem_bot.2 (Subtype.ext h)

theorem XR_eq_commutator :
    XR = ⁅(⊤ : Subgroup RM), ⊤⁆ := by
  apply Subgroup.map_injective RM.subtype_injective
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.2 onX_le_RM, commutator_RM]

instance XR_characteristic :
    XR.Characteristic := by
  rw [XR_eq_commutator]
  infer_instance

theorem mem_stabilizer_XR
    (α : MulAut RM) : α ∈ stabilizer XR :=
  (mem_stabilizer_iff_map XR α).2 (Subgroup.characteristic_iff_map_eq.1 XR_characteristic α)

@[expose] def resX :
    MulAut RM →* MulAut onX :=
  (MulAut.congr XREquiv).toMonoidHom.comp
    ((restrict XR).comp ((MonoidHom.id (MulAut RM)).codRestrict _ mem_stabilizer_XR))

theorem resX_apply
    (α : MulAut RM) (x : onX) :
    ((resX α x : onX) : Equiv.Perm (Fin 120)) =
      ((α ⟨x, onX_le_RM x.2⟩ : RM) : Equiv.Perm (Fin 120)) := rfl

theorem resX_injective :
    Function.Injective resX := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro α hα
  have hfix : ∀ x : onX, ((α ⟨x, onX_le_RM x.2⟩ : RM) : Equiv.Perm (Fin 120)) = x := fun x => by
    have h := congrArg (fun β : MulAut onX => ((β x : onX) : Equiv.Perm (Fin 120))) hα
    simpa only [resX_apply, MulAut.one_apply] using h
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun r => Subtype.ext ?_
  set s := (r : Equiv.Perm (Fin 120))⁻¹ * ((α r : RM) : Equiv.Perm (Fin 120)) with hs
  have hsR : s ∈ RM := mul_mem (inv_mem r.2) (α r).2
  have hsC : s ∈ Subgroup.centralizer (onX : Set (Equiv.Perm (Fin 120))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hrx : (r : Equiv.Perm (Fin 120)) * x * (r : Equiv.Perm (Fin 120))⁻¹ ∈ onX :=
      conj_mem_X r.2 hx
    have h1 := hfix ⟨_, hrx⟩
    have h2 : α (⟨(r : Equiv.Perm (Fin 120)) * x * (r : Equiv.Perm (Fin 120))⁻¹,
        onX_le_RM hrx⟩ : RM) = α r * α ⟨x, onX_le_RM hx⟩ * (α r)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul]
      rfl
    have h3 := hfix ⟨x, hx⟩
    rw [h2] at h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1
    rw [h3] at h1
    rw [hs]
    calc x * ((r : Equiv.Perm (Fin 120))⁻¹ * ((α r : RM) : Equiv.Perm (Fin 120))) =
        (r : Equiv.Perm (Fin 120))⁻¹ * (((α r : RM) : Equiv.Perm (Fin 120)) * x *
          ((α r : RM) : Equiv.Perm (Fin 120))⁻¹) * ((α r : RM) : Equiv.Perm (Fin 120)) := by
          rw [h1]; group
      _ = (r : Equiv.Perm (Fin 120))⁻¹ * ((α r : RM) : Equiv.Perm (Fin 120)) * x := by group
  have hs1 : s ∈ RM ⊓ Subgroup.centralizer (onX : Set _) := ⟨hsR, hsC⟩
  rw [RM_inf_centralizer, Subgroup.mem_bot, hs, inv_mul_eq_one] at hs1
  exact hs1.symm

end CFSG.Sporadic.ONOddCore
